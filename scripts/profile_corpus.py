"""Profile the regression corpus for the site's profiling page.

Runs every fixture under every domain x context policy with the native CLI, the
Interval runs again with the WebAssembly bundle under Node, and a recursion-depth
sweep under entry-state contexts. Writes one snapshot to
pages/data/profiling/<date>-<commit>.json, records the device and toolchain it was
measured on, and lists the snapshot first in pages/data/profiling/index.json.

Timings depend on the machine and on what else runs on it: close other work and
keep --jobs low for numbers worth comparing across snapshots.
"""

import argparse
import bisect
import gzip
import json
import math
import os
import platform
import re
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
from vimp_fixture import param_args  # noqa: E402

CLI = REPO / "cli/voblint"
BUNDLE = REPO / "build/browser/voblint_web.bc.wasm.js"
HARNESS = REPO / "tests/voblint_web_calls.cjs"
CORPUS = REPO / "tests/regression"
OUT_DIR = REPO / "pages/data/profiling"

DOMAINS = ["sign", "parity", "congruence", "interval", "int"]
CONTEXTS = {"none": [], "entry-state": [], "call-string-1": ["--context-depth", "1"]}
DEPTHS = [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 1500, 2000]
# A Chrome worker recurses about as deep as Node at this stack size (KiB).
WASM_STACK_KIB = 512
# voblint_main.ml: 1 configuration rejected, 2 parse error, 3 timeout, 4 ill-formed.
EXIT_STATUS = {1: "rejected", 2: "invalid", 3: "timeout", 4: "invalid"}
VERDICT = re.compile(r"\s(PROVED|REFUTED|UNKNOWN|DEAD)\s")


def out(cmd):
    try:
        return subprocess.run(
            cmd, capture_output=True, text=True, check=False
        ).stdout.strip()
    except OSError:
        return ""


def device():
    """The machine and toolchain a snapshot was measured on, without identifying the user."""
    system = platform.system()
    info = {
        "os": platform.platform(terse=True),
        "arch": platform.machine(),
        "logical_cpus": os.cpu_count(),
        "python": platform.python_version(),
        "node": out(["node", "--version"]),
        "ocaml": out(["opam", "exec", "--", "ocamlfind", "ocamlopt", "-version"]),
        "wasm_of_ocaml": out(["opam", "exec", "--", "wasm_of_ocaml", "--version"]),
    }
    if system == "Darwin":
        info["cpu"] = out(["sysctl", "-n", "machdep.cpu.brand_string"])
        info["model"] = out(["sysctl", "-n", "hw.model"])
        mem = out(["sysctl", "-n", "hw.memsize"])
        info["memory_gib"] = round(int(mem) / 2**30) if mem.isdigit() else None
        info["performance_cpus"] = (
            int(out(["sysctl", "-n", "hw.perflevel0.logicalcpu"]) or 0) or None
        )
        info["on_battery"] = "Battery Power" in out(["pmset", "-g", "batt"])
    elif system == "Linux":
        cpuinfo = Path("/proc/cpuinfo").read_text(errors="replace")
        model = re.search(r"model name\s*:\s*(.+)", cpuinfo)
        info["cpu"] = model.group(1).strip() if model else platform.processor()
        meminfo = re.search(r"MemTotal:\s*(\d+) kB", Path("/proc/meminfo").read_text())
        info["memory_gib"] = round(int(meminfo.group(1)) / 2**20) if meminfo else None
        info["virtualized"] = "hypervisor" in cpuinfo
    else:
        info["cpu"] = platform.processor()
    return info


def time_cmd():
    """BSD and GNU time print peak RSS differently; None where neither is present."""
    if platform.system() == "Darwin":
        return (
            ["/usr/bin/time", "-l"],
            re.compile(r"(\d+)\s+maximum resident set size"),
            1,
        )
    if Path("/usr/bin/time").exists():
        return (
            ["/usr/bin/time", "-v"],
            re.compile(r"Maximum resident set size \(kbytes\): (\d+)"),
            1024,
        )
    return [], None, 1


TIME_PREFIX, RSS_RE, RSS_UNIT = time_cmd()


def timed(cmd, timeout):
    start = time.perf_counter()
    p = subprocess.run(
        [*TIME_PREFIX, *cmd], capture_output=True, text=True, timeout=timeout
    )
    wall = time.perf_counter() - start
    m = RSS_RE.search(p.stderr) if RSS_RE else None
    return p, wall * 1000, int(m.group(1)) * RSS_UNIT if m else None


def cli_args(domain, context, timeout):
    policy = "call-string" if context.startswith("call-string") else context
    return [
        str(CLI),
        "--analysis",
        domain,
        "--context",
        policy,
        *CONTEXTS[context],
        "--timeout",
        str(timeout),
    ]


TIMING = re.compile(r"voblint-timing: analysis_ms=([0-9.]+)")


def analysis_ms(stderr):
    """The CLI's own measurement of the solve (--timing), without start-up or printing."""
    m = TIMING.search(stderr)
    return float(m.group(1)) if m else None


# Tracing slows a run down, and the counts need no timing, so a traced run may take longer.
TRACE_TIME_FACTOR = 4


def solver_work(path, domain, context, timeout):
    """Counts from a traced run's JSON Lines events, which the CLI writes to stderr.

    A traced run that does not finish leaves a cut-off trace, so its counts are unknown
    rather than whatever part of the trace was written."""
    unknown = {"evals": None, "unknowns": None, "contexts": None}
    limit = timeout * TRACE_TIME_FACTOR
    try:
        p = subprocess.run(
            [
                *cli_args(domain, context, limit),
                "--trace",
                "--compact",
                "--format",
                "jsonl",
                str(path),
            ],
            capture_output=True,
            text=True,
            timeout=limit + 10,
        )
    except subprocess.TimeoutExpired:
        return unknown
    if p.returncode != 0:
        return unknown
    evals = 0
    unknowns, contexts = set(), set()
    for line in p.stderr.splitlines():
        if not line.startswith("{"):
            continue
        e = json.loads(line)
        if e.get("event") == "eq":
            evals += 1
        if e.get("event") == "solve" and e.get("unknown"):
            unknowns.add(json.dumps(e["unknown"], sort_keys=True))
            contexts.add(json.dumps(e["unknown"].get("context"), sort_keys=True))
    return {"evals": evals, "unknowns": len(unknowns), "contexts": len(contexts)}


def timed_reps(path, domain, context, reps, timeout):
    """Median wall and solve time and peak RSS over [reps] runs, or the failing exit status."""
    walls, solves, rss, text = [], [], 0, ""
    for _ in range(reps):
        p, wall, peak = timed(
            [*cli_args(domain, context, timeout), "--timing", str(path)], timeout + 10
        )
        if p.returncode != 0:
            return {"status": EXIT_STATUS.get(p.returncode, f"exit {p.returncode}")}
        walls.append(wall)
        solves.append(analysis_ms(p.stderr))
        rss = max(rss, peak or 0)
        text = p.stdout
    return {
        "status": "ok",
        "wall_ms": statistics.median(walls),
        "ms": statistics.median(solves) if None not in solves else None,
        "rss": rss or None,
        "stdout": text,
    }


def native(job, reps, timeout):
    path, domain, context = job
    row = {
        "fixture": str(path.relative_to(CORPUS)),
        "domain": domain,
        "context": context,
    }
    try:
        result = timed_reps(path, domain, context, reps, timeout)
        if result["status"] != "ok":
            row["status"] = result["status"]
            return row
        found = VERDICT.findall(result.pop("stdout"))
        row.update(
            status="ok",
            ms=result["ms"],
            wall_ms=result["wall_ms"],
            rss=result["rss"],
            verdicts={
                k: found.count(k) for k in ("PROVED", "REFUTED", "UNKNOWN", "DEAD")
            },
        )
        row.update(solver_work(path, domain, context, timeout))
    except subprocess.TimeoutExpired:
        row["status"] = "timeout"
    return row


def wasm_reps(paths, domain, context, reps, timeout):
    """Median over [reps] runs of each fixture's in-process time in the browser bundle."""
    runs = [wasm(paths, domain, context, timeout) for _ in range(reps)]
    return [
        None if None in times else statistics.median(times)
        for times in zip(*runs, strict=True)
    ]


def wasm(paths, domain, context, timeout):
    """In-process analysis time of the browser bundle, one Node process per batch as a page
    session reuses its worker; a batch that crashes is retried one fixture at a time."""
    policy, depth = (
        ("call-string", int(context.rsplit("-", 1)[1]))
        if context.startswith("call-string")
        else (context, 0)
    )
    calls = [
        [
            domain,
            "warrow",
            policy,
            depth,
            "fixpoint",
            "flow-sensitive",
            p.read_text(),
            "off",
        ]
        for p in paths
    ]
    try:
        p = subprocess.run(
            [
                "node",
                f"--stack-size={WASM_STACK_KIB}",
                "--require",
                str(HARNESS),
                str(BUNDLE),
            ],
            capture_output=True,
            text=True,
            cwd=REPO,
            timeout=timeout * len(paths) + 30,
            env={**os.environ, "VOBLINT_WEB_CALLS": json.dumps(calls)},
        )
    except subprocess.TimeoutExpired:
        p = None
    if p is None or p.returncode:
        if len(paths) == 1:
            return [None]
        return [ms for q in paths for ms in wasm([q], domain, context, timeout)]
    return [
        a["timing"]["analysis_ms"] if a["status"] == "ok" else None
        for a in map(json.loads, json.loads(p.stdout))
    ]


def depth_program(n):
    return (
        "fun h(i) {\n  if (i == 0) { return 3; }\n  r = h(i - 1);\n  return r;\n}\n"
        f"fun main() {{\n  x = h({n}); __voblint_check(x == 3);\n}}\n"
    )


def depth_sweep(reps, timeout):
    """h(n) under entry-state for every domain, n growing until a run passes the timeout."""
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        for domain in DOMAINS:
            for n in DEPTHS:
                f = Path(tmp) / f"h{n}.vimp"
                f.write_text(depth_program(n))
                row = {"domain": domain, "n": n, "native_ms": None, "wasm_ms": None}
                try:
                    result = timed_reps(f, domain, "entry-state", reps, timeout)
                except subprocess.TimeoutExpired:
                    result = {"status": "timeout"}
                if result["status"] == "ok":
                    row.update(
                        native_ms=result["ms"],
                        wall_ms=result["wall_ms"],
                        rss=result["rss"],
                        **solver_work(f, domain, "entry-state", timeout),
                    )
                    row["wasm_ms"] = wasm_reps(
                        [f], domain, "entry-state", reps, timeout
                    )[0]
                else:
                    row["status"] = result["status"]
                rows.append(row)
                print(
                    f"  {domain} n={n}: native {row['native_ms']}, wasm {row['wasm_ms']}",
                    flush=True,
                )
                if result["status"] != "ok":
                    break  # deeper runs only take longer
    return rows


# Programs that each grow one size parameter n and keep everything else small, so a
# solve time that grows faster than the solver's evaluations exposes the cost of the
# generated code's list-based sets and maps along that one dimension.
def _vars(n):
    xs = [f"x{k}" for k in range(n)]
    body = "".join(f"  {x} = {k};\n" for k, x in enumerate(xs))
    loop = "".join(f"    {x} = {x} + 1;\n" for x in xs)
    return (
        f"fun main() {{\n{body}  i = 0;\n  while (i < 3) {{\n{loop}    i = i + 1;\n  }}\n"
        f"  __voblint_check(0 < x{n - 1});\n}}\n"
    )


def _points(n):
    body = "".join("  x = x + 1;\n" for _ in range(n))
    return f"fun main() {{\n  x = 0;\n{body}  __voblint_check(0 < x);\n}}\n"


def _globals(n):
    # One declaration: VIMP takes a single comma-separated global list.
    decls = "global " + ", ".join(f"g{k}" for k in range(n)) + ";\n"
    writes = "".join(f"  g{k} = {k + 1};\n" for k in range(n))
    return (
        f"{decls}fun set() {{\n{writes}  return 0;\n}}\n"
        f"fun main() {{\n  set();\n  __voblint_check(0 < g0);\n}}\n"
    )


def _call_sites(n):
    calls = "".join(f"  y{k} = f(1);\n" for k in range(n))
    return (
        f"fun f(a) {{\n  return a;\n}}\n"
        f"fun main() {{\n{calls}  __voblint_check(y0 == 1);\n}}\n"
    )


def _procs(n):
    chain = "".join(
        f"fun p{k}(a) {{\n  r = p{k + 1}(a);\n  return r;\n}}\n" for k in range(n - 1)
    )
    return (
        f"{chain}fun p{n - 1}(a) {{\n  return a;\n}}\n"
        f"fun main() {{\n  x = p0(1);\n  __voblint_check(x == 1);\n}}\n"
    )


def _loops(n):
    loop = "  i = 0;\n  while (i < 10) {\n    i = i + 1;\n  }\n"
    return f"fun main() {{\n{loop * n}  __voblint_check(i == 10);\n}}\n"


# name -> (what grows, program, domain, context policy). Call sites run twice: call
# strings give each site its own context, while entry-state shares one context across the
# identical calls, which separates the number of contexts from the number of call sites.
SCALING = {
    "variables": ("variables in one procedure", _vars, "interval", "none"),
    "points": ("straight-line statements", _points, "interval", "none"),
    "globals": ("globals written by one procedure", _globals, "interval", "none"),
    "call-sites-k1": (
        "call sites, one context each (call strings, k = 1)",
        _call_sites,
        "interval",
        "call-string-1",
    ),
    "call-sites-entry": (
        "call sites sharing one context (entry-state)",
        _call_sites,
        "interval",
        "entry-state",
    ),
    "procedures": ("procedures in a call chain", _procs, "interval", "none"),
    "loops": ("sequential loops", _loops, "interval", "none"),
    "recursion": (
        "recursion depth (entry-state)",
        depth_program,
        "interval",
        "entry-state",
    ),
}
SCALING_SIZES = [10, 20, 50, 100, 200, 500, 1000, 2000, 5000]
# The size at which the page shows each family's program: large enough to show the
# repeated pattern, small enough to read.
EXAMPLE_N = 4


def scaling_examples():
    return {
        family: {"n": EXAMPLE_N, "source": program(EXAMPLE_N)}
        for family, (_, program, _, _) in SCALING.items()
    }


def scaling_sweep(reps, timeout):
    """Each family at growing n until a run passes the timeout or fails."""
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        for family, (what, program, domain, context) in SCALING.items():
            for n in SCALING_SIZES:
                f = Path(tmp) / f"{family}-{n}.vimp"
                f.write_text(program(n))
                row = {
                    "family": family,
                    "what": what,
                    "domain": domain,
                    "context": context,
                    "n": n,
                    "native_ms": None,
                }
                try:
                    result = timed_reps(f, domain, context, reps, timeout)
                except subprocess.TimeoutExpired:
                    result = {"status": "timeout"}
                if result["status"] == "ok":
                    row.update(
                        native_ms=result["ms"],
                        wall_ms=result["wall_ms"],
                        rss=result["rss"],
                        **solver_work(f, domain, context, timeout),
                    )
                else:
                    row["status"] = result["status"]
                rows.append(row)
                print(f"  {family} n={n}: {row['native_ms']}", flush=True)
                if result["status"] != "ok":
                    break  # larger programs only take longer
    return rows


def loglog_slope(points):
    pts = [(math.log(x), math.log(y)) for x, y in points if x > 0 and y > 0]
    if len(pts) < 2:
        return 0.0
    mx = sum(p[0] for p in pts) / len(pts)
    my = sum(p[1] for p in pts) / len(pts)
    den = sum((a - mx) ** 2 for a, _ in pts)
    return sum((a - mx) * (b - my) for a, b in pts) / den if den else 0.0


def scaling_target(rows):
    """The family whose solve time outgrows its evaluations most, at its largest finished n.

    Times are fitted from n = 100, where start-up no longer dominates; evaluations are
    exact counts and fitted from every traced size from n = 20, since tracing passes the
    time limit at smaller n than timing does."""
    best = None
    for family, (_, program, domain, context) in SCALING.items():
        timed = [
            r
            for r in rows
            if r["family"] == family and r.get("native_ms") and r["n"] >= 100
        ]
        traced = [
            r for r in rows if r["family"] == family and r.get("evals") and r["n"] >= 20
        ]
        if len(timed) < 3 or len(traced) < 3:
            continue
        gap = loglog_slope([(r["n"], r["native_ms"]) for r in timed]) - loglog_slope(
            [(r["n"], r["evals"]) for r in traced]
        )
        top = max(timed, key=lambda r: r["n"])
        if best is None or gap > best[0]:
            best = (
                gap,
                (f"{family} n={top['n']}", None, domain, context, program(top["n"])),
            )
    return best[1] if best else None


# The recursion stress case is always profiled; the rest are the corpus's slowest fixtures.
STRESS_TARGET = ("h(1000)", None, "interval", "entry-state", depth_program(1000))
SLOWEST_PROFILED = 3


def flame_targets(runs, scaling=None):
    """h(1000), the scaling family whose time outgrows its work most, then the slowest
    distinct fixtures, each under its slowest configuration."""
    targets, seen = [STRESS_TARGET], set()
    extra = scaling_target(scaling) if scaling else None
    if extra:
        targets.append(extra)
    ok = [r for r in runs if r.get("status") == "ok" and r.get("ms") is not None]
    for r in sorted(ok, key=lambda r: -r["ms"]):
        if r["fixture"] in seen:
            continue
        seen.add(r["fixture"])
        targets.append(
            (Path(r["fixture"]).stem, r["fixture"], r["domain"], r["context"], None)
        )
        if len(targets) > SLOWEST_PROFILED + (1 if extra else 0):
            break
    return targets


THREAD_LINE = re.compile(r"^ {4}(\d+) Thread_")
SAMPLE_LINE = re.compile(
    r"^(?P<indent>[ +!:|]*)(?P<count>\d+) (?P<frame>.+?)  \(in [^)]*\)"
)
# A frame below this share of the samples folds into its parent's self time.
FLAME_MIN_SHARE = 0.002


def frame_name(raw):
    """camlVoblint_Generated$map_4218 -> Voblint_Generated.map; runtime symbols stay as they are."""
    m = re.fullmatch(r"caml(?:Dune__exe__)?([A-Z]\w*?)\$(.+?)(?:_\d+)?", raw)
    return f"{m.group(1)}.{m.group(2)}" if m else raw


def parse_sample(text):
    """The main thread's call graph from macOS `sample` output, as a {name, value, children} tree."""
    root = None
    stack = []
    for line in text.split("Call graph:", 1)[1].splitlines()[1:]:
        if not line.strip():
            break
        thread = THREAD_LINE.match(line)
        if thread:
            if root is not None:
                break  # later threads: the analysis runs on the main thread only
            root = {
                "name": "all samples",
                "value": int(thread.group(1)),
                "children": [],
            }
            stack = [root]
            continue
        m = SAMPLE_LINE.match(line[4:])
        if not m or root is None:
            continue
        depth = len(m.group("indent")) // 2
        node = {
            "name": m.group("frame").split()[0],
            "value": int(m.group("count")),
            "children": [],
        }
        del stack[depth:]
        stack[-1]["children"].append(node)
        stack.append(node)
    return root


def merge_siblings(children):
    by_name = {}
    for c in children:
        if c["name"] in by_name:
            m = by_name[c["name"]]
            m["value"] += c["value"]
            m["children"].extend(c["children"])
            m["recursion"] = max(m.get("recursion", 1), c.get("recursion", 1))
        else:
            by_name[c["name"]] = c
    for m in by_name.values():
        m["children"] = merge_siblings(m["children"])
    return list(by_name.values())


def collapse_recursion(node):
    """Merges every call of a frame into a same-named parent, as flame-graph tools do for
    recursion, so a 1000-deep List.map is one bar; [recursion] keeps how deep it went."""
    levels = 1
    while any(c["name"] == node["name"] for c in node["children"]):
        lifted = []
        for c in node["children"]:
            lifted.extend(c["children"] if c["name"] == node["name"] else [c])
        node["children"] = merge_siblings(lifted)
        levels += 1
    if levels > 1:
        node["recursion"] = max(levels, node.get("recursion", 1))
    for child in node["children"]:
        collapse_recursion(child)


# Frames a complete stack starts from; any other root is a stack `sample` cut short.
ENTRY_FRAMES = re.compile(
    r"^(camlDune__exe__Voblint_main\$|start$|main$|caml_main|caml_start_program|caml_program)"
)


def group_truncated(root):
    real = [c for c in root["children"] if ENTRY_FRAMES.match(c["name"])]
    cut = [c for c in root["children"] if not ENTRY_FRAMES.match(c["name"])]
    if cut:
        real.append(
            {
                "name": "[callers not recorded]",
                "truncated": True,
                "value": sum(c["value"] for c in cut),
                "children": merge_siblings(cut),
            }
        )
    root["children"] = real


def prune(node, floor):
    node["children"] = [c for c in node["children"] if c["value"] >= floor]
    for c in node["children"]:
        prune(c, floor)


def parse_samply(profile_path, syms_path):
    """The analysis thread's stacks from a samply profile and its symbol sidecar, as a
    {name, value, children} tree rooted at "all samples"."""
    profile = json.load(gzip.open(profile_path))
    syms = json.loads(Path(syms_path).read_text())
    strings = syms["string_table"]
    tables = {}
    for lib in syms["data"]:
        entries = sorted(lib["symbol_table"], key=lambda e: e["rva"])
        tables[lib["debug_name"]] = ([e["rva"] for e in entries], entries)
    thread = max(profile["threads"], key=lambda t: len(t["samples"]["stack"]))
    frames, funcs, resources = (
        thread["frameTable"],
        thread["funcTable"],
        thread["resourceTable"],
    )
    libs = profile["libs"]

    def symbol(frame):
        lib = libs[resources["lib"][funcs["resource"][frames["func"][frame]]]][
            "debugName"
        ]
        address = frames["address"][frame]
        rvas, entries = tables.get(lib, ([], []))
        i = bisect.bisect_right(rvas, address) - 1
        if i >= 0 and address < entries[i]["rva"] + entries[i]["size"]:
            return strings[entries[i]["symbol"]]
        return "???"

    stacks = thread["stackTable"]
    root = {"name": "all samples", "value": 0, "children": []}
    node_of = {}

    def node(stack):
        # Iterative: stacks are hundreds of frames deep, deeper than Python's recursion limit.
        path = []
        while stack is not None and stack not in node_of:
            path.append(stack)
            stack = stacks["prefix"][stack]
        parent = node_of[stack] if stack is not None else root
        for s in reversed(path):
            name = symbol(stacks["frame"][s])
            child = next((c for c in parent["children"] if c["name"] == name), None)
            if child is None:
                child = {"name": name, "value": 0, "children": []}
                parent["children"].append(child)
            node_of[s] = parent = child
        return parent

    weights = thread["samples"].get("weight") or [1] * len(thread["samples"]["stack"])
    for stack, weight in zip(thread["samples"]["stack"], weights, strict=True):
        if stack is None:
            continue
        node(stack)
        root["value"] += weight
        # Inclusive counts: every frame on the path gets the sample.
        s = stack
        while s is not None:
            node_of[s]["value"] += weight
            s = stacks["prefix"][s]
    return root


def analysis_child(proc):
    """The CLI runs the analysis in a forked child so it can enforce --timeout; profile that."""
    for _ in range(500):
        child = out(["pgrep", "-P", str(proc.pid)]).split()
        if child or proc.poll() is not None:
            return child[0] if child else None
        time.sleep(0.002)
    return None


def record_samply(cmd, tmp):
    """samply attached to the analysis child; it records until it is interrupted."""
    profile = Path(tmp) / "profile.json.gz"
    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL)
    child = analysis_child(proc)
    if child is None:
        proc.wait()
        return None
    recorder = subprocess.Popen(
        [
            "samply",
            "record",
            "--save-only",
            "--unstable-presymbolicate",
            "-o",
            str(profile),
            "-p",
            child,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    proc.wait()
    recorder.send_signal(signal.SIGINT)
    _, err = recorder.communicate(timeout=120)
    if recorder.returncode != 0 or not profile.exists():
        print(
            f"  samply failed: {err.strip().splitlines()[-1] if err.strip() else recorder.returncode}"
            " (attaching needs `samply setup` once)",
            flush=True,
        )
        return None
    return parse_samply(profile, Path(tmp) / "profile.json.syms.json")


def record_sample(cmd, tmp, timeout):
    """macOS `sample`: no setup, but it keeps only the innermost 512 frames of a stack."""
    out_file = Path(tmp) / "sample.txt"
    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL)
    child = analysis_child(proc)
    if child:
        subprocess.run(
            ["sample", child, str(timeout), "1", "-mayDie", "-file", str(out_file)],
            capture_output=True,
            text=True,
        )
    proc.wait()
    return parse_sample(out_file.read_text()) if out_file.exists() else None


TOP_LEVEL_DEF = r"^(?:let rec|let|and) {}\b"
SYMBOL = re.compile(r"caml(?:Dune__exe__)?([A-Z]\w*?)\$(.+)_(\d+)")


class SourceIndex:
    """Where a native symbol's function is defined, from the source rather than debug info:
    the native binary on macOS carries no line tables. OCaml numbers a module's functions in
    definition order, so the k-th symbol of a name is the k-th top-level definition of it
    whenever the two counts agree; otherwise, and for anonymous closures, there is no line."""

    def __init__(self):
        self.stamps = {}
        for line in out(["nm", str(CLI)]).splitlines():
            m = SYMBOL.fullmatch(line.split()[-1].lstrip("_")) if line else None
            if m:
                self.stamps.setdefault((m.group(1), m.group(2)), set()).add(
                    int(m.group(3))
                )
        self.files = {}
        for root in ("codegen/generated/ml", "cli"):
            for f in (REPO / root).rglob("*.ml"):
                if "_build" not in f.parts:
                    self.files.setdefault(f.stem.lower(), f)
        self.text = {}

    def locate(self, raw):
        m = SYMBOL.fullmatch(raw)
        if not m or m.group(2) == "fun":
            return None
        module, name, stamp = m.group(1), m.group(2), int(m.group(3))
        path = self.files.get(module.lower())
        if path is None:
            return None
        if path not in self.text:
            self.text[path] = path.read_text().splitlines()
        pattern = re.compile(TOP_LEVEL_DEF.format(re.escape(name)))
        defs = [i + 1 for i, text in enumerate(self.text[path]) if pattern.match(text)]
        stamps = sorted(self.stamps.get((module, name), ()))
        if not defs or len(defs) != len(stamps) or stamp not in stamps:
            return None
        return {"path": str(path.relative_to(REPO)), "line": defs[stamps.index(stamp)]}


def finish(node, sources):
    """Display names and source locations, once merging by raw symbol is done."""
    raw = node["name"]
    node["name"] = frame_name(raw)
    where = sources.locate(raw)
    if where:
        node["source"] = where
    for c in node["children"]:
        finish(c, sources)


def flame_profiles(targets, timeout):
    if platform.system() != "Darwin":
        print("  skipped: CPU profiles are recorded on macOS only", flush=True)
        return None
    profiler = (
        "samply"
        if shutil.which("samply")
        else "sample"
        if shutil.which("sample")
        else None
    )
    if profiler is None:
        print("  skipped: neither samply nor sample is installed", flush=True)
        return None
    version = out(["samply", "--version"]) if profiler == "samply" else "macOS sample"
    profiles = []
    sources = SourceIndex()
    with tempfile.TemporaryDirectory() as tmp:
        for title, fixture, domain, context, source in targets:
            src = CORPUS / fixture if fixture else Path(tmp) / "program.vimp"
            if not fixture:
                src.write_text(source)
            cmd = [*cli_args(domain, context, timeout), str(src)]
            tree = (
                record_samply(cmd, tmp)
                if profiler == "samply"
                else record_sample(cmd, tmp, timeout)
            )
            if tree is None or not tree["value"]:
                print(f"  {title}: no samples", flush=True)
                continue
            group_truncated(tree)
            collapse_recursion(tree)
            prune(tree, tree["value"] * FLAME_MIN_SHARE)
            finish(tree, sources)
            profiles.append(
                {
                    "title": title,
                    "fixture": fixture,
                    "domain": domain,
                    "context": context,
                    # A generated program has no fixture path, so its link carries the source.
                    **({} if fixture else {"source": src.read_text()}),
                    "profiler": version,
                    "interval_ms": 1,
                    "samples": tree["value"],
                    "tree": tree,
                }
            )
            print(f"  {title}: {tree['value']} samples with {version}", flush=True)
    return profiles


def write_snapshot(snapshot, label):
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    meta = snapshot["meta"]
    name = f"{meta['date']}-{meta['commit']}.json"
    (OUT_DIR / name).write_text(json.dumps(snapshot, separators=(",", ":")) + "\n")
    index_path = OUT_DIR / "index.json"
    index = (
        json.loads(index_path.read_text()) if index_path.exists() else {"snapshots": []}
    )
    entry = {
        "label": label
        or f"{meta['commit']} · {meta['date']} · {meta['device']['cpu']}",
        "file": f"data/profiling/{name}",
    }
    index["snapshots"] = [
        entry,
        *(s for s in index["snapshots"] if s["file"] != entry["file"]),
    ]
    index_path.write_text(json.dumps(index, indent=2) + "\n")
    return OUT_DIR / name


PHASES = ("native", "wasm", "depth", "scaling", "flame")
# Where each phase stores its results in a snapshot.
PHASE_KEYS = {
    "native": "runs",
    "wasm": "browser",
    "depth": "depth",
    "scaling": "scaling",
    "flame": "flame",
}


def browser_runs(fixtures, runs, reps, timeout):
    """The browser bundle on every fixture and configuration whose native solve finished.

    The Node harness has no timeout of its own, so a program that runs past the limit
    natively would stall its whole batch; such runs are recorded as skipped instead."""
    finished = {
        (r["fixture"], r["domain"], r["context"])
        for r in runs
        if r.get("status") == "ok"
    }
    rows = []
    for domain in DOMAINS:
        for context in CONTEXTS:
            print(f"  {domain} / {context}", flush=True)
            todo = []
            for p in fixtures:
                name = str(p.relative_to(CORPUS))
                if (name, domain, context) in finished:
                    todo.append(p)
                else:
                    rows.append(
                        {
                            "fixture": name,
                            "domain": domain,
                            "context": context,
                            "wasm_ms": None,
                            "skipped": "native run did not finish",
                        }
                    )
            for i in range(0, len(todo), 40):
                batch = todo[i : i + 40]
                times = wasm_reps(batch, domain, context, reps, timeout)
                for p, ms in zip(batch, times, strict=True):
                    rows.append(
                        {
                            "fixture": str(p.relative_to(CORPUS)),
                            "domain": domain,
                            "context": context,
                            "wasm_ms": ms,
                        }
                    )
    return rows


def revision():
    dirty = bool(
        out(["git", "-C", str(REPO), "status", "--porcelain", "--untracked-files=no"])
    )
    origin = out(["git", "-C", str(REPO), "remote", "get-url", "origin"])
    return {
        "commit": out(["git", "-C", str(REPO), "rev-parse", "--short", "HEAD"])
        + ("-dirty" if dirty else ""),
        # Source links in the CPU profiles point at this revision.
        "commit_sha": out(["git", "-C", str(REPO), "rev-parse", "HEAD"]),
        "repo_url": re.sub(
            r"(\.git)?$",
            "",
            re.sub(r"^git@github\.com:", "https://github.com/", origin),
        ),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--reps", type=int, default=3, help="timed runs per fixture and configuration"
    )
    ap.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="parallel native runs; more is faster but adds timing noise",
    )
    ap.add_argument(
        "--timeout",
        type=int,
        default=30,
        help="seconds before a run counts as a timeout",
    )
    ap.add_argument(
        "--filter", default="", help="only fixtures whose path contains this"
    )
    ap.add_argument("--label", default="", help="the snapshot's name on the page")
    ap.add_argument(
        "--phases",
        default=",".join(PHASES),
        help=f"comma list of phases to run, from {', '.join(PHASES)}",
    )
    ap.add_argument(
        "--update",
        type=Path,
        help="re-run --phases into this existing snapshot instead of writing a new one",
    )
    ap.add_argument(
        "--resume",
        action="store_true",
        help="continue a run that stopped, from build/profiling-partial.json",
    )
    args = ap.parse_args()
    phases = [x for x in args.phases.split(",") if x]
    if unknown := set(phases) - set(PHASES):
        sys.exit(f"unknown phases: {', '.join(sorted(unknown))}")

    for need in (CLI, BUNDLE):
        if not need.exists():
            sys.exit(
                f"{need} missing: run `pixi run cli-build` and `pixi run browser-build`"
            )
    if not shutil.which("node"):
        sys.exit("node not on PATH")

    snapshot = json.loads(args.update.read_text()) if args.update else {}
    filter_ = (
        snapshot.get("meta", {}).get("filter") or "" if args.update else args.filter
    )
    fixtures = sorted(
        p
        for p in CORPUS.rglob("*.vimp")
        if filter_ in str(p) and "--timeout" not in (param_args(p) or [])
    )
    started = time.time()

    # Each finished phase is saved, so a run that dies keeps what it measured; --resume
    # continues it, but only at the commit that measured it.
    partial_path = REPO / "build" / "profiling-partial.json"
    head = revision()["commit_sha"]
    if args.resume and partial_path.exists():
        partial = json.loads(partial_path.read_text())
        if partial.get("commit_sha") == head and not args.update:
            snapshot.update(partial["snapshot"])
            print(
                f"resuming: {', '.join(partial['done'])} already measured", flush=True
            )
        else:
            print(
                "not resuming: the partial run was measured at another commit",
                flush=True,
            )

    def done(phase, key):
        partial_path.parent.mkdir(parents=True, exist_ok=True)
        finished = [p for p, k in PHASE_KEYS.items() if k in snapshot]
        partial_path.write_text(
            json.dumps({"commit_sha": head, "done": finished, "snapshot": snapshot})
        )
        print(f"  saved {phase} to {partial_path.relative_to(REPO)}", flush=True)

    def wanted(phase):
        return phase in phases and (args.update or PHASE_KEYS[phase] not in snapshot)

    if wanted("native"):
        jobs = [(p, d, c) for p in fixtures for d in DOMAINS for c in CONTEXTS]
        print(
            f"native: {len(jobs)} runs x {args.reps} reps, {args.jobs} at a time",
            flush=True,
        )
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            snapshot["runs"] = list(
                pool.map(lambda j: native(j, args.reps, args.timeout), jobs)
            )
        done("native", "runs")
    if wanted("wasm"):
        print("wasm: every domain and context policy", flush=True)
        if "runs" not in snapshot:
            sys.exit(
                "the browser phase compares against the native runs; run that phase"
            )
        snapshot["browser"] = browser_runs(
            fixtures, snapshot["runs"], args.reps, args.timeout
        )
        done("wasm", "browser")
    if wanted("depth"):
        print("depth sweep", flush=True)
        snapshot["depth"] = depth_sweep(args.reps, args.timeout)
        done("depth", "depth")
    if wanted("scaling"):
        print("scaling families", flush=True)
        snapshot["scaling"] = scaling_sweep(args.reps, args.timeout)
        snapshot["scaling_examples"] = scaling_examples()
        done("scaling", "scaling")
    if wanted("flame"):
        print("CPU profiles", flush=True)
        if "runs" not in snapshot:
            sys.exit(
                "CPU profiles pick their programs from the native runs; run that phase"
            )
        snapshot["flame"] = flame_profiles(
            flame_targets(snapshot["runs"], snapshot.get("scaling")), args.timeout
        )
        done("flame", "flame")

    if args.update:
        # A partial re-run keeps the original measurement's metadata and says what changed.
        snapshot["meta"].setdefault("updates", []).append(
            {
                "phases": phases,
                "date": time.strftime("%Y-%m-%d"),
                "duration_s": round(time.time() - started),
                "cpu": device()["cpu"],
                **revision(),
            }
        )
        for key in ("commit_sha", "repo_url"):
            snapshot["meta"].setdefault(key, revision()[key])
        args.update.write_text(json.dumps(snapshot, separators=(",", ":")) + "\n")
        print(f"updated {args.update} in {round(time.time() - started)} s")
        return

    if set(phases) != set(PHASES):
        sys.exit("a new snapshot needs every phase; use --update for a partial re-run")
    snapshot["meta"] = {
        **revision(),
        "date": time.strftime("%Y-%m-%d"),
        "duration_s": round(time.time() - started),
        "device": device(),
        "reps": args.reps,
        "jobs": args.jobs,
        "timeout_s": args.timeout,
        "wasm_stack_kib": WASM_STACK_KIB,
        "fixtures": len(fixtures),
        "filter": args.filter or None,
    }
    path = write_snapshot(snapshot, args.label)
    partial_path.unlink(missing_ok=True)
    print(f"wrote {path.relative_to(REPO)} in {snapshot['meta']['duration_s']} s")


if __name__ == "__main__":
    main()
