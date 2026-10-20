#!/usr/bin/env python3
"""Lift the profiling page's measurements into thesis data.

`scripts/profile_corpus.py` records snapshots under ``pages/data/profiling/`` for the
site's profiling page. The thesis cites one of them, pinned in
``thesis/shared/profiling.toml``, so its numbers belong to a fixed measurement rather
than whichever snapshot is newest. This tool reduces that snapshot to the figures the
evaluation prints and writes ``thesis/shared/generated/profiling.json``; the thesis
reads that file. It never writes to ``pages/``.

The reductions match the page's readings: solve times are the CLI's own ``--timing``
medians, ratios use only runs of at least ``RATIO_FLOOR_MS`` natively, and power-law
slopes are least-squares fits on log-log axes from ``n = 100`` up.

    python3 thesis/tools/profiling.py            # write
    python3 thesis/tools/profiling.py --check    # fail when the file is stale
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from pathlib import Path

import tomllib

REPO = Path(__file__).resolve().parents[2]
PIN = REPO / "thesis" / "shared" / "profiling.toml"
OUT = REPO / "thesis" / "shared" / "generated" / "profiling.json"

RATIO_FLOOR_MS = 1.0
SLOPE_FROM_N = 100
# The CPU profile the thesis describes, by its title in the snapshot.
STRESS_PROFILE = "h(1000)"
LOOKUP_FRAMES = ("Voblint_Generated.membera", "caml_apply2")


def slope(points):
    pts = [(math.log(x), math.log(y)) for x, y in points if x > 0 and y > 0]
    if len(pts) < 3:
        return None
    mx = statistics.fmean(p[0] for p in pts)
    my = statistics.fmean(p[1] for p in pts)
    return sum((a - mx) * (b - my) for a, b in pts) / sum((a - mx) ** 2 for a, _ in pts)


def inclusive(node, name, inside=False):
    """Samples whose stack contains a frame named [name], each sample counted once."""
    if not inside and node["name"] == name:
        return node["value"]
    return sum(inclusive(c, name, inside) for c in node["children"])


def self_times(node, acc):
    own = node["value"] - sum(c["value"] for c in node["children"])
    if own > 0:
        acc[node["name"]] = acc.get(node["name"], 0) + own
    for c in node["children"]:
        self_times(c, acc)
    return acc


def summarize(snapshot, source):
    meta = snapshot["meta"]
    runs = [r for r in snapshot["runs"] if r["status"] in ("ok", "rejected", "timeout")]
    ok = [r for r in runs if r["status"] == "ok" and r.get("ms") is not None]
    solves = sorted(r["ms"] for r in ok)

    native = {(r["fixture"], r["domain"], r["context"]): r["ms"] for r in ok}
    ratios = [
        b["wasm_ms"] / native[key]
        for b in snapshot.get("browser", [])
        if b["wasm_ms"] is not None
        and (key := (b["fixture"], b["domain"], b["context"])) in native
        and native[key] >= RATIO_FLOOR_MS
    ]

    # The slowest 5% of runs and their share of all solve time.
    top = max(1, round(len(solves) * 0.05))
    top_share = sum(solves[-top:]) / sum(solves)

    depth = {}
    for row in snapshot.get("depth", []):
        domain = row.get("domain", "interval")
        if row.get("native_ms") is not None:
            depth.setdefault(domain, []).append(
                {
                    "n": row["n"],
                    "native_ms": row["native_ms"],
                    "wasm_ms": row.get("wasm_ms"),
                    "evals": row.get("evals"),
                    "contexts": row.get("contexts"),
                    "rss_mib": round((row.get("rss") or 0) / 2**20),
                }
            )
    fits = {
        domain: {
            "time": slope(
                [(p["n"], p["native_ms"]) for p in pts if p["n"] >= SLOPE_FROM_N]
            ),
            "evals": slope(
                [
                    (p["n"], p["evals"])
                    for p in pts
                    if p["n"] >= SLOPE_FROM_N and p["evals"]
                ]
            ),
            "max_n": max(p["n"] for p in pts),
            "contexts_at_max": max(pts, key=lambda p: p["n"])["contexts"],
        }
        for domain, pts in depth.items()
    }

    profile = next(
        (f for f in snapshot.get("flame") or [] if f["title"] == STRESS_PROFILE), None
    )
    flame = None
    if profile:
        tree = profile["tree"]
        total = tree["value"]
        own = self_times(tree, {})
        flame = {
            "samples": total,
            "solver_share": inclusive(
                tree, "Voblint_Generated.tD_side_rule_Interp_solve_rec_c"
            )
            / total,
            "report_share": inclusive(tree, "Voblint_Generated.report_of") / total,
            # Samples taken inside a list membership test, each counted once.
            "membership_share": inclusive(tree, "Voblint_Generated.membera") / total,
            "lookup_self_share": sum(
                v
                for k, v in own.items()
                if k in LOOKUP_FRAMES or k.startswith("Voblint_Generated.equal_")
            )
            / total,
            "profiler": profile.get("profiler"),
        }

    return {
        "source": source,
        "meta": {
            "commit": meta["commit"],
            "date": meta["date"],
            "cpu": meta["device"]["cpu"],
            "memory_gib": meta["device"].get("memory_gib"),
            "os": meta["device"].get("os"),
            "reps": meta["reps"],
            "timeout_s": meta["timeout_s"],
        },
        "fixtures": len({r["fixture"] for r in runs}),
        "configurations": len({(r["domain"], r["context"]) for r in runs}),
        "runs": len(runs),
        "solve_median_ms": statistics.median(solves),
        "solve_p95_ms": solves[min(len(solves) - 1, math.ceil(0.95 * len(solves)) - 1)],
        "slowest_5pct_share": top_share,
        "browser_ratio_median": statistics.median(ratios) if ratios else None,
        "browser_ratio_runs": len(ratios),
        "depth": depth,
        "depth_fits": fits,
        "flame": flame,
    }


def build():
    pin = tomllib.loads(PIN.read_text())
    source = pin["snapshot"]
    snapshot = json.loads((REPO / source).read_text())
    return json.dumps(summarize(snapshot, source), indent=2, sort_keys=True) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail when the file is stale")
    args = ap.parse_args()
    text = build()
    if args.check:
        if not OUT.exists() or OUT.read_text() != text:
            sys.exit(
                f"{OUT.relative_to(REPO)} is stale: run `pixi run thesis-profiling-write`"
            )
        return
    OUT.write_text(text)
    print(f"wrote {OUT.relative_to(REPO)}")


if __name__ == "__main__":
    main()
