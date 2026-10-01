#!/usr/bin/env python3
"""Record or compare the analyzer's user-visible output over the regression corpus.

A refactor of the verified pipeline that must not change behaviour can be checked
against a snapshot taken before it. For every fixture under tests/regression this
runs the CLI with the fixture's `// PARAM:` flags and keeps four outputs: the text
report, the graph snapshot, the verbose solver trace and the browser payload
(`--json`). The payload's `raw` field is dropped: it serializes run_voblint's
input and typed answer as Isabelle constructors, which a change to the exported
types alters by design. A fixture with a `--timeout` keeps its text report only.

Usage:
    python3 scripts/golden_outputs.py --write [DIR]   record (default build/golden)
    python3 scripts/golden_outputs.py --check [DIR]   compare, list every difference
"""

from __future__ import annotations

import json
import os
import shlex
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CORPUS = REPO / "tests" / "regression"
BIN = Path(os.environ.get("VOBLINT_BIN", REPO / "_build/default/cli/voblint.exe"))


def params(path: Path) -> list[str]:
    for line in path.read_text().splitlines():
        if line.startswith("// PARAM:"):
            return shlex.split(line.removeprefix("// PARAM:"))
    return []


def run(args: list[str]) -> str:
    done = subprocess.run(
        [str(BIN), *args], capture_output=True, text=True, cwd=REPO, check=False
    )
    return f"exit {done.returncode}\n--- stdout\n{done.stdout}--- stderr\n{done.stderr}"


def outputs(path: Path) -> dict[str, str]:
    rel = str(path.relative_to(REPO))
    flags = params(path)
    result = {"text": run([*flags, rel])}
    if "--timeout" in flags or "--analysis" not in flags:
        return result
    result["snapshot"] = run([*flags, "--graph-snapshot", rel])
    payload = subprocess.run(
        [str(BIN), *flags, "--json", rel],
        capture_output=True,
        text=True,
        cwd=REPO,
        check=False,
    ).stdout
    try:
        data = json.loads(payload)
        data.pop("raw", None)
        result["json"] = json.dumps(data, indent=1, sort_keys=True) + "\n"
    except json.JSONDecodeError:
        result["json"] = payload
    with tempfile.NamedTemporaryFile(suffix=".trace") as trace:
        run([*flags, "--trace", "--verbose", "--output", trace.name, rel])
        result["trace"] = Path(trace.name).read_text()
    return result


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in ("--write", "--check"):
        sys.exit(__doc__)
    out = Path(sys.argv[2]) if len(sys.argv) > 2 else REPO / "build" / "golden"
    cases = sorted(CORPUS.rglob("*.vimp"))
    with ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
        results = dict(zip(cases, pool.map(outputs, cases), strict=True))
    differ = []
    for path, kinds in results.items():
        stem = out / path.relative_to(CORPUS)
        for kind, text in kinds.items():
            target = stem.with_suffix(f".{kind}")
            if mode == "--write":
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(text)
            elif not target.exists() or target.read_text() != text:
                differ.append(str(target.relative_to(out)))
    if mode == "--write":
        print(f"golden_outputs: recorded {len(results)} fixture(s) in {out}")
        return 0
    for name in differ:
        print(f"golden_outputs: differs: {name}")
    print(f"golden_outputs: {len(results)} fixture(s), {len(differ)} output(s) differ")
    return 1 if differ else 0


if __name__ == "__main__":
    sys.exit(main())
