"""What a regression fixture declares about itself, read one way by every consumer.

A fixture's first line is `// PARAM: <voblint arguments>`, the flags
tests/run.py runs it with. A fixture may also opt into exact arithmetic
diagnostics with `// EXPECT-ARITHMETIC` and inline `// ARITH:` annotations, and
carry a graph snapshot between `// EXPECT-GRAPH-BEGIN` and `-END`. The runner,
the HTML-report audit and the playground's example corpus import these readers
from here, so none of them can read a fixture differently from the runner that
decides what it means.
"""

from __future__ import annotations

import re
from collections import Counter
from pathlib import Path

PARAM_RE = re.compile(r"^// PARAM: (.*)$")
ARITHMETIC_HEADER = "// EXPECT-ARITHMETIC"
ARITHMETIC_ENTRY_RE = re.compile(r"(WARN|ERROR) (division|remainder)-by-zero")
GRAPH_BEGIN = "// EXPECT-GRAPH-BEGIN"
GRAPH_END = "// EXPECT-GRAPH-END"

# Flags that choose what voblint prints, not what it computes.
OUTPUT_FLAGS = frozenset(
    {"--dot", "--graph-snapshot", "--parse-only", "--ast", "--html"}
)

# Flags that bound the run rather than select an analysis.
RUNNER_FLAGS = frozenset({"--timeout"})

# The analysis-selecting flags and the setting each one names.
SETTING_FLAGS = {
    "--analysis": "analyses",
    "--context": "context",
    "--context-depth": "context_depth",
    "--globals": "globals",
}


def param_args(path: Path) -> list[str] | None:
    """The PARAM header's arguments, or None when line 1 is not a PARAM header."""
    lines = path.read_text().splitlines()
    match = PARAM_RE.match(lines[0]) if lines else None
    return match.group(1).split() if match else None


def analysis_settings(args: list[str]) -> dict[str, object]:
    """The analysis a header selects, keyed by setting; absent flags are absent keys.

    `--analysis` may list several domains, comma-separated, in report order. An
    unknown flag is an error rather than skipped, so a new voblint option cannot
    silently mean nothing to a consumer that maps these settings elsewhere.
    """
    settings: dict[str, object] = {}
    rest = list(args)

    while rest:
        flag = rest.pop(0)

        if flag in OUTPUT_FLAGS:
            continue

        if flag not in SETTING_FLAGS and flag not in RUNNER_FLAGS:
            raise ValueError(f"unknown PARAM flag {flag!r}")

        if not rest:
            raise ValueError(f"PARAM flag {flag!r} has no value")

        value = rest.pop(0)

        if flag in RUNNER_FLAGS:
            continue

        key = SETTING_FLAGS[flag]
        if key == "analyses":
            settings[key] = value.split(",")
        elif key == "context_depth":
            settings[key] = int(value)
        else:
            settings[key] = value

    return settings


def shown_source(source: str) -> str:
    """The program a reader should see: without the runner's header, arithmetic
    opt-in, and graph snapshot. Verdict and ARITH comments stay; they document it."""
    lines = source.splitlines()
    if lines and PARAM_RE.match(lines[0]):
        lines = lines[1:]
    kept: list[str] = []
    in_graph = False
    for line in lines:
        text = line.strip()
        if text == GRAPH_BEGIN:
            in_graph = True
        elif text == GRAPH_END:
            in_graph = False
        elif not in_graph and text != ARITHMETIC_HEADER:
            kept.append(line)
    while kept and not kept[0].strip():
        kept.pop(0)
    # No final newline: an editor would show it as an empty last line.
    return "\n".join(kept).rstrip()


def expected_arithmetic(path: Path) -> Counter | None:
    """An opted-in fixture pins every (line, severity, operation) occurrence."""
    lines = path.read_text().splitlines()
    headers = sum(line.strip() == ARITHMETIC_HEADER for line in lines)
    if headers > 1:
        raise ValueError("duplicate EXPECT-ARITHMETIC directive")
    expected = Counter()
    for line_no, line in enumerate(lines, start=1):
        if "// ARITH" not in line:
            continue
        if not headers:
            raise ValueError(f"line {line_no}: ARITH requires {ARITHMETIC_HEADER}")
        _, annotation = line.split("// ARITH", 1)
        if not annotation.startswith(":"):
            raise ValueError(f"line {line_no}: expected '// ARITH: ...'")
        annotation = annotation[1:].strip()
        if annotation == "NONE":
            continue
        for entry in annotation.split(";"):
            match = ARITHMETIC_ENTRY_RE.fullmatch(entry.strip())
            if match is None:
                raise ValueError(
                    f"line {line_no}: malformed ARITH entry {entry.strip()!r}"
                )
            severity = "warning" if match[1] == "WARN" else "error"
            expected[line_no, severity, match[2]] += 1
    return expected if headers else None
