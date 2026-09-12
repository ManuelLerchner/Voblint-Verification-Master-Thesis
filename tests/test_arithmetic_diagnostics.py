"""CLI arithmetic findings: severity, occurrence coverage, and source links.

These checks inspect arithmetic findings separately from assertion verdicts: VIMP
division remains total, while a separate diagnostic reports zero divisors.
Run after `pixi run cli-build`; a missing executable is a failed prerequisite.
"""

import os
import re
import subprocess
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

from report_output import diagnostic_lines


REPO_ROOT = Path(__file__).resolve().parent.parent
VOBLINT = Path(os.environ.get("VOBLINT_BIN", REPO_ROOT / "cli/voblint"))
DIAGNOSTIC = re.compile(
    r"^(.+):(\d+):(\d+): (warning|error): "
    r"(possible (?:division|remainder) by zero|"
    r"(?:division|remainder) by zero whenever this operation is evaluated): "
    r"(.+) \[([^\]]+)\]$"
)


def run_program(tmp_path, source, *args, analysis="interval"):
    assert VOBLINT.is_file(), "cli/voblint not built -- run `pixi run cli-build`"
    path = tmp_path / "arithmetic.vimp"
    path.write_text(source)
    proc = subprocess.run(
        [str(VOBLINT), "--analysis", analysis, *args, str(path)],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0, proc.stderr
    diagnostics = []
    for line in diagnostic_lines(proc.stdout + "\n" + proc.stderr):
        if " by zero" not in line:
            continue
        match = DIAGNOSTIC.fullmatch(line)
        assert match, f"malformed arithmetic diagnostic: {line}"
        assert Path(match[1]) == path
        assert 1 <= int(match[2]) <= len(source.splitlines())
        assert int(match[3]) > 0
        assert match[7] in analysis.split(",")
        diagnostics.append(match)
    return proc, diagnostics


@pytest.mark.parametrize("analysis", ["sign", "interval", "int", "parity", "congruence"])
@pytest.mark.parametrize("operator, noun", [("/", "division"), ("%", "remainder")])
def test_zero_divisor_uses_domain_precision(tmp_path, analysis, operator, noun):
    _, findings = run_program(
        tmp_path, f"fun main() {{ x = 10 {operator} 0; }}\n", analysis=analysis
    )
    assert len(findings) == 1
    # Parity represents zero as Even, which includes nonzero integers.
    severity = "warning" if analysis == "parity" else "error"
    assert findings[0][4] == severity
    assert noun in findings[0][5]


@pytest.mark.parametrize("analysis", ["sign", "interval", "int", "parity", "congruence"])
def test_unknown_divisor_warns(tmp_path, analysis):
    _, findings = run_program(
        tmp_path,
        "fun main() { y = __voblint_nondet_int(); x = 10 / y; }\n",
        analysis=analysis,
    )
    assert len(findings) == 1
    assert findings[0].group(4, 5) == ("warning", "possible division by zero")


@pytest.mark.parametrize("analysis", ["sign", "interval", "int", "parity", "congruence"])
def test_nonzero_divisor_is_silent(tmp_path, analysis):
    _, findings = run_program(
        tmp_path, "fun main() { y = 3; x = 10 / y; z = 10 % y; }\n",
        analysis=analysis,
    )
    assert findings == []


def test_unreachable_operation_is_silent(tmp_path):
    _, findings = run_program(
        tmp_path, "fun main() { if (0) { x = 10 / 0; } else { x = 1; } }\n"
    )
    assert findings == []


@pytest.mark.parametrize("expression", ["0 && 1 / 0", "1 || 1 / 0", "1 && 1 / 0", "0 || 1 / 0"])
def test_boolean_operands_are_all_inspected(tmp_path, expression):
    _, findings = run_program(
        tmp_path, f"fun main() {{ __voblint_check({expression}); }}\n"
    )
    assert len(findings) == 1
    assert findings[0][4] == "error"


@pytest.mark.parametrize("expression", ["(10 / 0) % 0", "(10 / 0) + (10 / 0)"])
def test_distinct_arithmetic_occurrences_are_preserved(tmp_path, expression):
    _, findings = run_program(tmp_path, f"fun main() {{ x = {expression}; }}\n")
    assert len(findings) == 2
    assert all(finding[4] == "error" for finding in findings)


def test_conditional_guard_is_reported_once(tmp_path):
    _, findings = run_program(
        tmp_path,
        "fun main() { if (10 / 0) { x = 1; } else { x = 2; } }\n",
    )
    assert len(findings) == 1


@pytest.mark.parametrize("statement", ["x = f(10 / 0);", "f(10 / 0);", "x = min(10 / 0, 1);", "x = max(1, 10 / 0);"])
def test_call_arguments_are_inspected(tmp_path, statement):
    _, findings = run_program(
        tmp_path, "fun f(n) { return n; }\n" + f"fun main() {{ {statement} }}\n"
    )
    assert len(findings) == 1
    assert findings[0][2] == "2"
    assert findings[0][4] == "error"


def test_return_expression_is_inspected(tmp_path):
    _, findings = run_program(
        tmp_path,
        "fun f(n) {\n  return 10 / n;\n}\nfun main() { x = f(0); }\n",
    )
    assert len(findings) == 1
    assert findings[0][2] == "2"
    assert findings[0][4] == "error"


@pytest.mark.parametrize("context_args", [("--context", "entry-state"), ("--context", "call-string", "--context-depth", "1")])
@pytest.mark.parametrize("solver", ["join", "per-origin", "warrow", "warrow-per-origin"])
def test_contexts_aggregate_mixed_zero_and_nonzero_as_possible(tmp_path, context_args, solver):
    _, findings = run_program(
        tmp_path,
        "fun f(n) { return 10 / n; }\nfun main() { x = f(0); y = f(2); }\n",
        *context_args, "--solver", solver,
    )
    assert len(findings) == 1
    assert findings[0].group(4, 5) == ("warning", "possible division by zero")


def test_warning_does_not_change_total_execution(tmp_path):
    proc, findings = run_program(
        tmp_path,
        "fun main() { x = 7 / 0; y = 7 % 0; "
        "__voblint_check(x == 0); __voblint_check(y == 7); }\n",
    )
    assert len(findings) == 2
    assert proc.stdout.count("PROVED") == 2


def test_html_arithmetic_warning_links_to_source(tmp_path):
    out = tmp_path / "report"
    _, findings = run_program(
        tmp_path, "fun main() {\n  x = 10 / 0;\n}\n", "--html-out", str(out)
    )
    assert len(findings) == 1
    warning_docs = list((out / "warn").glob("warn*.xml"))
    assert len(warning_docs) == 1
    warning = ET.parse(warning_docs[0]).getroot().find("text")
    assert warning is not None
    assert warning.get("line") == "2"
    assert "division by zero" in "".join(warning.itertext()).lower()
    source = ET.parse(out / "files/arithmetic.vimp.xml").getroot()
    line = source.find("./ln[@nr='2']")
    assert line is not None
    assert warning_docs[0].stem in line.get("wrn", "")


@pytest.mark.parametrize("view, prefix", [("--dot", "digraph AnalysisCFG"), ("--dot-full", "digraph AnalysisCFG"), ("--graph-snapshot", "clusters:")])
def test_graph_stdout_stays_free_of_diagnostics(tmp_path, view, prefix):
    proc, findings = run_program(tmp_path, "fun main() { x = 10 / 0; }\n", view)
    assert len(findings) == 1
    assert proc.stdout.startswith(prefix)
    assert "division by zero" not in proc.stdout


def test_multiline_operations_use_statement_start_positions(tmp_path):
    _, findings = run_program(
        tmp_path,
        "fun main() {\n"
        "  // An ignored expression: 10 / 0.\n"
        "  // Comments must not shift the statement map.\n"
        "  x =\n"
        "    10 / 0;\n"
        "  y = f(0);\n"
        "}\n"
        "fun f(n) {\n"
        "  return\n"
        "    10 / n;\n"
        "}\n",
    )
    assert sorted((int(finding[2]), int(finding[3])) for finding in findings) == [(4, 3), (9, 3)]


def test_html_preserves_findings_from_every_domain(tmp_path):
    out = tmp_path / "report"
    _, findings = run_program(
        tmp_path, "fun main() {\n  x = 10 / 0;\n}\n", "--html-out", str(out),
        analysis="interval,parity",
    )
    assert sorted(finding.group(4, 7) for finding in findings) == [
        ("error", "interval"), ("warning", "parity"),
    ]
    warnings = list((out / "warn").glob("warn*.xml"))
    assert len(warnings) == 2
    messages = ["".join(ET.parse(path).getroot().itertext()) for path in warnings]
    assert any("[interval]" in message for message in messages)
    assert any("[parity]" in message for message in messages)
    source = ET.parse(out / "files/arithmetic.vimp.xml").getroot()
    line = source.find("./ln[@nr='2']")
    assert line is not None
    assert all(path.stem in line.get("wrn", "") for path in warnings)


def test_plain_report_has_two_aligned_tables(tmp_path):
    proc, findings = run_program(
        tmp_path, "fun main() { x = 10 / 0; __voblint_check(x == 0); }\n"
    )
    assert proc.stderr == ""
    assert len(findings) == 1
    arithmetic, checks = proc.stdout.split("Assertion checks\n")
    assert "Arithmetic diagnostics\nLocation  Point  Severity  Message\n" in arithmetic
    assert "Location  Point  Condition  Verdict  State\n" in checks
    assert "ERROR" in arithmetic and "PROVED" in checks
    for section, columns in [(arithmetic.split("Arithmetic diagnostics\n")[1],
                              ["Point", "Severity", "Message"]),
                             (checks, ["Point", "Condition", "Verdict", "State"])]:
        header, separator, row = section.splitlines()[:3]
        for column in columns:
            offset = header.index(column)
            assert separator[offset] == "-"
            assert row[offset] != " "


def test_empty_report_sections_are_explicit(tmp_path):
    proc, findings = run_program(tmp_path, "fun main() { x = 1; }\n")
    assert findings == []
    assert proc.stderr == ""
    assert proc.stdout.endswith("Arithmetic diagnostics\nNone\n\nAssertion checks\nNone\n")
