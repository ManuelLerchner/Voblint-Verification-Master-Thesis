"""Regression harness contracts for source-annotated arithmetic diagnostics."""

import importlib.util
import subprocess
import sys
from collections import Counter
from pathlib import Path
from unittest.mock import patch

import pytest

RUNNER = Path(__file__).with_name("run.py")
spec = importlib.util.spec_from_file_location("regression_runner", RUNNER)
runner = importlib.util.module_from_spec(spec)
# run.py configures its terminal stream; pytest's capture proxy is not one.
with patch.object(sys, "stdout", sys.__stdout__):
    spec.loader.exec_module(runner)


@pytest.fixture
def case(tmp_path, monkeypatch):
    monkeypatch.setattr(runner, "REGRESSION_DIR", tmp_path)
    monkeypatch.setattr(runner, "REPO_ROOT", tmp_path)
    path = tmp_path / "01-arithmetic.vimp"
    path.write_text(
        "// PARAM: --analysis interval\n"
        "// EXPECT-ARITHMETIC\n"
        "fun main() {\n"
        "  x = (1 / 0) + (1 / 0); // ARITH: ERROR division-by-zero; ERROR division-by-zero\n"
        "  y = 1 % 0; // ARITH: WARN remainder-by-zero\n"
        "  z = 1 / 2; // ARITH: NONE\n"
        "}\n"
    )
    return path


def diagnostic(
    path, line=4, severity="error", operation="division", analysis="interval"
):
    message = (
        f"possible {operation} by zero"
        if severity == "warning"
        else f"{operation} by zero whenever this operation is evaluated"
    )
    return f"{path}:{line}:3: {severity}: {message}: (1 / 0) [{analysis}]\n"


def matching_stderr(case):
    return diagnostic(case) * 2 + diagnostic(case, 5, "warning", "remainder")


def test_annotations_preserve_duplicate_occurrences(case):
    assert runner.expected_arithmetic(case) == Counter(
        {
            (4, "error", "division"): 2,
            (5, "warning", "remainder"): 1,
        }
    )
    assert runner.check_arithmetic(
        case, ["--analysis", "interval"], matching_stderr(case)
    ) == (True, [])


@pytest.mark.parametrize(
    "change, expected_problem",
    [
        (
            lambda path: diagnostic(path) + diagnostic(path, 5, "warning", "remainder"),
            "missing 1 error",
        ),
        (lambda path: matching_stderr(path) + diagnostic(path), "unexpected 1 error"),
        (
            lambda path: matching_stderr(path) + diagnostic(path, 6),
            "line 6: unexpected",
        ),
        (
            lambda path: matching_stderr(path) + diagnostic(path, 7),
            "line 7: unexpected",
        ),
        (
            lambda path: (
                diagnostic(path, 4, "warning") * 2
                + diagnostic(path, 5, "warning", "remainder")
            ),
            "missing 2 error",
        ),
        (
            lambda path: matching_stderr(path).replace(":4:3:", ":3:3:"),
            "line 4: missing",
        ),
    ],
)
def test_mismatches_fail_with_source_and_count(case, change, expected_problem):
    ok, problems = runner.check_arithmetic(
        case, ["--analysis", "interval"], change(case)
    )
    assert not ok
    assert any(expected_problem in problem for problem in problems)


@pytest.mark.parametrize(
    "annotation",
    [
        "WARN division-by-zerro",
        "WARNING division-by-zero",
        "",
        "NONE; ERROR division-by-zero",
    ],
)
def test_lint_rejects_malformed_annotations(case, annotation):
    case.write_text(
        "// PARAM: --analysis interval\n// EXPECT-ARITHMETIC\n"
        f"fun main() {{ x = 1 / 0; }} // ARITH: {annotation}\n"
    )
    assert any("malformed ARITH entry" in problem for problem in runner.lint_case(case))


def test_lint_requires_opt_in(case):
    case.write_text(case.read_text().replace("// EXPECT-ARITHMETIC\n", ""))
    assert any("ARITH requires" in problem for problem in runner.lint_case(case))


def test_lint_requires_verdicts_on_checks_in_warning_only_case(case):
    case.write_text(
        "// PARAM: --analysis interval\n// EXPECT-ARITHMETIC\n"
        "fun main() { __voblint_check(1); }\n"
    )
    assert any("no verdict annotation" in problem for problem in runner.lint_case(case))


@pytest.mark.parametrize(
    "change",
    [
        lambda path: diagnostic(path).replace(":4:3:", ":4:0:"),
        lambda path: diagnostic(path.with_name("other.vimp")),
        lambda path: diagnostic(path, analysis="sign"),
        lambda path: diagnostic(path).replace("error:", "warning:"),
        lambda path: diagnostic(path).replace(" [interval]", ""),
    ],
)
def test_malformed_or_misattributed_output_fails(case, change):
    assert not runner.check_arithmetic(case, ["--analysis", "interval"], change(case))[
        0
    ]


def test_directive_alone_requires_no_diagnostics(case):
    case.write_text(
        "// PARAM: --analysis interval\n// EXPECT-ARITHMETIC\nfun main() { x = 1; }\n"
    )
    assert runner.expected_arithmetic(case) == Counter()
    assert runner.check_arithmetic(case, ["--analysis", "interval"], "") == (True, [])
    assert not runner.check_arithmetic(
        case, ["--analysis", "interval"], diagnostic(case)
    )[0]


def test_existing_fixtures_do_not_acquire_warning_expectations(case):
    case.write_text("// PARAM: --analysis interval\nfun main() { x = 1 / 0; }\n")
    assert runner.expected_arithmetic(case) is None
    assert runner.check_arithmetic(
        case, ["--analysis", "interval"], diagnostic(case)
    ) == (True, [])


def test_warning_only_fixture_runs_successfully(case, monkeypatch):
    monkeypatch.setattr(
        runner,
        "run_voblint",
        lambda *_: subprocess.CompletedProcess(
            [], 0, stdout="", stderr=matching_stderr(case)
        ),
    )
    ok, messages = runner._check_case_body(case, ["--analysis", "interval"], "voblint")
    assert ok, messages
    assert any("3 arithmetic diagnostic(s)" in message for message in messages)


def test_warning_only_fixture_rejects_nonzero_exit(case, monkeypatch):
    monkeypatch.setattr(
        runner,
        "run_voblint",
        lambda *_: subprocess.CompletedProcess([], 1, stdout="", stderr="parse error"),
    )
    ok, messages = runner._check_case_body(case, ["--analysis", "interval"], "voblint")
    assert not ok
    assert any("non-zero unexpectedly" in message for message in messages)
