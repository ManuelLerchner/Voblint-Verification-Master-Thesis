"""Property 5: every kind boundary survives the frontend, and nothing past the
last one is accepted.

A decimal constant is read at arbitrary precision and then range-checked, so
the interesting inputs are exactly the values where that reading and C
6.4.4.1p5's kind ladder branch: each kind's two extremes and one step either
side, and the two unsigned maxima that no literal may name as such. The
Hypothesis strategies draw from the same pool, but incidentally; this module
asserts the coverage rather than hoping for it.

int64's minimum is absent deliberately. It cannot be written as a decimal
literal at all: the magnitude passes the bound before the negation applies.
C has the same wart, and the frontend reproduces it rather than quietly
accepting a value the ladder has no type for.
"""

import pytest

from oracle import run_parse_only
from strategies import _BOUNDARIES

INT64_MAX = 9223372036854775807


def _program(literal: str) -> str:
    return f"void main() {{\n  int64 x;\n  x := {literal}\n}}\n"


@pytest.mark.parametrize("value", _BOUNDARIES)
def test_boundary_literal_is_accepted(value):
    result = run_parse_only(_program(str(value)))
    assert result.returncode == 0, (
        f"frontend rejected the boundary literal {value}:\n{result.stderr}"
    )


@pytest.mark.parametrize(
    "value",
    [INT64_MAX + 1, INT64_MAX + 2, 2 ** 64, 2 ** 64 - 1, 10 ** 30],
)
def test_literal_past_the_last_kind_is_rejected(value):
    result = run_parse_only(_program(str(value)))
    assert result.returncode != 0, (
        f"frontend accepted {value}, which no kind can represent"
    )
    assert "exceeds the largest kind" in result.stderr, (
        f"rejected {value}, but not with the range diagnostic:\n{result.stderr}"
    )


def test_int64_minimum_is_not_writable_as_a_literal():
    # Not a defect: the negation applies to a literal that has already passed
    # the bound. Pinned so that a future change to the reader has to decide
    # this deliberately rather than by accident.
    result = run_parse_only(_program(f"0 - {INT64_MAX + 1}"))
    assert result.returncode != 0
    assert "exceeds the largest kind" in result.stderr
