"""Regression pins for shapes that used to be non-expressible before
VIMP_Source_Print.thy's string_of_exp grew a uniform, precedence-climbing
parenthesization rule (exp_prio) covering every constructor, together with
grammar/vimp.yaml's exp_paren production (`LPAREN exp RPAREN`, passthrough).

Before that: a Plus/Minus tree demoted under a Times, or a Plus/Minus chain
nested on its own right branch, had no parenthesized source form at all, so
it could not print to text that re-parsed back to the same tree. Now the
printer inserts parentheses wherever exp_prio says a subtree needs them, so
these same shapes round-trip like any other -- this file was updated from
"must fail" to "must round-trip" once that limitation was fixed (its
predecessor docstring anticipated exactly this: "if pretty_string_of_program
ever grows aexp parens, these would need to become positive cases instead").

Kept separate from the main round-trip property (test_roundtrip.py) as
concrete regression anchors, not just probabilistic Hypothesis coverage.
"""

import pytest

from oracle import run_ast_driver

PAREN_REQUIRED_PROGRAMS = [
    # Times(Plus(a, b), c): a Plus demoted under Times.
    (
        "times-over-plus",
        ([], ("Assign", "x", ("Times", ("Plus", ("V", "a"), ("V", "b")), ("V", "c"))), []),
    ),
    # Times(a, Plus(b, c)): same issue on the right branch of Times.
    (
        "times-over-plus-right",
        ([], ("Assign", "x", ("Times", ("V", "a"), ("Plus", ("V", "b"), ("V", "c")))), []),
    ),
    # Plus(a, Plus(b, c)): a Plus/Minus chain nesting on the right, not the
    # left -- source's "expr := term ((+|-) term)*" only ever nests left
    # without parens.
    (
        "plus-nested-right",
        ([], ("Assign", "x", ("Plus", ("V", "a"), ("Plus", ("V", "b"), ("V", "c")))), []),
    ),
    # Minus(a, Minus(b, c)): same issue with Minus.
    (
        "minus-nested-right",
        ([], ("Assign", "x", ("Minus", ("V", "a"), ("Minus", ("V", "b"), ("V", "c")))), []),
    ),
]


@pytest.mark.parametrize(
    "prog", [p for _, p in PAREN_REQUIRED_PROGRAMS], ids=[n for n, _ in PAREN_REQUIRED_PROGRAMS]
)
def test_paren_required_shape_roundtrips(prog):
    result = run_ast_driver(prog)
    assert result.stdout.strip() == "OK", (
        f"expected {prog!r} to round-trip via printer-inserted parens, "
        f"but ast_driver said:\n{result.stdout}"
    )
