"""Pins the known, inherent round-trip limit documented in
VIMP_Source_Print.thy's string_of_aexp comment: a Plus/Minus tree demoted
under a Times, or a Plus/Minus chain nested on its own right branch, has no
parenthesized aexp source form at all, so it cannot print to text that
re-parses back to the same tree.

Kept separate from strategies.py's generators (which only ever produce
source-expressible shapes, by construction) and from the round-trip
property test: these are deliberately-excluded shapes, asserted here to
still fail the same way (not "OK") -- a regression pin, not a property.
If pretty_string_of_program ever grows aexp parens, these would need to
become positive cases instead.
"""

import pytest

from oracle import run_ast_driver

NON_EXPRESSIBLE_PROGRAMS = [
    # Times(Plus(a, b), c): a Plus demoted under Times -- the doc comment's
    # own example of a tree "not obtainable from any concrete VIMP source".
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
    # left -- source's "expr := term ((+|-) term)*" only ever nests left.
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
    "prog", [p for _, p in NON_EXPRESSIBLE_PROGRAMS], ids=[n for n, _ in NON_EXPRESSIBLE_PROGRAMS]
)
def test_non_expressible_shape_does_not_roundtrip(prog):
    result = run_ast_driver(prog)
    assert result.stdout.startswith("FAIL"), (
        f"expected {prog!r} to fail the round trip (documented grammar limit), "
        f"but ast_driver said:\n{result.stdout}"
    )
