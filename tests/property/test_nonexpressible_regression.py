"""Regression pins for shapes that used to be non-expressible before
the grammar-generated printer (cli/frontend/vimp_printer.ml) grew a uniform, precedence-climbing
parenthesization rule (the precedence table in manifests/vimp-grammar.yaml) covering every constructor, together with
manifests/vimp-grammar.yaml's exp_paren production (`LPAREN exp RPAREN`, passthrough).

Before that: a Plus/Minus tree demoted under a Times, or a Plus/Minus chain
nested on its own right branch, had no parenthesized source form at all, so
it could not print to text that re-parsed back to the same tree. Now the
printer inserts parentheses wherever the precedence table says a subtree needs them, so
these same shapes round-trip like any other -- this file was updated from
"must fail" to "must round-trip" once that limitation was fixed (its
predecessor docstring anticipated exactly this: "if the printer
ever grows aexp parens, these would need to become positive cases instead").

Kept separate from the main round-trip property (test_roundtrip.py) as
concrete regression anchors, not just probabilistic Hypothesis coverage.
"""

import pytest
from oracle import run_ast_driver
from strategies import main_program

# Declarations below the top level of a body: the printer declares a local at the
# first statement that writes it, at any depth, so these print and parse back.
NESTED_DECLARATION_PROGRAMS = [
    # if (1) { i32 x = 1; }
    (
        "declaration-in-if",
        (
            [],
            ([("x", "i32")], ("If", ("N", "1"), ("Assign", "x", ("N", "1")), "Skip")),
            [],
        ),
    ),
    # while (0) { u8 y; }
    (
        "declaration-in-while",
        ([], ([("y", "u8")], ("While", ("N", "0"), ("Random", "y"))), []),
    ),
    # if (1) { skip; } else { i64 z = min(1, 2); }
    (
        "call-declaration-in-else",
        (
            [],
            (
                [("z", "i64")],
                (
                    "If",
                    ("N", "1"),
                    "Skip",
                    ("Call", ("Some", "z"), "min", [("N", "1"), ("N", "2")]),
                ),
            ),
            [],
        ),
    ),
]

PAREN_REQUIRED_PROGRAMS = [
    # Times(Plus(a, b), c): a Plus demoted under Times.
    (
        "times-over-plus",
        (
            main_program(
                ["a", "b", "c", "x"],
                (
                    "Assign",
                    "x",
                    ("Times", ("Plus", ("V", "a"), ("V", "b")), ("V", "c")),
                ),
            )
        ),
    ),
    # Times(a, Plus(b, c)): same issue on the right branch of Times.
    (
        "times-over-plus-right",
        (
            main_program(
                ["a", "b", "c", "x"],
                (
                    "Assign",
                    "x",
                    ("Times", ("V", "a"), ("Plus", ("V", "b"), ("V", "c"))),
                ),
            )
        ),
    ),
    # Plus(a, Plus(b, c)): a Plus/Minus chain nesting on the right, not the
    # left -- source's "expr := term ((+|-) term)*" only ever nests left
    # without parens.
    (
        "plus-nested-right",
        (
            main_program(
                ["a", "b", "c", "x"],
                ("Assign", "x", ("Plus", ("V", "a"), ("Plus", ("V", "b"), ("V", "c")))),
            )
        ),
    ),
    # Minus(a, Minus(b, c)): same issue with Minus.
    (
        "minus-nested-right",
        (
            main_program(
                ["a", "b", "c", "x"],
                (
                    "Assign",
                    "x",
                    ("Minus", ("V", "a"), ("Minus", ("V", "b"), ("V", "c"))),
                ),
            )
        ),
    ),
]


@pytest.mark.parametrize(
    "prog",
    [p for _, p in PAREN_REQUIRED_PROGRAMS],
    ids=[n for n, _ in PAREN_REQUIRED_PROGRAMS],
)
def test_paren_required_shape_roundtrips(prog):
    result = run_ast_driver(prog)
    assert result.stdout.strip() == "OK", (
        f"expected {prog!r} to round-trip via printer-inserted parens, "
        f"but ast_driver said:\n{result.stdout}"
    )


@pytest.mark.parametrize(
    "prog",
    [p for _, p in NESTED_DECLARATION_PROGRAMS],
    ids=[n for n, _ in NESTED_DECLARATION_PROGRAMS],
)
def test_nested_declaration_roundtrips(prog):
    result = run_ast_driver(prog)
    assert result.stdout.strip() == "OK", (
        f"expected {prog!r} to round-trip with its declaration nested, "
        f"but ast_driver said:\n{result.stdout}"
    )
