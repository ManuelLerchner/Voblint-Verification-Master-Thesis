"""Arbitrary (not left-associativity-restricted) aexp generation and a
precedence-aware printer, exercising the aexp_paren production added to
grammar/vimp.yaml -- the whole point of adding it is that a generator no
longer has to restrict itself to left-associated shapes the way
strategies.py's `terms`/`aexps` still do (a narrower, still-valid generator
now, not a necessary one -- it predates aexp_paren and hasn't been relaxed
to use it). The printer here inserts parentheses wherever the precedence
table says a subtree needs them, and the shipped grammar reconstructs the
exact same tree.

Precedence table mirrors grammar/vimp.yaml's `precedence:` section
(PLUS/MINUS at 65, STAR at 70, both left-associative) -- duplicated by hand
here rather than parsed from the YAML, since this is exercising exactly the
mechanization claim (precedence table -> printer parens) as an independent
check, not reusing the same code the generator itself uses.
"""

from hypothesis import strategies as st

from strategies import VAR_POOL, sexp  # noqa: F401  (re-exported for callers)

PRECEDENCE = {"Plus": 65, "Minus": 65, "Times": 70}
OP_TEXT = {"Plus": "+", "Minus": "-", "Times": "*"}
ATOM_PRECEDENCE = 1000  # N/V never need parens


@st.composite
def arbitrary_aexp(draw, max_depth=4):
    if max_depth <= 0 or draw(st.booleans()):
        return draw(
            st.one_of(
                st.integers(min_value=-1000, max_value=1000).map(lambda n: ("N", str(n))),
                st.sampled_from(VAR_POOL).map(lambda x: ("V", x)),
            )
        )
    op = draw(st.sampled_from(["Plus", "Minus", "Times"]))
    left = draw(arbitrary_aexp(max_depth - 1))
    right = draw(arbitrary_aexp(max_depth - 1))
    return (op, left, right)


def print_aexp(node, min_prec: int = 0) -> str:
    """Precedence-climbing printer: parenthesizes exactly when the
    subtree's own precedence is lower than what the calling context
    requires. Left-associative throughout (matches PLUS/MINUS/STAR's
    `assoc: left` in grammar/vimp.yaml): the left operand is printed
    requiring only `prec` (same precedence chains without parens), the
    right operand requiring `prec + 1` (same precedence on the right DOES
    need parens, since that would otherwise silently reassociate)."""
    tag = node[0]
    if tag in ("N", "V"):
        return node[1]
    prec = PRECEDENCE[tag]
    left = print_aexp(node[1], prec)
    right = print_aexp(node[2], prec + 1)
    text = f"{left}{OP_TEXT[tag]}{right}"
    return f"({text})" if prec < min_prec else text
