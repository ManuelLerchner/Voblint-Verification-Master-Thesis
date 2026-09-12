"""The source grammar's statement boundaries and braced conditional chains."""

import pytest

from oracle import run_parse_only


@pytest.mark.parametrize("source", [
    "fun main() {}",
    "fun f() { return; } fun main() { f(); }",
    "fun f(x) { return x; } fun main() { x = f(1); }",
    "fun main() { x = 1; if (x) { x = 2; } x = 3; }",
    "fun main() { if (0) {} else if (1) {} else {} }",
    "fun main() { if (0) {} else if (1) {} }",
    "fun main() { while (0) {} if (1) { __voblint_check(1); } }",
])
def test_c_style_statements_parse(source):
    result = run_parse_only(source)
    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize("source", [
    "fun main() { x = 1 }",
    "fun main() { x = 1; if (x) { x = 2; }; }",
    "fun main() { if (1) x = 1; }",
    "fun main() { if (1) {} else x = 1; }",
    "fun main() { if ((x = 1)) {} }",
    "fun main() { x := 1; }",
    "void main() { skip; }",
])
def test_invalid_statement_shapes_are_rejected(source):
    result = run_parse_only(source)
    assert result.returncode == 2
    assert "parse error" in result.stderr
