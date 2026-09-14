"""The source grammar's statement boundaries and braced conditional chains."""

import pytest

from oracle import dump_source, run_ast_driver, run_parse_only


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


COMPARISONS = ("<", "<=", ">", ">=", "==", "!=")


@pytest.mark.parametrize("operator", COMPARISONS)
def test_comparisons_parse_with_arithmetic_and_logic(operator):
    result = run_parse_only(
        f"fun main() {{ __voblint_check(x + 1 {operator} y * 2 && x != y); }}"
    )
    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize("first", COMPARISONS)
@pytest.mark.parametrize("second", COMPARISONS)
def test_comparison_precedence_groups(first, second):
    result = run_parse_only(
        f"fun main() {{ __voblint_check(x {first} y {second} z); }}"
    )
    same_group = (first in ("==", "!=")) == (second in ("==", "!="))
    if same_group:
        assert result.returncode == 2
        assert "parse error" in result.stderr
    else:
        assert result.returncode == 0, result.stderr

    parenthesized = run_parse_only(
        f"fun main() {{ __voblint_check((x {first} y) {second} z); }}"
    )
    assert parenthesized.returncode == 0, parenthesized.stderr


@pytest.mark.parametrize("expr, source", [
    (("Eq", ("V", "x"), ("Less", ("V", "y"), ("V", "z"))), "x == y < z"),
    (("NotEq", ("GreaterEq", ("V", "x"), ("V", "y")), ("V", "z")), "x >= y != z"),
    (("Less", ("Eq", ("V", "x"), ("V", "y")), ("V", "z")), "(x == y) < z"),
    (("Greater", ("V", "x"), ("NotEq", ("V", "y"), ("V", "z"))), "x > (y != z)"),
])
def test_mixed_comparison_grouping_roundtrips(expr, source):
    program = ([], ("Assign", "result", expr), [])
    assert f"result = {source};" in dump_source(program)
    result = run_ast_driver(program)
    assert result.stdout.strip() == "OK", result.stdout


@pytest.mark.parametrize("expr, source", [
    (("Div", ("Times", ("V", "x"), ("V", "y")), ("V", "z")), "x * y / z"),
    (("Mod", ("Div", ("V", "x"), ("V", "y")), ("V", "z")), "x / y % z"),
    (("Div", ("V", "x"), ("Times", ("V", "y"), ("V", "z"))), "x / (y * z)"),
    (("Mod", ("V", "x"), ("Div", ("V", "y"), ("V", "z"))), "x % (y / z)"),
])
def test_multiplicative_grouping_roundtrips(expr, source):
    program = ([], ("Assign", "result", expr), [])
    assert f"result = {source};" in dump_source(program)
    result = run_ast_driver(program)
    assert result.stdout.strip() == "OK", result.stdout
