# Property-test AST<->printer oracle driver. Test-only; not part of the
# shipped voblint CLI. Copies the same Voblint_CLI.ml / vimp_parser.mly /
# vimp_lexer.mll / vimp_frontend.ml sources ../../cli (the main CLI) builds
# from, so ocamlopt's .cmi/.cmx build byproducts land here rather than
# polluting ../../cli, and menhir/ocamllex run on local copies.
#
# `make test` runs the Hypothesis property suite (round-trip, mutation
# fuzzing, non-expressible-shape regressions) against ast_driver and voblint
# both; `python3 -m venv ../../.venv && ../../.venv/bin/pip install -r
# requirements.txt` once beforehand to provide hypothesis/pytest.

.PHONY: all test clean

all: ast_driver paren_roundtrip

test: ast_driver paren_roundtrip
	../../.venv/bin/python3 -m pytest .

Voblint_CLI.ml: ../../codegen/generated/ml/Voblint_CLI.ml
	cp $< $@

vimp_parser.mly: ../../cli/vimp_parser.mly
	cp $< $@

vimp_lexer.mll: ../../cli/vimp_lexer.mll
	cp $< $@

vimp_frontend.ml: ../../cli/vimp_frontend.ml
	cp $< $@

vimp_parser.ml vimp_parser.mli: vimp_parser.mly
	menhir vimp_parser.mly

vimp_lexer.ml: vimp_lexer.mll
	ocamllex vimp_lexer.mll

ast_driver: Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml vimp_frontend.ml ast_driver.ml
	ocamlfind ocamlopt -package str,zarith -linkpkg \
	  Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml vimp_frontend.ml ast_driver.ml -o ast_driver

paren_roundtrip: Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml paren_roundtrip.ml
	ocamlfind ocamlopt -package str,zarith -linkpkg \
	  Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml paren_roundtrip.ml -o paren_roundtrip

clean:
	rm -f ast_driver paren_roundtrip Voblint_CLI.ml vimp_parser.ml vimp_parser.mli vimp_parser.automaton \
	  vimp_parser.conflicts vimp_parser.mly vimp_lexer.ml vimp_lexer.mll vimp_frontend.ml *.cmi *.cmx *.o
