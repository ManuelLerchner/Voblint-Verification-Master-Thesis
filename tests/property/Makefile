# Property-test AST<->printer oracle driver. Test-only; not part of the
# shipped voblint CLI. Copies the same Voblint_CLI.ml / vimp_lexer.ml /
# vimp_parser.ml sources ../../cli (the main CLI) builds from, so ocamlopt's
# .cmi/.cmx build byproducts land here rather than polluting ../../cli.

.PHONY: all clean

all: ast_driver

Voblint_CLI.ml: ../../codegen/generated/ml/Voblint_CLI.ml
	cp $< $@

vimp_lexer.ml: ../../cli/vimp_lexer.ml
	cp $< $@

vimp_parser.ml: ../../cli/vimp_parser.ml
	cp $< $@

ast_driver: Voblint_CLI.ml vimp_lexer.ml vimp_parser.ml ast_driver.ml
	ocamlfind ocamlopt -package str,zarith -linkpkg \
	  Voblint_CLI.ml vimp_lexer.ml vimp_parser.ml ast_driver.ml -o ast_driver

clean:
	rm -f ast_driver Voblint_CLI.ml vimp_lexer.ml vimp_parser.ml *.cmi *.cmx *.o
