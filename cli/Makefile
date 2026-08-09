# voblint CLI: a thin, unverified parser/adapter over the Isabelle-generated
# Voblint_CLI OCaml module (src/Examples/Tooling/Example_State_Report_GraphViz.thy's
# export_code block). Requires ocamlfind + the zarith package on PATH, same
# as codegen/regression/ocaml; does not require Isabelle to build (only to
# regenerate ../codegen/generated/ml/Voblint_CLI.ml via `make -C .. codegen`).

.PHONY: all clean test

all: voblint

test: voblint
	python3 ../tests/run.py

# Copied in (not symlinked) so ocamlopt can infer the module name
# "Voblint_CLI" from the filename, matching codegen/regression/ocaml's own
# convention. Do not hand-edit the copy; rerun `make -C .. codegen` and
# `make` here instead.
Voblint_CLI.ml: ../codegen/generated/ml/Voblint_CLI.ml
	cp $< $@

voblint: Voblint_CLI.ml vimp_lexer.ml vimp_parser.ml main.ml
	ocamlfind ocamlopt -package str,zarith,unix -linkpkg \
	  Voblint_CLI.ml vimp_lexer.ml vimp_parser.ml main.ml -o voblint

clean:
	rm -f voblint Voblint_CLI.ml *.cmi *.cmx *.o
