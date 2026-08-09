# voblint CLI: a thin, unverified adapter over the Isabelle-generated
# Voblint_CLI OCaml module (src/Examples/Tooling/Example_State_Report_GraphViz.thy's
# export_code block). The frontend (vimp_parser.mly, vimp_lexer.mll) is
# generated from grammar/vimp.yaml by scripts/gen_vimp_menhir.py and
# committed, the same convention codegen/generated/ uses for Isabelle output
# -- `make` needs only ocamlfind + zarith + menhir + ocamllex on PATH, not
# Python/PyYAML/Isabelle; regenerating the frontend (only needed if
# grammar/vimp.yaml changed) is the separate `make generate`.

.PHONY: all generate clean test

all: voblint

generate:
	cd .. && .pixi/envs/default/bin/python3 scripts/gen_vimp_menhir.py

test: voblint
	python3 ../tests/run.py

# Copied in (not symlinked) so ocamlopt can infer the module name
# "Voblint_CLI" from the filename, matching codegen/regression/ocaml's own
# convention. Do not hand-edit the copy; rerun `make -C .. codegen` and
# `make` here instead.
Voblint_CLI.ml: ../codegen/generated/ml/Voblint_CLI.ml
	cp $< $@

vimp_parser.ml vimp_parser.mli: vimp_parser.mly
	menhir vimp_parser.mly

vimp_lexer.ml: vimp_lexer.mll
	ocamllex vimp_lexer.mll

voblint: Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml vimp_frontend.ml main.ml
	ocamlfind ocamlopt -package str,zarith,unix -linkpkg \
	  Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml vimp_frontend.ml main.ml -o voblint

clean:
	rm -f voblint Voblint_CLI.ml vimp_parser.ml vimp_parser.mli vimp_parser.automaton vimp_parser.conflicts \
	  vimp_lexer.ml *.cmi *.cmx *.o
