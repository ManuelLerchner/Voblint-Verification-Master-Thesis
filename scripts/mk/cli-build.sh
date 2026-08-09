#!/usr/bin/env bash
# Builds the voblint CLI: a thin, unverified adapter over the
# Isabelle-generated Voblint_CLI OCaml module
# (src/Examples/Tooling/Example_State_Report_GraphViz.thy's export_code
# block), plus the Menhir/ocamllex frontend generated from
# grammar/vimp.yaml (scripts/gen_vimp_menhir.py; only needed if that
# changed -- cli/vimp_parser.mly and cli/vimp_lexer.mll are committed).
# Requires ocamlfind + menhir + ocamllex + the zarith/unix findlib packages
# on PATH; does not require Isabelle or Python to build.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CLI_DIR="$REPO_ROOT/cli"

# Copied in (not symlinked) so ocamlopt can infer the module name
# "Voblint_CLI" from the filename, matching codegen/regression/ocaml's own
# convention. Do not hand-edit the copy; rerun `pixi run codegen` and this
# script instead.
cp "$REPO_ROOT/codegen/generated/ml/Voblint_CLI.ml" "$CLI_DIR/Voblint_CLI.ml"

cd "$CLI_DIR"
menhir vimp_parser.mly
ocamllex vimp_lexer.mll
ocamlfind ocamlopt -package str,zarith,unix -linkpkg \
  Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml vimp_frontend.ml main.ml -o voblint
