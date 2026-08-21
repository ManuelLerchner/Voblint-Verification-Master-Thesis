#!/usr/bin/env bash
# Property-test AST<->printer oracle driver build. Test-only; not part of
# the shipped voblint CLI. Copies the same Voblint_CLI.ml / vimp_parser.mly
# / vimp_lexer.mll / vimp_frontend.ml sources cli/ (the main CLI) builds
# from, so ocamlopt's .cmi/.cmx build byproducts land here rather than
# polluting cli/, and menhir/ocamllex run on local copies.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
PROP_DIR="$REPO_ROOT/tests/property"

cp "$REPO_ROOT/codegen/generated/ml/Voblint_CLI.ml" "$PROP_DIR/Voblint_CLI.ml"
cp "$REPO_ROOT/cli/vimp_parser.mly" "$PROP_DIR/vimp_parser.mly"
cp "$REPO_ROOT/cli/vimp_lexer.mll" "$PROP_DIR/vimp_lexer.mll"
cp "$REPO_ROOT/cli/vimp_frontend.ml" "$PROP_DIR/vimp_frontend.ml"

cd "$PROP_DIR"
menhir vimp_parser.mly
ocamllex vimp_lexer.mll
ocamlfind ocamlopt -package str,zarith -linkpkg \
  Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml vimp_frontend.ml ast_driver.ml -o ast_driver
