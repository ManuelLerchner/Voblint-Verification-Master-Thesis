#!/usr/bin/env bash
# Property-test AST<->printer oracle driver build. Test-only; not part of
# the shipped voblint CLI. Copies the same Voblint_CLI.ml / vimp_parser.mly
# / vimp_lexer.mll / vimp_frontend.ml sources cli/ (the main CLI) builds
# from. Dune keeps compiler byproducts under `_build/`.
set -euo pipefail

if [ "${VOBLINT_OPAM_EXEC:-0}" != "1" ] && command -v opam >/dev/null 2>&1; then
  exec env VOBLINT_OPAM_EXEC=1 opam exec -- "$0" "$@"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
PROP_DIR="$REPO_ROOT/tests/property"

cd "$PROP_DIR"
rm -f vimp_parser.ml vimp_parser.mli vimp_lexer.ml
dune build ./ast_driver.exe
cp "$REPO_ROOT/_build/default/tests/property/ast_driver.exe" ast_driver
