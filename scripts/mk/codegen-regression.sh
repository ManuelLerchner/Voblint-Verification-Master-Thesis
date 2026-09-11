#!/usr/bin/env bash
# Compile and run the hand-written OCaml driver under codegen/regression/
# against the tracked codegen/generated/ sources, and check its output
# against the values already proved by
# src/Examples/CLI/Example_Analysis_Dispatch_Regression.thy's
# dispatch_demo_* lemmas.
# Requires dune and the zarith package (Code_Target_Numeral backs int/nat by
# Zarith's Z.t on the OCaml side) on PATH; does not require Isabelle.
set -euo pipefail

if [ "${VOBLINT_OPAM_EXEC:-0}" != "1" ] && command -v opam >/dev/null 2>&1; then
  exec env VOBLINT_OPAM_EXEC=1 opam exec -- "$0" "$@"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT/codegen/regression/ocaml"
dune build ./main.exe
cp "$REPO_ROOT/_build/default/codegen/regression/ocaml/main.exe" regression-ml
./regression-ml
