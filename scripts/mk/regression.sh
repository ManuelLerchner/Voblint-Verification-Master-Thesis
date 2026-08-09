#!/usr/bin/env bash
# Compile and run the hand-written Haskell/OCaml drivers under
# codegen/regression/ against the tracked codegen/generated/ sources, and
# check their output against the values already proved by
# src/Examples/Mixed/Example_Analysis_Dispatch.thy's dispatch_demo_* lemmas.
# Requires ghc and ocamlfind (+ the zarith package -- Code_Target_Numeral
# backs int/nat by Zarith's Z.t on the OCaml side) on PATH; does not require
# Isabelle.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT/codegen/regression/haskell"
ghc -i../../generated/hs -o regression-hs Main.hs
./regression-hs

cd "$REPO_ROOT/codegen/regression/ocaml"
cp ../../generated/ml/Voblint_Analyse_OCaml.ml ./Voblint_Analyse_OCaml.ml
ocamlfind ocamlopt -package str,zarith -linkpkg Voblint_Analyse_OCaml.ml main.ml -o regression-ml
./regression-ml
