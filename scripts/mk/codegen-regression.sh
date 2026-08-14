#!/usr/bin/env bash
# Compile and run the hand-written OCaml driver under codegen/regression/
# against the tracked codegen/generated/ sources, and check its output
# against the values already proved by
# src/Examples/Regression/Example_Analysis_Dispatch_Regression.thy's
# dispatch_demo_* lemmas.
# Requires ocamlfind (+ the zarith package -- Code_Target_Numeral backs
# int/nat by Zarith's Z.t on the OCaml side) on PATH; does not require
# Isabelle.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT/codegen/regression/ocaml"
cp ../../generated/ml/Voblint_Analyse_OCaml.ml ./Voblint_Analyse_OCaml.ml
# -8/-11/-20: routine artifacts of Isabelle's OCaml serializer (partial
# matches Isabelle's own type discipline already rules out, e.g. Set's
# unreachable Coset case here; unused dictionary-passing arguments), not
# signs of a real problem in the generated code.
ocamlfind ocamlopt -w -8-11-20 -package str,zarith -linkpkg Voblint_Analyse_OCaml.ml main.ml -o regression-ml
./regression-ml
