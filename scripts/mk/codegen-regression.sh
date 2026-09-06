#!/usr/bin/env bash
# Compile and run the hand-written OCaml driver under codegen/regression/
# against the tracked codegen/generated/ sources, and check its output
# against the values already proved by
# src/Examples/CLI/Example_Analysis_Dispatch_Regression.thy's
# dispatch_demo_* lemmas.
# Requires ocamlfind (+ the zarith package -- Code_Target_Numeral backs
# int/nat by Zarith's Z.t on the OCaml side) on PATH; does not require
# Isabelle.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT/codegen/regression/ocaml"
cp ../../generated/ml/Voblint_CLI.ml ./Voblint_CLI.ml
# The two files are compiled separately so they can carry different warning
# settings. -8/-11/-20 are routine artifacts of Isabelle's OCaml serializer
# (partial matches Isabelle's own type discipline already rules out, e.g. Set's
# unreachable Coset case; unused dictionary-passing arguments) and are silenced
# for the generated file only. main.ml keeps -8: a renderer that stops covering
# every constructor of a generated datatype is exactly the drift this harness
# exists to catch, and silencing it there once turned a compile error into a
# runtime "Pattern matching failed". -warn-error +8 makes that a build failure.
ocamlfind ocamlopt -w -8-11-20 -package str,zarith -c Voblint_CLI.ml
ocamlfind ocamlopt -w -11-20 -warn-error +8 -package str,zarith -linkpkg Voblint_CLI.cmx main.ml -o regression-ml
./regression-ml
