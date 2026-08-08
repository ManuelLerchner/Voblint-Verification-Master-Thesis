#!/bin/sh
# Regenerates codegen/generated/ from the Isabelle export_code declarations in
# src/Examples/Sign/Example_Sign_Codegen.thy,
# src/Examples/Interval/Exec_Ivl_Run.thy, and
# src/Examples/Mixed/Example_Analysis_Dispatch.thy. Do not hand-edit files
# under codegen/generated/ -- rerun this script instead.
set -eu

cd "$(dirname "$0")/.."

AFP="${AFP:-$HOME/afp/thys}"
TD_DIR="vendor/td-verification"

isabelle build -v -j12 -o threads=12 -N -d "$AFP" -d "$TD_DIR" -D . Voblint_Examples

rm -rf codegen/generated
mkdir -p codegen/generated

# Haskell exports nest one level deeper (code/<module>/<module>.hs) than
# OCaml (code/<file_prefix>.ocaml), so they need different -p prune counts.
isabelle export \
  -d "$AFP" -d "$TD_DIR" -d . \
  -O codegen/generated -p 3 \
  -x 'Voblint_Examples.Example_Sign_Codegen:code/*/*.hs' \
  -x 'Voblint_Examples.Exec_Ivl_Run:code/*/*.hs' \
  -x 'Voblint_Examples.Example_Analysis_Dispatch:code/*/*.hs' \
  Voblint_Examples

isabelle export \
  -d "$AFP" -d "$TD_DIR" -d . \
  -O codegen/generated -p 2 \
  -x 'Voblint_Examples.Example_Sign_Codegen:code/*.ocaml' \
  -x 'Voblint_Examples.Exec_Ivl_Run:code/*.ocaml' \
  -x 'Voblint_Examples.Example_Analysis_Dispatch:code/*.ocaml' \
  Voblint_Examples

echo "Regenerated codegen/generated/:"
find codegen/generated -type f
