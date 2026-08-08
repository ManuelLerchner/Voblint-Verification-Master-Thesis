#!/bin/sh
# Regenerates codegen/generated/ from the Isabelle export_code declarations in
# src/Examples/{Sign,Interval}/Exec_*.thy. Do not hand-edit files under
# codegen/generated/ -- rerun this script instead.
set -eu

cd "$(dirname "$0")/.."

AFP="${AFP:-$HOME/afp/thys}"
TD_DIR="vendor/td-verification"

isabelle build -v -j12 -o threads=12 -N -d "$AFP" -d "$TD_DIR" -D . Voblint_Examples

rm -rf codegen/generated
mkdir -p codegen/generated
isabelle export \
  -d "$AFP" -d "$TD_DIR" -d . \
  -O codegen/generated -p 3 \
  -x 'Voblint_Examples.Exec_Sign_DG_Run:code/**' \
  -x 'Voblint_Examples.Exec_Ivl_Run:code/**' \
  Voblint_Examples

echo "Regenerated codegen/generated/:"
find codegen/generated -type f
