#!/bin/sh
# Regenerates codegen/generated/ from the export_files declarations in
# src/Examples/ROOT (which mirror the export_code declarations in
# src/Examples/Sign/Example_Sign_Codegen.thy,
# src/Examples/Interval/Exec_Ivl_Run.thy, and
# src/Examples/Mixed/Example_Analysis_Dispatch.thy). Do not hand-edit files
# under codegen/generated/ -- rerun this script instead.
set -eu

cd "$(dirname "$0")/.."

AFP="${AFP:-$HOME/afp/thys}"
TD_DIR="vendor/td-verification"

rm -rf codegen/generated
mkdir -p codegen/generated

# -e materializes the session's export_files declarations (ROOT) onto the
# file system; -N builds a fresh log per session; the session itself is
# rebuilt (or reused, if already up to date) as part of the same invocation.
isabelle build -v -j12 -o threads=12 -N -e -d "$AFP" -d "$TD_DIR" -D . Voblint_Examples

echo "Regenerated codegen/generated/:"
find codegen/generated -type f
