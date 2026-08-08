#!/bin/sh
# Regenerates codegen/generated/ from the export_files declarations in
# src/Examples/ROOT (which mirror the export_code declarations in
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

# Isabelle's OCaml backend always names its export blob with a ".ocaml"
# extension (fixed by the code generator, not by file_prefix), which is why
# ROOT's export_files pattern for it is "code/*.ocaml" -- that pattern is
# matched against Isabelle's own export name, not a free-form rename target.
# Renaming the materialized file to ".ml" here is a purely cosmetic, purely
# on-disk rename after the fact; codegen-check's git diff only ever compares
# this script's own output against itself, so it stays deterministic.
for f in codegen/generated/ml/*.ocaml; do
  [ -e "$f" ] || continue
  mv "$f" "${f%.ocaml}.ml"
done

echo "Regenerated codegen/generated/:"
find codegen/generated -type f
