#!/bin/sh
# Regenerates codegen/generated/ from the export_files declarations in
# src/Codegen/ROOT. Do not hand-edit files
# under codegen/generated/ -- rerun this script instead.
set -eu

cd "$(dirname "$0")/.."

AFP="${AFP:-$HOME/afp/thys}"
TD_DIR="vendor/td-verification"
ISABELLE="${ISABELLE:-isabelle}"

rm -rf codegen/generated
mkdir -p codegen/generated

# -e materializes the session's export_files declarations (ROOT) onto the
# file system; -N builds a fresh log per session; the session itself is
# rebuilt (or reused, if already up to date) as part of the same invocation.
"$ISABELLE" build -v -j12 -o threads=12 -N -e -d "$AFP" -d "$TD_DIR" -D . Voblint_Codegen

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

# Stamp what source state produced this output -- cli-build.sh compares
# against it so a .thy fix that never got regenerated fails loudly instead
# of silently compile-testing stale generated code (see codegen-hash.sh).
"$(dirname "$0")/mk/codegen-hash.sh" >codegen/generated/.source-hash

echo "Regenerated codegen/generated/:"
find codegen/generated -type f
