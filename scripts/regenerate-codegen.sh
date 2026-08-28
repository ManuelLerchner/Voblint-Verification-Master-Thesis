#!/bin/sh
# Regenerates codegen/generated/ from the export_files declarations in
# src/Codegen/ROOT. Do not hand-edit files
# under codegen/generated/ -- rerun this script instead.
set -eu

cd "$(dirname "$0")/.."

AFP="${AFP:-$HOME/afp/thys}"
TD_DIR="vendor/td-verification"
ISABELLE="${ISABELLE:-isabelle}"

# -d for the repository root, not -D: -D would *select* every session it
# finds there, which pulls Voblint_Examples into a run that only needs
# Voblint_Codegen. The two are siblings on Voblint_CLI (neither imports the
# other), so building Examples here contributes nothing to the exported code
# and costs several minutes on every regeneration -- including every CLI-only
# change, since Examples sits downstream of Voblint_CLI too. Naming
# Voblint_Codegen alone still builds its own dependency chain
# (Core -> Analysis -> Formalization -> CLI -> Codegen); it just stops there.
#
# The session is built before codegen/generated is cleared, so a failing
# build leaves the previous output in place instead of destroying it and
# stranding the tree with neither a fresh nor a stale export.
"$ISABELLE" build -v -j12 -o threads=12 -d "$AFP" -d "$TD_DIR" -d . Voblint_Codegen

rm -rf codegen/generated
mkdir -p codegen/generated

# -e materializes the session's export_files declarations (ROOT) onto the
# file system. The session is already up to date from the build above, so
# this invocation only writes out the exports.
"$ISABELLE" build -j12 -o threads=12 -e -d "$AFP" -d "$TD_DIR" -d . Voblint_Codegen

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
