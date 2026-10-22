#!/usr/bin/env bash
# Render the source changes to the Typst files since origin/main as one PDF,
# one side-by-side diffst table per changed file, for reviewing a branch without
# reading the raw diff. The comparison starts at the merge base, so commits that
# reached main after the branch left it do not show as reverted.
#
#   typst-diff.sh [base-rev] [out.pdf]     (base-rev defaults to origin/main)
#
# Only .typ sources are compared: generated data and figures change with them
# but are not prose a reviewer reads.
set -euo pipefail

BASE_REF="${1:-origin/main}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OUT="${2:-$REPO_ROOT/build/thesis-diff.pdf}"
WORK="$REPO_ROOT/build/thesis-diff"
cd "$REPO_ROOT"

BASE="$(git merge-base "$BASE_REF" HEAD)"
base_short="$(git rev-parse --short "$BASE")"
head_short="$(git rev-parse --short HEAD)"

rm -rf "$WORK"
mkdir -p "$WORK/old" "$WORK/new" "$(dirname "$OUT")"

# Typst string literal: only the backslash and the quote need escaping.
typst_str() {
  local s="${1//\\/\\\\}"
  printf '"%s"' "${s//\"/\\\"}"
}

doc="$WORK/diff.typ"
{
  echo '#import "@preview/diffst:0.1.0": diffst'
  echo '#set page(paper: "a4", flipped: true, margin: 1.2cm, numbering: "1")'
  echo '#set text(size: 8pt)'
  echo '#set heading(numbering: none)'
  printf '= Typst changes from %s (%s) to %s\n\n' "$BASE_REF" "$base_short" "$head_short"
} > "$doc"

count=0
# Committed changes only, renames as a removal and an addition.
while IFS= read -r file; do
  count=$((count + 1))
  mkdir -p "$WORK/old/$(dirname "$file")" "$WORK/new/$(dirname "$file")"
  # A file added or deleted is compared with an empty one.
  git show "$BASE:$file" > "$WORK/old/$file" 2> /dev/null || : > "$WORK/old/$file"
  git show "HEAD:$file" > "$WORK/new/$file" 2> /dev/null || : > "$WORK/new/$file"
  {
    printf '== #raw(%s)\n\n' "$(typst_str "$file")"
    printf '#diffst(path(%s), path(%s), old-label: %s, new-label: %s)\n\n' \
      "$(typst_str "old/$file")" "$(typst_str "new/$file")" \
      "$(typst_str "$base_short")" "$(typst_str "$head_short")"
  } >> "$doc"
done < <(git diff --name-only --no-renames "$BASE" HEAD -- '*.typ')

if [ "$count" -eq 0 ]; then
  echo 'No Typst source changed.' >> "$doc"
else
  # The outline goes after the title, once the sections exist.
  sed -i.bak '/^= Typst changes/a\
#outline(title: none, depth: 2)
' "$doc" && rm -f "$doc.bak"
fi

typst compile --root "$WORK" "$doc" "$OUT"
echo "typst-diff: $count file(s) -> $OUT"
