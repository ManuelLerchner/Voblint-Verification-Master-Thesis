#!/usr/bin/env bash
# Build the thesis with its changes since origin/main marked in place, as
# latexdiff does for LaTeX: added words blue and underlined, removed words red
# and struck through. A copy of thesis/ gets every changed chapter replaced by
# typdiff's markup of the old and new source, then compiles like the thesis.
# The comparison starts at the merge base, as typst-diff.sh does.
#
#   typst-redline.sh [base-rev] [out.pdf]     (base-rev defaults to origin/main)
set -euo pipefail

BASE_REF="${1:-origin/main}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OUT="${2:-$REPO_ROOT/build/thesis-redline.pdf}"
WORK="$REPO_ROOT/build/thesis-redline"
cd "$REPO_ROOT"

BASE="$(git merge-base "$BASE_REF" HEAD)"

rm -rf "$WORK"
mkdir -p "$WORK" "$(dirname "$OUT")"
# The working tree, generated data included, so the copy builds like thesis/.
rsync -a --exclude '*.pdf' thesis/ "$WORK/"

count=0
while IFS= read -r file; do
  rel="${file#thesis/}"
  # A new chapter has nothing to compare with and stays as it is.
  old="$(mktemp)"
  if git show "$BASE:$file" > "$old" 2> /dev/null; then
    typdiff "$old" "$file" -o "$WORK/$rel"
    count=$((count + 1))
  fi
  rm -f "$old"
done < <(git diff --name-only --no-renames --diff-filter=M "$BASE" HEAD -- 'thesis/*.typ')

set --
[ -n "${SITE_URL:-}" ] && set -- --input "site-url=${SITE_URL%/}/"
log="$(mktemp)"
trap 'rm -f "$log"' EXIT

# typdiff reprints a whole file and can break markup it did not change. A file
# whose marked copy fails to compile falls back to its plain new source, so one
# such file costs its own marks, not the whole document.
unmarked=()
while ! typst compile --root "$WORK" --font-path "$WORK/assets/fonts" "$@" \
  "$WORK/thesis.typ" "$OUT" 2> "$log"; do
  broken="$(sed -n "s|.*─ ${WORK#"$REPO_ROOT"/}/\(.*\.typ\):.*|\1|p" "$log" | head -n 1)"
  if [ -z "$broken" ] || [ ! -f "thesis/$broken" ] || cmp -s "thesis/$broken" "$WORK/$broken"; then
    cat "$log" >&2
    exit 1
  fi
  cp "thesis/$broken" "$WORK/$broken"
  unmarked+=("$broken")
done

echo "typst-redline: $((count - ${#unmarked[@]})) file(s) marked -> $OUT"
if [ "${#unmarked[@]}" -gt 0 ]; then
  echo "typst-redline: typdiff output did not compile, shown unmarked: ${unmarked[*]}"
fi
