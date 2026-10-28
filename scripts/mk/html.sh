#!/usr/bin/env bash
# HTML browser info for all session theories (see Isabelle System Manual,
# browser_info). Output is copied to build/isabelle-html/ for a repo-local entry
# point; Isabelle also keeps a copy under ISABELLE_HOME_USER/browser_info/.
# See https://stackoverflow.com/questions/17833567/
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

HTML_DIR="$REPO_ROOT/build/isabelle-html"
read -ra SESSIONS <<<"$(bash "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/sessions.sh" | tr '\n' ' ')"
ISABELLE_HOME_USER="${ISABELLE_HOME_USER:-$("$ISABELLE" getenv -b ISABELLE_HOME_USER 2>/dev/null)}"
test -n "$ISABELLE_HOME_USER" || { echo "ERROR: could not resolve ISABELLE_HOME_USER." >&2; exit 1; }

# Clean build (-c) so every session is rebuilt and therefore presented.
# Isabelle emits HTML only for sessions it actually builds; -o browser_info
# on warm heaps would skip up-to-date ancestors (and re-presenting them
# collides on the isabelle_sources PRIMARY KEY). In fresh CI -c is a no-op.
"$ISABELLE" build -v -j2 -o threads=12 -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" -o browser_info -c "${SESSIONS[@]}"
rm -rf "$HTML_DIR"
mkdir -p "$HTML_DIR"
cp -R "$ISABELLE_HOME_USER/browser_info/." "$HTML_DIR/"
# Keep the interactive map with the HTML artifact: Pages needs no Isabelle runtime.
bash "$REPO_ROOT/scripts/mk/entity-deps.sh"
python3 "$REPO_ROOT/scripts/pages_proof_map.py" --html "$HTML_DIR" --out "$HTML_DIR/assets/proof-map.json"
touch "$HTML_DIR/.nojekyll"
echo "Open $HTML_DIR/Voblint/Voblint_Examples/index.html"
