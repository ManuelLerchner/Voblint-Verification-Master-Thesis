#!/usr/bin/env bash
# HTML browser info for all session theories (see Isabelle System Manual,
# browser_info). Output is copied to docs/html/ for a repo-local entry
# point; Isabelle also keeps a copy under ISABELLE_HOME_USER/browser_info/.
# See https://stackoverflow.com/questions/17833567/
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

HTML_DIR="$REPO_ROOT/docs/html"
SESSIONS="Voblint_VIMP Voblint_CFG Voblint_Core Voblint_Analysis Voblint_Formalization Voblint_Examples"
ISABELLE_HOME_USER="${ISABELLE_HOME_USER:-$("$ISABELLE" getenv -b ISABELLE_HOME_USER 2>/dev/null)}"
test -n "$ISABELLE_HOME_USER" || { echo "ERROR: could not resolve ISABELLE_HOME_USER." >&2; exit 1; }

# Clean build (-c) so every session is rebuilt and therefore presented.
# Isabelle emits HTML only for sessions it actually builds; -o browser_info
# on warm heaps would skip up-to-date ancestors (and re-presenting them
# collides on the isabelle_sources PRIMARY KEY). In fresh CI -c is a no-op.
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" -o browser_info -c $SESSIONS
rm -rf "$HTML_DIR"
mkdir -p "$HTML_DIR"
cp -R "$ISABELLE_HOME_USER/browser_info/." "$HTML_DIR/"
touch "$HTML_DIR/.nojekyll"
echo "Open $HTML_DIR/Unsorted/Voblint_Examples/index.html"
