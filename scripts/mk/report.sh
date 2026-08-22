#!/usr/bin/env bash
# Emit an HTML result directory and serve it, for the `report` pixi task.
#
# Goblint's frontend needs a web server: browsers refuse the cross-document
# loads it performs over file://. This mirrors what Goblint's own docs tell
# users to run, down to the port.
#
# The g2html submodule is initialized here rather than in vendor.sh, so the
# Isabelle build and codegen never fetch a frontend they don't use.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

DEMO="tests/regression/16-composite-domain/precision/01-refinement_beats_components.vimp"
PORT="${PORT:-8080}"
OUTDIR="$REPO_ROOT/result"

source_file="${1:-$REPO_ROOT/$DEMO}"
analysis="${2:-int}"

test -e "$REPO_ROOT/vendor/g2html/.git" \
  || git -C "$REPO_ROOT" submodule update --init vendor/g2html

# conda-forge's graphviz registers its renderer plugins from a post-link
# script, which pixi skips unless run-post-link-scripts is enabled. Without
# that registry `dot -Tsvg` fails with 'Format: "svg" not recognized'. `dot -c`
# rebuilds it in the active prefix and is idempotent, so probe first and only
# pay for it on a prefix that needs it -- a system graphviz already works and
# is left alone.
if ! printf 'digraph{a}' | dot -Tsvg >/dev/null 2>&1; then
  dot -c >/dev/null 2>&1 || true
fi

python3 "$REPO_ROOT/scripts/emit_html_report.py" \
  --analysis "$analysis" "$source_file" "$OUTDIR"

echo
echo "Serving $OUTDIR on http://localhost:$PORT/index.xml  (Ctrl-C to stop)"
echo
exec python3 -m http.server --directory "$OUTDIR" "$PORT"
