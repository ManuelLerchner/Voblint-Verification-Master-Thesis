#!/usr/bin/env bash
# Emit an HTML result directory with `voblint --html` and serve it, for the
# `report` pixi task.
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
OUTDIR="${OUTDIR:-$REPO_ROOT/result}"

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

rm -rf "$OUTDIR"
"$REPO_ROOT/cli/voblint" --analysis "$analysis" --html-out "$OUTDIR" "$source_file"

url="http://localhost:$PORT/index.xml"

# Open the report once the server is actually accepting connections. Backgrounded
# because the server below never returns. NO_OPEN=1 skips it, as does a headless
# box with neither opener installed.
if [ -z "${NO_OPEN:-}" ]; then
  opener=""
  command -v open >/dev/null 2>&1 && opener="open"
  [ -z "$opener" ] && command -v xdg-open >/dev/null 2>&1 && opener="xdg-open"
  if [ -n "$opener" ]; then
    (
      for _ in $(seq 40); do
        if curl -s -o /dev/null --max-time 1 "$url"; then break; fi
        sleep 0.25
      done
      "$opener" "$url" >/dev/null 2>&1 || true
    ) &
  fi
fi

echo
echo "Serving $OUTDIR on $url  (Ctrl-C to stop)"
echo
exec python3 -m http.server --directory "$OUTDIR" "$PORT"
