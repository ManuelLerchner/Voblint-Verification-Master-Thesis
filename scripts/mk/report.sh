#!/usr/bin/env bash
# Serve an existing HTML result directory for the
# `html-report-serve` pixi task.
#
# Goblint's frontend needs a web server: browsers refuse the cross-document
# loads it performs over file://. This mirrors what Goblint's own docs tell
# users to run, down to the port.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

if [ "$#" -gt 1 ]; then
  echo "Usage: pixi run html-report-serve [REPORT_DIR]" >&2
  exit 1
fi

PORT="${PORT:-8080}"
OUTDIR="${1:-${OUTDIR:-$REPO_ROOT/build/report}}"

if [ ! -f "$OUTDIR/index.xml" ]; then
  echo "No report at $OUTDIR/index.xml. Generate one with voblint --html first." >&2
  exit 1
fi

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
