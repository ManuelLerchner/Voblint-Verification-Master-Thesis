#!/usr/bin/env bash
# Compile the browser adapter and generated analyzer export to JavaScript.
set -euo pipefail

if [ "${VOBLINT_OPAM_EXEC:-0}" != "1" ] && command -v opam >/dev/null 2>&1; then
  exec env VOBLINT_OPAM_EXEC=1 opam exec -- /bin/bash "$0" "$@"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT"
dune build cli/browser_main.bc.js
mkdir -p build/browser
cp _build/default/cli/browser_main.bc.js build/browser/voblint.js
echo "Browser analyzer: $REPO_ROOT/build/browser/voblint.js"