#!/usr/bin/env bash
# Compile the browser adapter and generated analyzer export to WebAssembly.
set -euo pipefail

if [ "${VOBLINT_OPAM_EXEC:-0}" != "1" ] && command -v opam >/dev/null 2>&1; then
  exec env VOBLINT_OPAM_EXEC=1 opam exec -- /bin/bash "$0" "$@"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT"
dune build cli/browser_main.bc.wasm.js

OUT="$REPO_ROOT/build/browser"
GENERATED="$REPO_ROOT/_build/default/cli"

rm -rf "$OUT"
mkdir -p "$OUT"

cp \
  "$GENERATED/browser_main.bc.wasm.js" \
  "$OUT/browser_main.bc.wasm.js"

cp -R \
  "$GENERATED/browser_main.bc.wasm.assets" \
  "$OUT/browser_main.bc.wasm.assets"

echo "Browser analyzer:"
echo "  $OUT/browser_main.bc.wasm.js"
echo "  $OUT/browser_main.bc.wasm.assets/"