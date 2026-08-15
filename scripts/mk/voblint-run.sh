#!/usr/bin/env bash
# Wraps cli/voblint for the `voblint` pixi task: runs the analysis
# regardless of a stale codegen/generated/ (cli-build.sh's own mismatch
# warning stays non-fatal there by design -- see its header -- because
# cli-test and cli-smoke also depend on cli-build and shouldn't be blocked
# by it), but fails `pixi run voblint` afterward if generated/ was stale,
# so the analysis output stays visible while the mismatch is still
# CI-visible. Preserves a genuine analysis failure exit code over the
# staleness one.
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

stamp="$REPO_ROOT/codegen/generated/.source-hash"
current_hash="$("$SCRIPT_DIR/codegen-hash.sh")"
source_mismatch=0
if [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$current_hash" ]; then
  source_mismatch=1
fi

"$REPO_ROOT/cli/voblint" "$@"
analysis_status=$?

if [ "$analysis_status" -ne 0 ]; then
  exit "$analysis_status"
fi

exit "$source_mismatch"
