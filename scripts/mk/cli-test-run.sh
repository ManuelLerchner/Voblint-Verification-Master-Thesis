#!/usr/bin/env bash
# Wraps tests/run.py for the `cli-test` pixi task: runs the regression
# suite regardless of a stale codegen/generated/ (cli-build.sh's own
# mismatch warning stays non-fatal there by design -- see its header --
# because cli-smoke and voblint also depend on cli-build and shouldn't be
# blocked by it), but fails `pixi run cli-test` afterward if generated/ was
# stale, so the suite's output stays visible while the mismatch is still
# CI-visible (cli-test is one of the `ci` task's dependencies). Preserves a
# genuine test failure exit code over the staleness one.
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

stamp="$REPO_ROOT/codegen/generated/.source-hash"
current_hash="$("$SCRIPT_DIR/codegen-hash.sh")"
source_mismatch=0
if [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$current_hash" ]; then
  source_mismatch=1
fi

python3 "$REPO_ROOT/tests/run.py" "$@"
test_status=$?

if [ "$test_status" -ne 0 ]; then
  exit "$test_status"
fi

exit "$source_mismatch"
