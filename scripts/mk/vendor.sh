#!/usr/bin/env bash
# Initialize the td-verification submodule, pinned via the superproject
# gitlink. Idempotent: a second run is a no-op.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TD_DIR="$REPO_ROOT/vendor/td-verification"

test -e "$TD_DIR/.git" || git submodule update --init "$TD_DIR"
