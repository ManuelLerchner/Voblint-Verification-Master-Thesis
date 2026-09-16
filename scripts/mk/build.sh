#!/usr/bin/env bash
# Build the top-level session (incremental; requires `pixi run vendor-init` and
# bootstrap heaps to already exist).
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

SESSION="${SESSION:-Voblint_Examples}"

# Tee the -v output: check_build_reelaboration.py reads the per-theory lines to
# see which library heaps a session inherited and which it re-elaborated, and
# that is only visible in a build log. pipefail keeps the build's exit status.
LOG="${BUILD_LOG:-$REPO_ROOT/build/isabelle-build.log}"
mkdir -p "$(dirname "$LOG")"
set -o pipefail
"$ISABELLE" build -v -j2 -o threads=12 -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" "$SESSION" \
  2>&1 | tee "$LOG"
