#!/usr/bin/env bash
# Build the top-level session (incremental; requires `pixi run vendor` and
# bootstrap heaps to already exist).
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

SESSION="${SESSION:-Voblint_Examples}"
"$ISABELLE" build -v -j2 -o threads=6 -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" "$SESSION"
