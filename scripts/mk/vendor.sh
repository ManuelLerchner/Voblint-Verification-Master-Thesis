#!/usr/bin/env bash
# Initialize the td-verification submodule (pinned via the superproject
# gitlink) and apply vendor/td-verification.patch on top. Idempotent: a
# second run neither re-applies an already-applied patch nor fails.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TD_DIR="$REPO_ROOT/vendor/td-verification"
TD_PATCH="$REPO_ROOT/vendor/td-verification.patch"

test -e "$TD_DIR/.git" || git submodule update --init "$TD_DIR"

if [[ -s "$TD_PATCH" ]]; then
  if git -C "$TD_DIR" apply --check "$TD_PATCH" 2>/dev/null; then
    git -C "$TD_DIR" apply "$TD_PATCH"
    echo "Applied $TD_PATCH."
  elif git -C "$TD_DIR" apply --check --reverse "$TD_PATCH" 2>/dev/null; then
    : # already applied
  else
    echo "ERROR: $TD_PATCH does not apply cleanly to $TD_DIR." >&2
    exit 1
  fi
fi
