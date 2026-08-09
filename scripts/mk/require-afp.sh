#!/usr/bin/env bash
# Sourced (not executed) by the other scripts/mk/*.sh to resolve and check
# ISABELLE/AFP with the same defaults and error message the old Makefile
# used. Sets ISABELLE, AFP, REPO_ROOT, TD_DIR in the caller's shell.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TD_DIR="$REPO_ROOT/vendor/td-verification"
ISABELLE="${ISABELLE:-isabelle}"
AFP="${AFP:-$HOME/afp/thys}"

test -d "$AFP" || { echo "ERROR: AFP not found at $AFP. Set AFP=<path> or install AFP." >&2; exit 1; }
