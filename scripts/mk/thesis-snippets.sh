#!/usr/bin/env bash
# Lift the declarations thesis/shared/snippets.toml names into
# thesis/shared/generated/snippets/: --check diffs, --write regenerates.
# Snippets pinned to `~~/src/HOL/...` are read below ISABELLE_HOME; where
# Isabelle is not installed, isar-tools skips them with a note.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
if [ -z "${ISABELLE_HOME:-}" ] && command -v isabelle >/dev/null; then
  ISABELLE_HOME="$(isabelle getenv -b ISABELLE_HOME)"
  export ISABELLE_HOME
fi
exec isar project extract --statement \
  --manifest thesis/shared/snippets.toml \
  --out thesis/shared/generated/snippets "$@"
