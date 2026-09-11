#!/usr/bin/env bash
# Fail if the given paths differ from the staged snapshot or carry untracked
# files.
#
# Comparing against HEAD would reject an intentionally regenerated artifact
# after it has been staged. A pre-commit drift gate instead asks whether the
# generator changed the working tree relative to the index. `git diff` answers
# that for tracked paths; `git ls-files --others` covers new artifacts.
set -euo pipefail

if [ "$#" -eq 0 ]; then
  echo "usage: check-clean.sh <path>..." >&2
  exit 2
fi

modified="$(git diff --name-status -- "$@")"
untracked="$(git ls-files --others --exclude-standard -- "$@")"

if [ -n "$modified" ] || [ -n "$untracked" ]; then
  echo "drift detected in: $*" >&2
  if [ -n "$modified" ]; then
    echo "$modified" >&2
  fi
  if [ -n "$untracked" ]; then
    printf '?? %s\n' "$untracked" >&2
  fi
  echo >&2
  # Tracked modifications get a content diff; untracked files are named above.
  git --no-pager diff -- "$@" >&2 || true
  exit 1
fi
