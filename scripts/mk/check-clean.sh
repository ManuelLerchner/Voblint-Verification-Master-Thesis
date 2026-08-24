#!/usr/bin/env bash
# Fail if the given paths are dirty *or* carry untracked files.
#
# `git diff --exit-code` reports neither untracked files nor whole-directory
# additions, so a generator that emits a new artifact into a directory the
# build first `rm -rf`s passes it silently. `git status --porcelain` reports
# both, which is what a drift gate needs.
set -euo pipefail

if [ "$#" -eq 0 ]; then
  echo "usage: check-clean.sh <path>..." >&2
  exit 2
fi

status="$(git status --porcelain -- "$@")"

if [ -n "$status" ]; then
  echo "drift detected in: $*" >&2
  echo "$status" >&2
  echo >&2
  # Tracked modifications also get a diff; untracked files show up above only.
  git --no-pager diff -- "$@" >&2 || true
  exit 1
fi
