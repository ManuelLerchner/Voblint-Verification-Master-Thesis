#!/usr/bin/env bash
# Print this repository's session names, one per line, in ROOTS order.
#
# ROOTS is ordered so that a session's ancestors and its `sessions` entries
# always precede it, which makes this list usable directly as a build order.
# Deriving it here is the point: three scripts used to hard-code the list, and
# a session rename left `Voblint_Analysis` in two of them long after the
# session was gone -- caught only by CI, and only in the jobs that run them.
set -euo pipefail
REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

while IFS= read -r dir; do
  [ -n "$dir" ] || continue
  sed -n 's/^session[[:space:]]\{1,\}"\{0,1\}\([A-Za-z_0-9]\{1,\}\)"\{0,1\}[[:space:]]\{1,\}in.*/\1/p' \
    "$REPO_ROOT/$dir/ROOT"
done < "$REPO_ROOT/ROOTS"
