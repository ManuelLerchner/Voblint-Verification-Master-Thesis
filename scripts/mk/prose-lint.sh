#!/usr/bin/env bash
# Lint prose with Vale: the paths given, as the pre-commit hook passes its
# staged files, or the thesis chapters and paper sections. Vale reads
# .typ files through typst2vast from conda-forge.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/../.."

# Fetches the packages named in .vale.ini when it changed. The pre-commit
# hooks lint in parallel, and two concurrent syncs delete each other's files,
# so a lock directory (mkdir is atomic) lets one sync while the other waits.
stamp=.vale/styles/.synced
if [ ! -e "$stamp" ] || [ .vale.ini -nt "$stamp" ]; then
  lock=.vale/.sync.lock
  until mkdir "$lock" 2> /dev/null; do sleep 1; done
  trap 'rmdir "$lock"' EXIT
  if [ ! -e "$stamp" ] || [ .vale.ini -nt "$stamp" ]; then
    vale sync > /dev/null
    touch "$stamp"
  fi
  rmdir "$lock"
  trap - EXIT
fi

if [ "$#" -gt 0 ]; then
  exec vale "$@"
fi

targets=(thesis/content)
[ -d paper/sections ] && targets+=(paper/sections)
exec vale "${targets[@]}"
