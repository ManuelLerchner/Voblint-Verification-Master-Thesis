#!/usr/bin/env bash
# Lint prose with Vale: the paths given, as the pre-commit hook passes its
# staged files, or the thesis chapters and paper sections. Vale reads
# .typ files through typst2vast, which is built into the pixi environment
# until conda-forge packages it (conda-forge/staged-recipes#35317).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/../.."

# Pinned to a fork commit that keeps table cells, captions and display math
# out of the surrounding sentence (jdkato/typst2vast#2); return to a release
# once it is merged.
TYPST2VAST_REV=16086c6d04bffaaf73399f0eba825b1fbe7c036c
stamp="$CONDA_PREFIX/share/typst2vast.rev"
if [ "$(cat "$stamp" 2> /dev/null)" != "$TYPST2VAST_REV" ]; then
  cargo install --locked --force --root "$CONDA_PREFIX" \
    --git https://github.com/ManuelLerchner/typst2vast --rev "$TYPST2VAST_REV" typst2vast
  mkdir -p "$(dirname "$stamp")"
  printf '%s\n' "$TYPST2VAST_REV" > "$stamp"
fi

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
