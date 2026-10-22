#!/usr/bin/env bash
# Lint prose with Vale: the paths given, as the pre-commit hook passes its
# staged files, or the thesis chapters and paper sections. Vale reads
# .typ files through typst2vast, which is built into the pixi environment
# until conda-forge packages it (conda-forge/staged-recipes#35317).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/../.."

if ! command -v typst2vast > /dev/null; then
  cargo install --locked --version 0.1.0 --root "$CONDA_PREFIX" typst2vast
fi

# Fetches the packages named in .vale.ini; cheap once they are present.
vale sync > /dev/null

if [ "$#" -gt 0 ]; then
  exec vale "$@"
fi

targets=(thesis/content)
[ -d paper/sections ] && targets+=(paper/sections)
exec vale "${targets[@]}"
