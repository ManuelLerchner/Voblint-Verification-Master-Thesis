#!/usr/bin/env bash
# Lint the paper's LaTeX sources with chktex: the paths given, as the pre-commit
# hook passes its staged files, or every handwritten source. `-I0` checks each
# file once instead of following main.tex's \input chain into generated files.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/../.."

if [ "$#" -gt 0 ]; then
  exec chktex -q -I0 -l paper/chktexrc "$@"
fi

git ls-files -z 'paper/*.tex' ':!paper/lipics/' ':!paper/sty/' ':!paper/generated/' |
  xargs -0 chktex -q -I0 -l paper/chktexrc
