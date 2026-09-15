#!/usr/bin/env bash
# Format Typst sources with typstyle at the 100-column limit the theories follow:
# the paths given, as the pre-commit hook passes its staged files, or every tracked
# source except the generated symbol table.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/../.."

if [ "$#" -gt 0 ]; then
  exec typstyle -l 100 -i "$@"
fi

git ls-files -z '*.typ' ':!thesis/lib/isabelle-symbols.typ' | xargs -0 typstyle -l 100 -i
