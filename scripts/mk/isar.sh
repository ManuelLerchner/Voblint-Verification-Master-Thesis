#!/usr/bin/env bash
# Run isar-tools with the AFP, and the vendored TD sessions when checked out, on
# its session path, like `isabelle build -d`. Whether a word is an Isar command
# depends on the sessions a theory imports; without the AFP, `derive` and the
# other AFP commands would be read as part of the preceding command.
#
# Usage: isar.sh check|fmt [OPTIONS] [PATHS...]
# `fmt` wraps lines at 100 symbols, the limit `isar stats style` reports.
# Without PATHS it formats every tracked theory under src/ except generated
# ones: their generators own the layout, and the drift checks compare it.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"
cd "$REPO_ROOT"

include=(-d "$AFP")
if [ -f "$TD_DIR/ROOT" ]; then include+=(-d "$TD_DIR"); fi

command="$1"
shift
if [ "$command" != fmt ]; then
  exec isar "$command" "${include[@]}" "$@"
fi

paths=0
for arg in "$@"; do
  case "$arg" in -*) ;; *) paths=$((paths + 1)) ;; esac
done
if [ "$paths" -eq 0 ]; then
  mapfile -t theories < <(git ls-files -- 'src/*.thy' \
    | grep -v -e '/generated/' -e '^src/Program_Model/VIMP/VIMP_Grammar_Generated\.thy$')
  set -- "$@" "${theories[@]}"
fi
exec isar fmt --max-line-length 100 "${include[@]}" "$@"
