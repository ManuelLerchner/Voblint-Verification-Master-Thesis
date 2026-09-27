#!/usr/bin/env bash
# Run isar-tools with the AFP, and the vendored TD sessions when checked out, on
# its session path, like `isabelle build -d`. Whether a word is an Isar command
# depends on the sessions a theory imports; without the AFP, `derive` and the
# other AFP commands would be read as part of the preceding command.
# Usage: isar.sh check|fmt [ARGS...]; `fmt` without paths formats src/.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"
cd "$REPO_ROOT"

include=(-d "$AFP")
if [ -f "$TD_DIR/ROOT" ]; then include+=(-d "$TD_DIR"); fi

command="$1"
shift
if [ "$command" = fmt ] && [ $# -eq 0 ]; then set -- src; fi
exec isar "$command" "${include[@]}" "$@"
