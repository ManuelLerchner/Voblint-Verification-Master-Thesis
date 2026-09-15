#!/usr/bin/env bash
# Lint shell scripts with shellcheck: the paths given, as the pre-commit hook
# passes its staged files, or every tracked script.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/../.."

if [ "$#" -gt 0 ]; then
  exec shellcheck "$@"
fi

git ls-files -z '*.sh' | xargs -0 shellcheck
