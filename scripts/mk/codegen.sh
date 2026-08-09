#!/usr/bin/env bash
# Regenerate codegen/generated/ from the export_code declarations in
# src/Examples/{Sign,Interval}/Exec_*.thy. Do not hand-edit generated files.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

AFP="$AFP" "$REPO_ROOT/scripts/regenerate-codegen.sh"
