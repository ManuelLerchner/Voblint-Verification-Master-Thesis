#!/usr/bin/env bash
# Clone the AutoCorrode I/R MCP server (sparse checkout — ir/ only).
# Run once after cloning this repo, before start-ir.sh.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IR_REPO="$SCRIPT_DIR/ir-repo"

if [[ -d "$IR_REPO/.git" ]]; then
  echo "ir-repo/ already set up, skipping."
  exit 0
fi

echo "Cloning AutoCorrode (sparse, ir/ only) ..."
git clone \
  --filter=blob:none \
  --no-checkout \
  --depth 1 \
  https://github.com/awslabs/AutoCorrode \
  "$IR_REPO"

git -C "$IR_REPO" sparse-checkout set ir
git -C "$IR_REPO" checkout

echo "Installing Python requirements ..."
pip3 install -r "$IR_REPO/ir/requirements.txt"

echo ""
echo "Done. Start the daemon with:  ./start-ir.sh"
