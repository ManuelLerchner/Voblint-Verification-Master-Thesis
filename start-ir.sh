#!/usr/bin/env bash
# Start the Isabelle/REPL MCP server (I/R) on port 9148.
# Requires Isabelle2025-2 installed; set ISABELLE to its binary if not on PATH.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IR="$SCRIPT_DIR/ir-repo/ir/repl.py"

# Locate Isabelle binary
ISABELLE="${ISABELLE:-$HOME/Isabelle2025-2/bin/isabelle}"

if [[ ! -x "$ISABELLE" ]]; then
  echo "ERROR: Isabelle not found at '$ISABELLE'"
  echo "  Download from https://isabelle.in.tum.de/ and set ISABELLE=/path/to/bin/isabelle"
  exit 1
fi

echo "Using Isabelle: $ISABELLE"
echo "Starting I/R MCP server on http://localhost:9148/mcp ..."
echo "Auth token: isabelle-local  (fixed via IR_AUTH_TOKEN)"
echo ""

exec env IR_AUTH_TOKEN=isabelle-local python3 "$IR" \
  --isabelle "$ISABELLE" \
  --session HOL \
  --mcp
