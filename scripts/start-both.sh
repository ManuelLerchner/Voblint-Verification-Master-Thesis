#!/usr/bin/env bash
# Start both I/Q (jEdit + MCP on 8765) and I/R (headless REPL MCP on 9148).
# I/R runs in the background, I/Q in the foreground. Killing this script
# (Ctrl+C or window close) tears down I/R as well.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

IR_LOG="${IR_LOG:-$REPO_ROOT/.start-both-ir.log}"

IR_PID=""
cleanup() {
  if [[ -n "$IR_PID" ]] && kill -0 "$IR_PID" 2>/dev/null; then
    echo
    echo "Stopping I/R (pid=$IR_PID)..."
    kill "$IR_PID" 2>/dev/null || true
    wait "$IR_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT INT TERM

echo "Starting I/R in background (log: $IR_LOG)..."
"$SCRIPT_DIR/start-ir.sh" >"$IR_LOG" 2>&1 &
IR_PID=$!
echo "  I/R pid=$IR_PID (port 9148)"
echo

echo "Starting I/Q in foreground (port 8765)..."
"$SCRIPT_DIR/start-iq.sh" "$@"
