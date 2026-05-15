#!/usr/bin/env bash
# Start Isabelle/jEdit with the I/Q plugin auto-loaded. The plugin listens
# for MCP clients on 127.0.0.1:8765 once jEdit finishes loading. The auth
# token is pinned via IQ_AUTH_TOKEN so the .mcp.json `isabelle-iq` entry
# matches.
#
# Requires `./setup-iq.sh` to have been run at least once.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

export ISABELLE_HOME="${ISABELLE_HOME:-/Applications/Isabelle2025-2.app}"
ISABELLE="${ISABELLE:-$ISABELLE_HOME/bin/isabelle}"

if [[ ! -x "$ISABELLE" ]]; then
  echo "ERROR: Isabelle binary not found at '$ISABELLE'." >&2
  exit 1
fi

JAR="$HOME/.isabelle/Isabelle2025-2/jedit/jars/iq_plugin.jar"
if [[ ! -f "$JAR" ]]; then
  echo "ERROR: I/Q plugin JAR not installed at '$JAR'." >&2
  echo "  Run: ./setup-iq.sh" >&2
  exit 1
fi

# Session "TD" lives in the vendored td-verification submodule; jEdit must
# see it to load Goblint_Formalization. Matches start-ir.sh.
TD_COMPONENT_DIR="${TD_COMPONENT_DIR:-$SCRIPT_DIR/vendor/td-verification}"
if [[ ! -f "$TD_COMPONENT_DIR/ROOT" ]]; then
  echo "ERROR: TD solver component not found at '$TD_COMPONENT_DIR' (expected ROOT)." >&2
  echo "  Run: git submodule update --init vendor/td-verification" >&2
  exit 1
fi

# Match the token in .mcp.json
export IQ_AUTH_TOKEN="${IQ_AUTH_TOKEN:-isabelle-local}"

# Constrain I/Q's read/write reach to the proof repo
export IQ_MCP_ALLOWED_ROOTS="${IQ_MCP_ALLOWED_ROOTS:-$SCRIPT_DIR}"
export IQ_MCP_ALLOWED_READ_ROOTS="${IQ_MCP_ALLOWED_READ_ROOTS:-$SCRIPT_DIR}"

echo "Starting Isabelle/jEdit with I/Q (token=$IQ_AUTH_TOKEN, port=8765)..."
echo "  Allowed roots: $IQ_MCP_ALLOWED_ROOTS"
echo "  Plugin JAR:    $JAR"
echo
echo "Once the splash clears, agent can call mcp__isabelle-iq__authenticate"
echo "with token='$IQ_AUTH_TOKEN'."
echo

exec "$ISABELLE" jedit -d "$TD_COMPONENT_DIR" -d "$SCRIPT_DIR" "$@"
