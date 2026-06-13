#!/usr/bin/env bash
# Start the Isabelle/REPL MCP server (I/R) on port 9148.
# Requires Isabelle2025-2 installed; set ISABELLE to its binary if not on PATH.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
IR="$REPO_ROOT/vendor/autocorrode/ir/repl.py"

# Session "TD" (theory TD.TD_side) vendor submodule ROOT
TD_COMPONENT_DIR="${TD_COMPONENT_DIR:-$REPO_ROOT/vendor/td-verification}"
if [[ ! -f "$TD_COMPONENT_DIR/ROOT" ]]; then
  echo "ERROR: TD solver component not found at '$TD_COMPONENT_DIR' (expected ROOT)."
  echo "  Run: git submodule update --init vendor/td-verification"
  echo "  Or set TD_COMPONENT_DIR to the directory containing session TD's ROOT."
  exit 1
fi

# Locate Isabelle binary
ISABELLE="${ISABELLE:-/Applications/Isabelle2025-2.app/bin/isabelle}"

if [[ ! -x "$ISABELLE" ]]; then
  echo "ERROR: Isabelle not found at '$ISABELLE'"
  echo "  Download from https://isabelle.in.tum.de/ and set ISABELLE=/path/to/bin/isabelle"
  exit 1
fi

echo "Using Isabelle: $ISABELLE"
echo "Starting I/R MCP server on http://localhost:9148/mcp ..."
echo "Auth token: isabelle-local  (fixed via IR_AUTH_TOKEN)"
echo "MCP streamable-http requires Accept: application/json, text/event-stream (see .cursor/mcp.json)."
echo "Quick probe: curl -sS -m 2 -H \"Authorization: Bearer isabelle-local\" -H \"Accept: application/json, text/event-stream\" http://127.0.0.1:9148/mcp"
echo ""

PYTHON="${REPO_ROOT}/.venv/bin/python3"
if [[ ! -x "$PYTHON" ]]; then
  echo "ERROR: venv not found. Run ./scripts/setup.sh first."
  exit 1
fi

# ML process requires a Poly/ML heap for --session; build is incremental when up-to-date.
# Set IR_SKIP_HEAP_BUILD=1 to skip (faster restart if heap already exists; fails if missing).
# Verbose build by default (theory-level lines on stdout). Set IR_VERBOSE_BUILD=0 for quiet.
# Parallelism: unset IR_BUILD_JOBS => auto (-j hw.ncpu on macOS, nproc on Linux). On low RAM (e.g. 8 GB)
# set IR_BUILD_JOBS=4 (or 2) to reduce memory spikes from many concurrent Poly/ML workers.
if [[ "${IR_SKIP_HEAP_BUILD:-0}" != "1" ]]; then
  echo "Ensuring session heap (Voblint_Formalization) ..."
  vb=()
  [[ "${IR_VERBOSE_BUILD:-1}" != "0" ]] && vb=(-v)
  jobs=()
  if [[ -n "${IR_BUILD_JOBS:-}" ]]; then
    jobs=(-j "$IR_BUILD_JOBS")
  else
    case "$(uname -s)" in
      Darwin)
        n="$(sysctl -n hw.ncpu 2>/dev/null || true)"
        [[ -n "$n" ]] && jobs=(-j "$n")
        ;;
      Linux)
        command -v nproc >/dev/null 2>&1 && jobs=(-j "$(nproc)")
        ;;
    esac
  fi
  "$ISABELLE" build -b "${vb[@]}" "${jobs[@]}" -d "$TD_COMPONENT_DIR" -d "$REPO_ROOT" Voblint_Formalization
  echo ""
else
  echo "Skipping heap build (IR_SKIP_HEAP_BUILD=1)."
  echo ""
fi

echo "When MCP is running, leave this window alone: the %> prompt is the I/R console;"
echo "accidental keys (or Ctrl+C) can cancel input or shut down MCP (Uvicorn) while clients are connected."
echo ""

exec env IR_AUTH_TOKEN=isabelle-local IR_DEBUG="${IR_DEBUG:-1}" "$PYTHON" "$IR" \
  --isabelle "$ISABELLE" \
  --session Voblint_Formalization \
  --dir "$TD_COMPONENT_DIR" \
  --dir "$REPO_ROOT" \
  --mcp
