#!/usr/bin/env bash
# The exported tracer's verification gate, in order. Each step builds on the one
# before; run it alone, never beside another Isabelle or dune build.
#
#   1. regenerate the export from the theories
#   2. the trace calls are in the generated OCaml at every intended point
#   3. traced and untraced runs print the same result on the regression corpus
#   4. the trace tests, the reducer's unit tests and its invariant against the result
#   5. the WebAssembly build and the browser's traces
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

step() { printf '\n== %s\n' "$*"; }

step "1. codegen"
pixi run codegen
pixi run codegen-check

step "2. trace calls in the generated module"
python3 - codegen/generated/ml/Voblint_CLI.ml <<'EOF'
import re, sys

text = open(sys.argv[1]).read()

def body(name):
    m = re.search(r"^(?:let rec|and) " + re.escape(name) + r"\b.*?;;", text, re.S | re.M)
    if not m:
        sys.exit(f"missing function {name}")
    return m.group(0)

# (function, channel, minimum number of emit calls in its body)
expected = [
    ("tD_side_rule_Interp_solve_rec_c", "solver", 20),  # query, iterate, eq, rhs, side, ...
    ("tD_side_rule_Interp_solve", "solver", 2),         # start, stop
    ("destab_opt", "solver", 1),                        # destabilize
    ("destab_iter_opt", "solver", 1),                   # stable remove
    ("route_unit", "route", 1),
    ("cs_route", "route", 1),
    ("mcp_formals_route", "route", 1),
    ("analysis_report_of", "run", 3),                # one per context mode
]
bad = []
for name, channel, least in expected:
    n = body(name).count(f'Solver_trace_hook.emit "{channel}"')
    print(f"{name}: {n} emit \"{channel}\" (expected >= {least})")
    if n < least:
        bad.append(name)
if bad:
    sys.exit("trace calls missing in: " + ", ".join(bad))
EOF

step "3. traced and untraced results identical"
pixi run cli-build
fail=0
for f in $(fd -e vimp . tests/regression docs/readme-figures | sort); do
  for cfg in "interval none warrow" "interval entry-state join" "sign,parity call-string per-origin" "int entry-state warrow-per-origin"; do
    read -r analysis ctx globals <<<"$cfg"
    extra=()
    [ "$ctx" = call-string ] && extra=(--context-depth 1)
    plain="$(./cli/voblint --analysis "$analysis" --context "$ctx" "${extra[@]}" --globals "$globals" "$f" 2>/dev/null; echo "rc=$?")"
    traced="$(./cli/voblint --analysis "$analysis" --context "$ctx" "${extra[@]}" --globals "$globals" --trace --format jsonl "$f" 2>/dev/null; echo "rc=$?")"
    if [ "$plain" != "$traced" ]; then
      echo "DIFFERS: $f ($cfg)"
      fail=1
    fi
  done
done
[ "$fail" = 0 ] || { echo "traced output differs from untraced"; exit 1; }
pixi run cli-test

step "4. trace tests and replay invariant"
node --test tests/replay_state.test.mjs
python3 -m pytest tests/test_solver_trace.py tests/test_replay_invariant.py

step "5. browser"
pixi run browser-build
python3 -m pytest tests/test_browser_trace.py

echo
echo "tracer gate: all steps passed"
