#!/usr/bin/env bash
# Benchmarks cli/voblint with hyperfine for the `bench` pixi task: one timed
# series per abstract domain over the same FILE.vimp, so domain/solver cost
# can be compared in place. Non-FILE arguments pass through to cli/voblint
# unchanged (e.g. --context entry-state); pass --analysis yourself (comma
# list allowed) to narrow the comparison. Each candidate domain is probed
# once first -- a combination the CLI rejects as a configuration error
# (exit 1, say parity under --context entry-state) is dropped with a note
# instead of aborting the whole hyperfine run, and the probe doubles as the
# warm-up. Like voblint-run.sh, omitting FILE interactively opens an fzf
# picker over the regression corpus; cli/voblint itself stays
# non-interactive.
#
# --plot[=OUT.png] additionally exports the run as JSON next to OUT and
# renders a per-domain whisker + histogram plot via scripts/plot_bench.py
# (hyperfine itself only exports; plotting is a documented add-on).
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
VOBLINT="$REPO_ROOT/cli/voblint"

usage() {
  echo "usage: pixi run bench [--plot[=OUT.png]] [voblint flags...] FILE.vimp"
  echo "       default domain sweep: sign,interval,int,parity"
  echo "       --analysis a[,b,...] narrows the sweep; other flags pass through"
  echo "       --plot renders a per-domain whisker + histogram plot (default: voblint-bench.png)"
}

domains="sign,interval,int,parity"
passthrough=()
file=""
plot=0
plot_out="voblint-bench.png"

# Flag-arity-aware walk (mirrors cli/main.ml's parse_args) so a flag value
# like `--context entry-state` is not misread as the FILE positional.
args=("$@")
i=0
n=${#args[@]}
while [ "$i" -lt "$n" ]; do
  arg="${args[$i]}"
  case "$arg" in
    --help) usage; exit 0 ;;
    --plot) plot=1 ;;
    --plot=*) plot=1; plot_out="${arg#--plot=}" ;;
    --analysis) i=$((i + 1)); domains="${args[$i]:-}" ;;
    --context | --context-depth | --context-graph | --solver | --timeout | --html-out)
      passthrough+=("$arg" "${args[$((i + 1))]:-}"); i=$((i + 1)) ;;
    -*) passthrough+=("$arg") ;;
    *) file="$arg" ;;
  esac
  i=$((i + 1))
done

if [ -z "$file" ] && [ -t 0 ] && [ -t 1 ] && command -v fzf >/dev/null 2>&1; then
  selected="$(cd "$REPO_ROOT" && find tests/regression -type f -name '*.vimp' | sort \
    | fzf --prompt="bench file> " --height=40% --reverse \
          --preview 'bat --color=always {} 2>/dev/null || cat {}')" || exit 130
  [ -n "$selected" ] || exit 130
  file="$REPO_ROOT/$selected"
fi

if [ -z "$file" ]; then
  usage >&2
  exit 1
fi

# Probe each domain once: keep the ones the CLI accepts, drop configuration
# errors (exit 1) with the CLI's own message, and fail hard on anything else
# (parse error, timeout, ...) -- those would fail identically for every
# domain, so there is nothing left to compare.
valid=""
for d in $(printf '%s' "$domains" | tr ',' ' '); do
  probe_err="$("$VOBLINT" --analysis "$d" ${passthrough[@]+"${passthrough[@]}"} "$file" 2>&1 >/dev/null)"
  status=$?
  case "$status" in
    0) valid="${valid:+$valid,}$d" ;;
    1) echo "bench: skipping $d: ${probe_err:-configuration rejected}" >&2 ;;
    *) printf '%s\n' "$probe_err" >&2; exit "$status" ;;
  esac
done

if [ -z "$valid" ]; then
  echo "bench: no domain accepted this configuration" >&2
  exit 1
fi

quoted=""
for a in ${passthrough[@]+"${passthrough[@]}"} "$file"; do
  quoted="$quoted $(printf '%q' "$a")"
done

# -N skips the intermediate shell: these runs can sit in the low-millisecond
# range, where shell startup would dominate the measurement.
if [ "$plot" -eq 0 ]; then
  exec hyperfine -N -L analysis "$valid" \
    "$(printf '%q' "$VOBLINT") --analysis {analysis}$quoted"
fi

plot_json="${plot_out%.png}.json"
hyperfine -N -L analysis "$valid" --export-json "$plot_json" \
  "$(printf '%q' "$VOBLINT") --analysis {analysis}$quoted" || exit $?

python3 "$REPO_ROOT/scripts/plot_bench.py" "$plot_json" "$plot_out" \
  --title "$(basename "$file")" || exit $?

# Interactive convenience only: never block a scripted run on a viewer.
if [ -t 1 ] && command -v open >/dev/null 2>&1; then
  open "$plot_out"
fi
