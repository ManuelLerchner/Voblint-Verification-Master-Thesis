#!/usr/bin/env bash
# Wraps cli/voblint for the `voblint` pixi task: runs the analysis
# regardless of a stale codegen/generated/ (cli-build.sh's own mismatch
# warning stays non-fatal there by design -- see its header -- because
# cli-test and cli-smoke also depend on cli-build and shouldn't be blocked
# by it), but fails `pixi run voblint` afterward if generated/ was stale,
# so the analysis output stays visible while the mismatch is still
# CI-visible. Preserves a genuine analysis failure exit code over the
# staleness one.
#
# Also fuzzy-picks the FILE.vimp positional via fzf when the caller omitted
# it interactively, so `pixi run voblint --analysis interval` works like
# `pixi run voblint --analysis interval <tab-complete-ish fuzzy pick>`.
# cli/voblint itself stays deterministic/non-interactive (regression and
# property tests call it directly with an explicit file) -- the picker is
# wrapper-only plumbing, same as the staleness check below.
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

args=("$@")

# Does argv already carry a FILE positional? Walk it flag-arity-aware
# (mirrors cli/main.ml's parse_args) rather than treating any non-flag
# token as a file -- `--analysis interval` must not be misread as a file.
# --help short-circuits to cli/voblint unchanged: no picker.
has_file=0
skip_picker=0
i=0
n=${#args[@]}
while [ "$i" -lt "$n" ]; do
  arg="${args[$i]}"
  case "$arg" in
    --help) skip_picker=1; break ;;
    --analysis | --context | --solver | --timeout) i=$((i + 2)) ;;
    --dot | --dot-full | --graph-snapshot | --parse-only) i=$((i + 1)) ;;
    -*) i=$((i + 1)) ;;
    *) has_file=1; break ;;
  esac
done

if [ "$has_file" -eq 0 ] && [ "$skip_picker" -eq 0 ] && [ -t 0 ] && [ -t 1 ]; then
  if command -v fzf >/dev/null 2>&1; then
    # Repo-relative candidates (not absolute REPO_ROOT-prefixed paths) keep
    # the fuzzy match signal on the part that actually varies between
    # files, and fzf's own preview shell runs cwd'd to REPO_ROOT too so
    # `{}` still resolves -- both subshells below are command-substitution
    # forks, so the `cd` never leaks into the rest of this script.
    vimp_files="$(cd "$REPO_ROOT" && find tests/regression -type f -name '*.vimp' | sort)"
    if [ -n "$vimp_files" ]; then
      selected="$(cd "$REPO_ROOT" && printf '%s\n' "$vimp_files" \
        | fzf --prompt="voblint file> " --height=40% --reverse \
              --preview 'bat --color=always {} 2>/dev/null || cat {}')"
      fzf_status=$?
      if [ "$fzf_status" -ne 0 ] || [ -z "$selected" ]; then
        exit 130
      fi
      args+=("$REPO_ROOT/$selected")
    fi
  else
    echo "voblint: fzf not found on PATH -- skipping interactive file picker (install fzf to enable it)" >&2
  fi
fi

stamp="$REPO_ROOT/codegen/generated/.source-hash"
current_hash="$("$SCRIPT_DIR/codegen-hash.sh")"
source_mismatch=0
if [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$current_hash" ]; then
  source_mismatch=1
fi

"$REPO_ROOT/cli/voblint" ${args[@]+"${args[@]}"}
analysis_status=$?

if [ "$analysis_status" -ne 0 ]; then
  exit "$analysis_status"
fi

exit "$source_mismatch"
