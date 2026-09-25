#!/usr/bin/env bash
# Run the fast source-level checks against a committed tree, not the checkout.
#
# Hooks and `pixi run` check the working tree. A branch assembled without
# checking it out (a split-off PR, a cherry-pick onto another base) is then
# never checked itself, and a check fixed only in the checkout passes there
# while the branch still fails CI. This exports <ref> into a temporary
# directory and runs the checks from that copy; each script locates the
# repository from its own path, so it reads the exported tree.
#
# Usage: scripts/mk/check-ref.sh <ref>   (e.g. origin/isabelle/some-branch)
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: check-ref.sh <ref>" >&2
  exit 2
fi
ref="$1"
commit="$(git rev-parse --verify "$ref^{commit}")"

tree="$(mktemp -d "${TMPDIR:-/tmp}/check-ref.XXXXXX")"
trap 'rm -rf "$tree"' EXIT

git archive "$commit" | tar -x -C "$tree"

# `git archive` leaves submodules empty; export the solver at the pinned commit.
solver="vendor/td-verification"
pinned="$(git rev-parse "$commit:$solver" 2>/dev/null || true)"
if [ -n "$pinned" ] && git -C "$solver" cat-file -e "$pinned^{commit}" 2>/dev/null; then
  git -C "$solver" archive "$pinned" | tar -x -C "$tree/$solver"
else
  echo "check-ref: $solver at ${pinned:-?} unavailable; theory-prose may fail" >&2
fi

checks=(
  "scripts/check_theory_anchors.py"
  "scripts/check_pages_links.py --sources"
  "scripts/check_retired_identifiers.py"
  "scripts/check_thy_prose_refs.py"
  "scripts/check_locale_parameters.py"
  "scripts/check_isabelle_ascii.py"
  "scripts/check_thesis_refs.py"
)

failed=()
for check in "${checks[@]}"; do
  echo "== $check"
  # shellcheck disable=SC2086 # the entry carries its own arguments
  if ! python3 "$tree"/$check; then
    failed+=("$check")
  fi
done

echo
if [ "${#failed[@]}" -gt 0 ]; then
  echo "check-ref: ${#failed[@]} check(s) failed on $ref (${commit:0:8}):" >&2
  printf '  %s\n' "${failed[@]}" >&2
  exit 1
fi
echo "check-ref: all checks pass on $ref (${commit:0:8})"
