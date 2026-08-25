#!/bin/sh
# Build the Typst thesis with warnings treated as errors.
#
# Typst warns rather than fails on the things that quietly spoil a page -- an
# unresolved reference, a missing font, content overflowing its container. In a
# 100-page document those scroll past unread, so this fails the build on any of
# them. Pass --allow-warnings to see the document anyway while drafting.
set -eu

root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
out="$root/Voblint_Thesis.pdf"
strict=1
[ "${1:-}" = "--allow-warnings" ] && strict=0

log=$(mktemp)
trap 'rm -f "$log"' EXIT

if ! typst compile --root "$root" --font-path "$root/assets/fonts" \
     "$root/thesis.typ" "$out" 2>"$log"; then
  cat "$log" >&2
  exit 1
fi

warnings=$(grep -c '^warning:' "$log" || true)
if [ "$warnings" -gt 0 ]; then
  cat "$log" >&2
  if [ "$strict" -eq 1 ]; then
    echo "typst-build: $warnings warning(s); refusing to call this a build." >&2
    echo "Fix them, or pass --allow-warnings while drafting." >&2
    exit 1
  fi
fi

pages=$(pdfinfo "$out" 2>/dev/null | awk '/^Pages:/ {print $2}')
words=$(pdftotext "$out" - 2>/dev/null | wc -w | tr -d ' ')
echo "typst-build: ${pages:-?} pages, ${words:-?} words -> ${out#"$root"/}"
