#!/usr/bin/env bash
# Keep the presentation session outside ROOTS so ordinary proof builds do not
# acquire a LaTeX dependency or rebuild the entire development for printing.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

variant=document
case "${1:-}" in
  "") ;;
  --include-examples) variant=document-full ;;
  *) echo "Usage: $0 [--include-examples]" >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "Usage: $0 [--include-examples]" >&2
  exit 2
fi
python3 "$REPO_ROOT/scripts/gen_pdf_session.py" "$@"
"$ISABELLE" build -v -j2 -o threads=12 \
  -d "$AFP" -d "$TD_DIR" -d "$REPO_ROOT" \
  -D "$REPO_ROOT/build/pdf-session" Voblint_Document
test -s "$REPO_ROOT/output/$variant.pdf"
echo "PDF: $REPO_ROOT/output/$variant.pdf"
