#!/usr/bin/env bash
# Assemble the GitHub Pages site: landing page, Isabelle HTML, and PDFs.
# Isabelle HTML stays at the site root so thesis deep links keep working.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SITE_DIR="${1:-$REPO_ROOT/build/github-pages}"

HTML_SRC="${HTML_SRC:-$REPO_ROOT/build/isabelle-html}"
FORMALIZATION_PDF="${FORMALIZATION_PDF:-$REPO_ROOT/output/document.pdf}"
THESIS_PDF="${THESIS_PDF:-$REPO_ROOT/thesis/Voblint_Thesis.pdf}"
BROWSER_JS="${BROWSER_JS:-$REPO_ROOT/build/browser/voblint.js}"

for path in "$HTML_SRC" "$FORMALIZATION_PDF" "$THESIS_PDF" "$BROWSER_JS"; do
  test -e "$path" || {
    echo "ERROR: missing pages input: $path" >&2
    exit 1
  }
done

rm -rf "$SITE_DIR"
mkdir -p "$SITE_DIR/assets"
mkdir -p "$SITE_DIR/assets/reports"

cp -R "$HTML_SRC/." "$SITE_DIR/"
cp "$REPO_ROOT/pages/index.html" "$SITE_DIR/index.html"
cp "$REPO_ROOT/pages/style.css" "$SITE_DIR/style.css"
cp "$REPO_ROOT/pages/browser.js" "$SITE_DIR/browser.js"
cp "$REPO_ROOT/docs/images/banner.png" "$SITE_DIR/assets/banner.png"
cp "$REPO_ROOT/docs/images/favicon.png" "$SITE_DIR/assets/favicon.png" 
cp "$BROWSER_JS" "$SITE_DIR/assets/voblint.js"
cp "$REPO_ROOT/docs/images/while_loop_cfg.png" "$SITE_DIR/assets/while_loop_cfg.png"
for image in report-graph-sign report-context-interval report-int-refinement \
  report-arithmetic-definite report-arithmetic-possible; do
  if test -e "$REPO_ROOT/docs/images/$image.png"; then
    cp "$REPO_ROOT/docs/images/$image.png" "$SITE_DIR/assets/reports/$image.png"
  fi
done
cp "$FORMALIZATION_PDF" "$SITE_DIR/formalization.pdf"
cp "$THESIS_PDF" "$SITE_DIR/thesis.pdf"
touch "$SITE_DIR/.nojekyll"

echo "GitHub Pages site: $SITE_DIR"
