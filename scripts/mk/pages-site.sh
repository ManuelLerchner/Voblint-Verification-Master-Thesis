#!/usr/bin/env bash
# Assemble the GitHub Pages site: landing page, Isabelle HTML, PDFs, and
# the WebAssembly browser analyzer.
#
# Each input directory is copied whole, so a new page, image or wasm asset
# needs no entry here. Isabelle HTML stays at the site root so thesis deep links
# keep working; scripts/check_pages_links.py mirrors this layering.
#
# That whole-directory copy is also what publishes pages/robots.txt and the
# Google Search Console token pages/google*.html at the project root. Crawlers
# only read robots.txt at the host root; submit this project's sitemap through
# Search Console. .nojekyll below keeps these files served verbatim.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SITE_DIR="${1:-$REPO_ROOT/build/github-pages}"

HTML_SRC="${HTML_SRC:-$REPO_ROOT/build/isabelle-html}"
FORMALIZATION_PDF="${FORMALIZATION_PDF:-$REPO_ROOT/output/document.pdf}"
THESIS_PDF="${THESIS_PDF:-$REPO_ROOT/thesis/Lerchner_Master_Thesis.pdf}"
PAPER_PDF="${PAPER_PDF:-$REPO_ROOT/paper/_build/main.pdf}"
BROWSER_DIR="${BROWSER_DIR:-$REPO_ROOT/build/browser}"

for path in "$HTML_SRC" "$FORMALIZATION_PDF" "$THESIS_PDF" "$PAPER_PDF" "$BROWSER_DIR"; do
  test -e "$path" || {
    echo "ERROR: missing pages input: $path" >&2
    exit 1
  }
done

rm -rf "$SITE_DIR"
mkdir -p "$SITE_DIR/assets"

cp -R "$HTML_SRC/." "$SITE_DIR/"
cp -R "$REPO_ROOT/pages/." "$SITE_DIR/"
cp -R "$REPO_ROOT/docs/images/." "$SITE_DIR/assets/"

# wasm_of_ocaml emits a JavaScript loader plus a companion asset directory; both
# keep their generated names and relative layout.
cp -R "$BROWSER_DIR/." "$SITE_DIR/assets/"

# Source maps outweigh the wasm they describe and serve only local debugging;
# Finder metadata can ride along when pages/ is copied from a Mac checkout.
find "$SITE_DIR/assets" -name '*.map' -type f -delete
find "$SITE_DIR" -name '.DS_Store' -type f -delete

# Derived on every build so they never go stale: the explainer's size figures,
# and the regression corpus the playground offers as examples.
python3 "$REPO_ROOT/scripts/pages_stats.py" --out "$SITE_DIR/assets/site-stats.js" \
  --fill "$SITE_DIR"/*.html
python3 "$REPO_ROOT/scripts/pages_examples.py" --out "$SITE_DIR/assets/regression-examples.json"

# List search entry points; ordinary links expose the generated theory tree.
# In production, SITE_URL matches the canonical links in pages/*.html.
# Preview builds supply their own base URL.
SITE_URL="${SITE_URL:-https://manuellerchner.github.io/Voblint-Verification-Master-Thesis}"
# Build time is not a content modification date; omit optional lastmod values.
SITE_URL="${SITE_URL%/}"
{
  echo '<?xml version="1.0" encoding="UTF-8"?>'
  echo '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'
  for entry in "/" "/playground.html" "/proof-map.html" "/Voblint/index.html" "/profiling.html" "/thesis.pdf" "/paper.pdf" "/formalization.pdf"; do
    printf '  <url><loc>%s%s</loc></url>\n' "$SITE_URL" "$entry"
  done
  echo '</urlset>'
} > "$SITE_DIR/sitemap.xml"

cp "$FORMALIZATION_PDF" "$SITE_DIR/formalization.pdf"
cp "$THESIS_PDF" "$SITE_DIR/thesis.pdf"
cp "$PAPER_PDF" "$SITE_DIR/paper.pdf"
# A pull request preview also carries its changes against main.
if [ -n "${THESIS_DIFF_DIR:-}" ]; then
  cp "$THESIS_DIFF_DIR/thesis-diff.pdf" "$THESIS_DIFF_DIR/thesis-redline.pdf" "$SITE_DIR/"
fi
touch "$SITE_DIR/.nojekyll"

echo "GitHub Pages site: $SITE_DIR"
