#!/usr/bin/env bash
# Assemble the GitHub Pages site: landing page, Isabelle HTML, PDFs, and
# the WebAssembly browser analyzer.
#
# Each input directory is copied whole, so a new page, image or wasm asset
# needs no entry here. Isabelle HTML stays at the site root so thesis deep links
# keep working; scripts/check_pages_links.py mirrors this layering.
#
# That whole-directory copy is also what publishes pages/robots.txt and the
# Google Search Console token pages/google*.html at the site root, which is the
# only place either is looked for. .nojekyll below keeps them served verbatim.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SITE_DIR="${1:-$REPO_ROOT/build/github-pages}"

HTML_SRC="${HTML_SRC:-$REPO_ROOT/build/isabelle-html}"
FORMALIZATION_PDF="${FORMALIZATION_PDF:-$REPO_ROOT/output/document.pdf}"
THESIS_PDF="${THESIS_PDF:-$REPO_ROOT/thesis/Voblint_Thesis.pdf}"
BROWSER_DIR="${BROWSER_DIR:-$REPO_ROOT/build/browser}"

for path in "$HTML_SRC" "$FORMALIZATION_PDF" "$THESIS_PDF" "$BROWSER_DIR"; do
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

# The sitemap is derived too, so its lastmod cannot go stale. Only the pages a
# reader would search for are listed; the generated theory tree is reachable
# from them and is left to ordinary crawling. SITE_URL must match the canonical
# links in pages/*.html and the Sitemap line in pages/robots.txt.
SITE_URL="${SITE_URL:-https://manuellerchner.github.io/Voblint-Verification-Master-Thesis}"
BUILD_DATE="$(date -u +%Y-%m-%d)"
{
  echo '<?xml version="1.0" encoding="UTF-8"?>'
  echo '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'
  for entry in "/:1.0" "/playground.html:0.9" "/thesis.pdf:0.6" "/formalization.pdf:0.5"; do
    printf '  <url><loc>%s%s</loc><lastmod>%s</lastmod><priority>%s</priority></url>\n' \
      "$SITE_URL" "${entry%%:*}" "$BUILD_DATE" "${entry##*:}"
  done
  echo '</urlset>'
} > "$SITE_DIR/sitemap.xml"

cp "$FORMALIZATION_PDF" "$SITE_DIR/formalization.pdf"
cp "$THESIS_PDF" "$SITE_DIR/thesis.pdf"
touch "$SITE_DIR/.nojekyll"

echo "GitHub Pages site: $SITE_DIR"
