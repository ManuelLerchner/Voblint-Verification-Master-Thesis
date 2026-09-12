#!/usr/bin/env python3
"""Render the current README for inclusion after the formalization's title page."""

import argparse
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def build(output):
    if not shutil.which("pandoc"):
        raise SystemExit("pandoc is required for the README pages; install it and retry.")
    isabelle = os.environ.get("ISABELLE", "isabelle")
    home = subprocess.check_output([isabelle, "getenv", "-b", "ISABELLE_HOME"], text=True).strip()
    fonts = Path(home) / "doc/fonts"
    output = output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    help_text = subprocess.check_output(["pandoc", "--help"], text=True)
    no_highlight = ("--syntax-highlighting=none" if "--syntax-highlighting" in help_text
                    else "--no-highlight")
    # Isabelle's own fonts cover the symbols used in the README's theorem blocks.
    command = [
        "pandoc", str(REPO / "README.md"), "--from=gfm", "--standalone",
        "--lua-filter", str(REPO / "scripts/pdf_readme.lua"),
        "--pdf-engine=lualatex", no_highlight,
        "--include-in-header", str(REPO / "document/readme-header.tex"),
        "--resource-path", str(REPO),
        "-V", "geometry:margin=20mm", "-V", "fontsize:10pt", "-V", "papersize:a4",
        "-V", "monofont:IsabelleDejaVuSansMono.ttf",
        "-V", f"monofontoptions:Path={fonts}/,Scale=0.8",
        "-V", "colorlinks:true",
    ]
    # Publish only a successfully typeset rendering.
    with tempfile.TemporaryDirectory(prefix="readme-", dir=output.parent) as temporary:
        rendered = Path(temporary) / "readme.pdf"
        subprocess.run(command + ["-o", str(rendered)], cwd=REPO, check=True)
        rendered.replace(output)
    print(f"README PDF: {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    build(parser.parse_args().output)
