"""Resolve thesis citations against the HTML export's repository layout."""

import json
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def test_write_and_check_exported_html(tmp_path):
    scripts = tmp_path / "scripts"
    scripts.mkdir()
    checker = scripts / "check_thesis_links.py"
    shutil.copyfile(REPO / "scripts/check_thesis_links.py", checker)
    thesis = tmp_path / "thesis"
    thesis.mkdir()
    (thesis / "example.typ").write_text('isatype("pp")\n')
    page = tmp_path / "build/isabelle-html/Voblint/Voblint_CFG/CFG_Def.html"
    page.parent.mkdir(parents=True)
    page.write_text('<span class="entity_def" id="CFG_Def.pp|type"></span>')

    for mode in ("--write", "--check"):
        result = subprocess.run(
            [sys.executable, str(checker), mode, "--base", "https://example.org/"],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stdout + result.stderr

    payload = json.loads((thesis / "shared/generated/links.json").read_text())
    assert payload["links"] == {
        "type:pp": "Voblint/Voblint_CFG/CFG_Def.html#CFG_Def.pp%7Ctype"
    }
