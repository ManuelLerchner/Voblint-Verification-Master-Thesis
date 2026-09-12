"""The print inventory must neither omit helpers nor duplicate nested sessions."""

import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import gen_pdf_session
import build_readme_pdf


class PdfInventoryTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.repo = Path(self.directory.name)
        self.override = patch.object(gen_pdf_session, "REPO", self.repo)
        self.override.start()
        self.addCleanup(self.override.stop)
        (self.repo / "ROOTS").write_text("src/Base\nsrc/Base/Child\n")
        base = self.repo / "src/Base"
        (base / "generated").mkdir(parents=True)
        (base / "Child").mkdir()
        (base / "ROOT").write_text(
            'session Voblint_Base in "." = HOL +\n'
            '  directories\n    "generated"\n'
            '  theories\n    Entry\n')
        (base / "Child/ROOT").write_text(
            'session Voblint_Child in "." = Voblint_Base +\n'
            '  theories\n    Child\n')
        for name in ["Entry", "Helper", "generated/Assembly", "Child/Child"]:
            (base / (name + ".thy")).touch()

    def test_helpers_generated_and_nested_theories_are_all_included_once(self):
        sessions = gen_pdf_session.inventory()
        self.assertEqual(
            [(s["name"], [t["name"] for t in s["theories"]]) for s in sessions],
            [("Voblint_Base", ["Entry", "Assembly", "Helper"]),
             ("Voblint_Child", ["Child"])])

    def test_unowned_theory_blocks_an_incomplete_pdf(self):
        (self.repo / "src/Orphan.thy").touch()
        with self.assertRaisesRegex(ValueError, "outside session search paths"):
            gen_pdf_session.inventory()

    def test_missing_root_entry_blocks_generation(self):
        (self.repo / "src/Base/Entry.thy").unlink()
        with self.assertRaisesRegex(ValueError, "Unresolved theories"):
            gen_pdf_session.inventory()

    def test_colliding_latex_names_are_rejected(self):
        (self.repo / "src/Base/Child/Helper.thy").touch()
        with self.assertRaisesRegex(ValueError, "Duplicate LaTeX basename"):
            gen_pdf_session.inventory()

    def test_variants_preserve_imports_and_select_only_intended_examples(self):
        sessions = gen_pdf_session.inventory() + [{
            "name": "Voblint_Examples",
            "theories": [
                {"name": "Example_End_To_End_Certificate",
                 "path": "src/Examples/Capstone/Example_End_To_End_Certificate.thy"},
                {"name": "Voblint", "path": "src/Examples/Capstone/Voblint.thy"},
            ],
        }, {
            "name": "Voblint_Examples_Sign",
            "theories": [{"name": "Example_Sign", "path": "src/Examples/Sign/Example_Sign.thy"}],
        }]
        (self.repo / "document").mkdir()
        (self.repo / "document/root.tex").write_text("template")
        main, full = self.repo / "main", self.repo / "full"
        with patch.object(gen_pdf_session, "inventory", return_value=sessions):
            gen_pdf_session.generate(main)
            gen_pdf_session.generate(full, include_examples=True)
        main_root = (main / "ROOT").read_text()
        full_root = (full / "ROOT").read_text()
        self.assertEqual(
            main_root.split('  document_theories')[0].replace('"document=', '"document-full='),
            full_root.split('  document_theories')[0])
        self.assertNotIn("document_tags", main_root)
        self.assertIn('document_variants = "document=+proof,+ML,+invisible"', main_root)
        self.assertIn('    "readme.pdf"', main_root)
        self.assertIn('"Voblint_Examples_Sign.Example_Sign"', main_root)
        main_contents = (main / "document/contents.tex").read_text()
        full_contents = (full / "document/contents.tex").read_text()
        self.assertNotIn(r"\input{Example_Sign.tex}", main_contents)
        self.assertNotIn(r"\input{Voblint.tex}", main_contents)
        self.assertEqual(main_contents.count(r"\input{Example_End_To_End_Certificate.tex}"), 1)
        self.assertIn(r"\appendix", main_contents)
        self.assertNotIn(r"\appendix", full_contents)
        for session in sessions:
            for theory in session["theories"]:
                self.assertEqual(full_contents.count(r"\input{" + theory["name"] + ".tex}"), 1)
        self.assertIn(r"\input{Entry.tex}", main_contents)
        self.assertIn(r"\input{Assembly.tex}", main_contents)
        for root, contents in [(main_root, main_contents), (full_root, full_contents)]:
            exports = root.split('  document_theories\n')[1].split('  document_files')[0]
            names = re.findall(r'"[^".]+\.([^".]+)"', exports)
            inputs = re.findall(r'\\input\{([^}]+)\.tex\}', contents)
            self.assertCountEqual(names, inputs)
        main_exports = main_root.split('  document_theories\n')[1].split('  document_files')[0]
        self.assertNotIn('Voblint_Examples_Sign.Example_Sign', main_exports)
        self.assertIn('Voblint_Base.Entry', main_exports)
        self.assertIn('Voblint_Examples.Example_End_To_End_Certificate', main_exports)

    def test_missing_certificate_is_reported(self):
        with self.assertRaisesRegex(ValueError, "certificate appendix"):
            gen_pdf_session.presentation(gen_pdf_session.inventory())


class ReadmeBuildTests(unittest.TestCase):
    def test_failed_render_preserves_previous_pdf(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "readme.pdf"
            output.write_bytes(b"previous PDF")
            with patch.object(shutil, "which", return_value="tool"), \
                 patch.object(subprocess, "check_output", side_effect=["/isabelle", "--syntax-highlighting"]), \
                 patch.object(subprocess, "run", side_effect=subprocess.CalledProcessError(3, "pandoc")) as run:
                with self.assertRaises(subprocess.CalledProcessError):
                    build_readme_pdf.build(output)
            self.assertEqual(output.read_bytes(), b"previous PDF")


@unittest.skipUnless(shutil.which("pandoc"), "Pandoc is required for README conversion")
class ReadmeConversionTests(unittest.TestCase):
    def test_github_content_survives_print_conversion(self):
        source = '''<img src="https://github.com/user-attachments/assets/banner" alt="Banner">

# Guide

[Source](src/Example.thy)

[![CI](https://example.org/badge.svg)](https://example.org/ci)

<p><img src="docs/figure.png" alt="Local figure"><br>Gallery caption</p>

<details><summary>Exact theorem</summary>

```isabelle
lemma example: "x = x" by simp
```

</details>

| Name | Meaning |
| --- | --- |
| `long_identifier` | A description that needs a wrapping column. |
'''
        converted = subprocess.check_output([
            "pandoc", "--from=gfm", "--to=latex", "--no-highlight",
            "--lua-filter", str(Path(__file__).resolve().parents[1] / "scripts/pdf_readme.lua"),
        ], input=source, text=True)
        self.assertIn('/blob/main/src/Example.thy', converted)
        self.assertIn('https://example.org/ci', converted)
        self.assertIn('badge.svg', converted)
        self.assertIn('https://github.com/user-attachments/assets/banner', converted)
        self.assertIn('height=4mm', converted)
        self.assertIn('docs/figure.png', converted)
        self.assertIn('Gallery caption', converted)
        self.assertIn('Exact theorem', converted)
        self.assertIn('lemma example:', converted)
        self.assertIn('\\allowbreak', converted)
        self.assertIn('0.3600', converted)


if __name__ == "__main__":
    unittest.main()
