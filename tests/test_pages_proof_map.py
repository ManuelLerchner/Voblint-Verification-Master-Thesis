"""Check the map preserves entity identity, reference edges, and HTML anchors."""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from pages_proof_map import package


class ProofMapTests(unittest.TestCase):
    def test_interpretation_keeps_identity_and_links_generic_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            html = root / "Voblint" / "Test" / "Demo.html"
            html.parent.mkdir(parents=True)
            html.write_text(
                '<span class="command">locale</span>'
                '<span id="Demo.base|locale">base</span>'
                '<span class="command"><span id="Demo.base.answer|fact">'
                "definition</span></span>"
                '<span class="command"><span id="Demo.instance.answer|fact">'
                "global_interpretation</span></span>"
                '<a href="#Demo.base|locale">base</a>'
            )
            raw = {
                key: {"theory": "Demo", "deps": []}
                for key in (
                    "locale:Demo.base",
                    "thm:Demo.base.answer",
                    "thm:Demo.instance.answer",
                )
            }
            data = package(raw, root, set())
            location = data["locations"]["thm:Demo.instance.answer"]
            self.assertEqual(location["kind"], "interpretation")
            self.assertEqual(
                data["nodes"][location["generic"]][0], "thm:Demo.base.answer"
            )
            self.assertTrue(all(n[4] for n in data["nodes"]))
            self.assertNotIn("thm:Demo.base.answer", data["locations"])

    def test_entities_edges_and_verified_anchor_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            html = root / "Voblint" / "Voblint_Test" / "Demo.html"
            html.parent.mkdir(parents=True)
            html.write_text(
                '<span id="Demo.result|fact"></span><span id="Demo.f|const"></span>'
            )
            raw = {
                "thm:Demo.result": {
                    "theory": "Demo",
                    "deps": ["const:Demo.f", "const:HOL.Trueprop", "const:Demo.f"],
                },
                "const:Demo.f": {"theory": "Demo", "deps": ["const:Demo.f"]},
                "thm:Demo.generated": {"theory": "Demo", "deps": []},
            }
            data = package(raw, root, {"Demo.result|fact"}, {"Demo": "Voblint_Test"})
            self.assertEqual(
                data["theories"],
                [["Demo", "Voblint_Test", "Voblint/Voblint_Test/Demo.html"]],
            )
            by_id = {node[0]: (i, node) for i, node in enumerate(data["nodes"])}
            fact = by_id["thm:Demo.result"][1]
            self.assertEqual(fact[2], [by_id["const:Demo.f"][0]])
            self.assertEqual(fact[3:], [1, True, True])
            self.assertEqual(by_id["const:Demo.f"][1][2], [])
            self.assertFalse(by_id["thm:Demo.generated"][1][4])
            self.assertEqual(set(by_id), set(raw))

    def test_missing_html_fails_instead_of_dropping_entities(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "missing.*Demo"):
                package(
                    {"thm:Demo.result": {"theory": "Demo", "deps": []}},
                    Path(directory),
                    set(),
                )

    def test_stale_session_copy_does_not_override_current_owner(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for session in ("Voblint_Old", "Voblint_Current"):
                path = root / "Voblint" / session / "Demo.html"
                path.parent.mkdir(parents=True)
                path.write_text('<span id="Demo.result|fact"></span>')
            data = package(
                {"thm:Demo.result": {"theory": "Demo", "deps": []}},
                root,
                set(),
                {"Demo": "Voblint_Current"},
            )
            self.assertEqual(len(data["theories"]), 1)
            self.assertEqual(data["theories"][0][1], "Voblint_Current")

    def test_grouped_session_wins_over_stale_unsorted_copy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for group in ("Unsorted", "Voblint"):
                path = root / group / "Voblint_CFG" / "CFG_Def.html"
                path.parent.mkdir(parents=True)
                path.write_text('<span id="CFG_Def.call_action.nchotomy|fact"></span>')
            data = package(
                {"thm:CFG_Def.call_action.nchotomy": {"theory": "CFG_Def", "deps": []}},
                root,
                set(),
                {"CFG_Def": "Voblint_CFG"},
            )
            self.assertEqual(data["theories"][0][2], "Voblint/Voblint_CFG/CFG_Def.html")
            self.assertTrue(data["nodes"][0][4])


if __name__ == "__main__":
    unittest.main()
