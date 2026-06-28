#!/usr/bin/env python3
"""Rename pruns_to -> pcompletes in Isabelle sources and apply phase-3 patches."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"

RENAME_FILES = [
    SRC / "IMP2" / "IMP2_Proc.thy",
    SRC / "IMP2" / "IMP2_Bridge.thy",
    SRC / "IMP2" / "IMP2_VCG_Example.thy",
    SRC / "Formalization" / "Examples" / "Example_Inc_Proc.thy",
    SRC / "Formalization" / "Examples" / "Example_Proc_Call.thy",
    SRC / "Formalization" / "Voblint.thy",
]

GLOSSARY = ROOT / "docs" / "GLOSSARY.md"

PNO_STEP_BLOCK = r"""
definition pno_step :: "proc_table \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool" where
  "pno_step \<Pi> cfg \<longleftrightarrow>
     \<not> (\<exists>cfg'. pstep \<Pi> cfg cfg')"

lemma pfinal_imp_pno_step:
  assumes pf: "pfinal (c, s, frs)"
  shows "pno_step \<Pi> (c, s, frs)"
  using pf unfolding pno_step_def pfinal.simps
  by (auto elim!: SkipSE)

"""

PCOMPLETES_COMMENT = r"""(* A run of c from store s completes in t when it reaches a pfinal configuration
   whose store is t (Concrete Semantics: small-step termination to a good final cfg). *)"""


def rename_pruns_to(text: str) -> str:
    text = text.replace("pruns_to_", "pcompletes_")
    text = text.replace("pruns_to", "pcompletes")
    return text


def patch_imp2_proc(text: str) -> str:
    text = rename_pruns_to(text)

    text = text.replace(
        "definition pcompletes ::",
        PNO_STEP_BLOCK + "definition pcompletes ::",
        1,
    )

    text = text.replace(
        "(* A run of c from store s completes in t when it reaches a pfinal configuration\n"
        "   whose store is t. *)",
        PCOMPLETES_COMMENT,
        1,
    )

    text = text.replace(
        "lemma pcompletes_iff_reaches_pfinal:",
        "lemma pcompletes_iff_small_termination:",
        1,
    )

    old_iff = (
        "lemma pcompletes_iff_small_termination:\n"
        '  "pcompletes \\<Pi> c s t \\<longleftrightarrow>\n'
        '     (\\<exists>cfg. psteps \\<Pi> (c, s, []) cfg \\<and> pfinal cfg \\<and> fst (snd cfg) = t)"\n'
        "  unfolding pcompletes_def by auto\n"
    )
    new_iff = (
        "lemma pcompletes_iff_small_termination:\n"
        '  "pcompletes \\<Pi> c s t \\<longleftrightarrow>\n'
        '     (\\<exists>cfg. psteps \\<Pi> (c, s, []) cfg \\<and> pfinal cfg \\<and> fst (snd cfg) = t)"\n'
        "  unfolding pcompletes_def by auto\n"
        "\n"
        "lemma pcompletes_iff_reaches_pfinal[simp]:\n"
        '  "pcompletes \\<Pi> c s t \\<longleftrightarrow>\n'
        '     (\\<exists>cfg. psteps \\<Pi> (c, s, []) cfg \\<and> pfinal cfg \\<and> fst (snd cfg) = t)"\n'
        "  unfolding pcompletes_def by auto\n"
    )
    if old_iff not in text:
        raise SystemExit("pcompletes_iff_small_termination block not found in IMP2_Proc.thy")
    text = text.replace(old_iff, new_iff, 1)

    return text


def patch_imp2_bridge(text: str) -> str:
    text = rename_pruns_to(text)

    bridge_block = r"""
corollary big_step_imp_pcompletes:
  assumes run: "big_step (to_imp2_pi \<Pi>) (to_imp2_com c, S) T"
      and sp: "source_pi \<Pi>"
      and sc: "source_com c"
  shows "pcompletes \<Pi> c (proj0 S) (proj0 T)"
  using backward_sim[OF run sp refl sc] .

lemma ex_big_step_imp_ex_pcompletes:
  assumes sp: "source_pi \<Pi>"
      and sc: "source_com c"
      and run: "big_step (to_imp2_pi \<Pi>) (to_imp2_com c, S) T"
  shows "\<exists>t. pcompletes \<Pi> c (proj0 S) t"
  using big_step_imp_pcompletes[OF run sp sc] by blast

text \<open>
  Concrete Semantics equates big-step termination with reaching a final
  small-step configuration.  Here @{term pcompletes_iff_small_termination} is
  the small-step side (reach @{term pfinal}); @{term ex_big_step_imp_ex_pcompletes}
  is the big-to-small direction.  The converse (every @{term pcompletes} run
  comes from a @{term big_step}) is forward simulation (Track A, open).
\<close>

"""

    anchor = "theorem backward_sim:"
    if anchor not in text:
        raise SystemExit("backward_sim anchor not found in IMP2_Bridge.thy")
    if "big_step_imp_pcompletes" in text:
        return text
    after_backward = (
        "  using backward_sim_aux[OF sp bs refl cc sc] .\n\n"
        + bridge_block
    )
    text = text.replace(
        "  using backward_sim_aux[OF sp bs refl cc sc] .\n",
        after_backward,
        1,
    )
    return text


def patch_glossary(text: str) -> str:
    text = re.sub(
        r"\| `pruns_to`[^\n]*\n",
        "| `pcompletes`                                     | Procedural completion: `proc_table => com => store => store => bool`; reaches `pfinal`. See `pcompletes_iff_small_termination`. | `IMP2_Proc.thy` |\n",
        text,
        count=1,
    )
    if "`pfinal`" not in text:
        text = text.replace(
            "| `pstep`",
            "| `pfinal`                                       | Successful exit configuration: `SKIP` with empty frame stack.                                                                      | `IMP2_Proc.thy`   |\n| `pstep`",
            1,
        )
    return text


def main() -> int:
    proc_path = SRC / "IMP2" / "IMP2_Proc.thy"
    proc = proc_path.read_text()
    proc_path.write_text(patch_imp2_proc(proc))
    print(f"patched {proc_path.relative_to(ROOT)}")

    bridge_path = SRC / "IMP2" / "IMP2_Bridge.thy"
    bridge = bridge_path.read_text()
    bridge_path.write_text(patch_imp2_bridge(bridge))
    print(f"patched {bridge_path.relative_to(ROOT)}")

    for path in RENAME_FILES:
        if path in (proc_path, bridge_path):
            continue
        text = path.read_text()
        new = rename_pruns_to(text)
        if new != text:
            path.write_text(new)
            print(f"renamed in {path.relative_to(ROOT)}")

    if GLOSSARY.exists():
        g = GLOSSARY.read_text()
        ng = patch_glossary(g)
        if ng != g:
            GLOSSARY.write_text(ng)
            print(f"patched {GLOSSARY.relative_to(ROOT)}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
