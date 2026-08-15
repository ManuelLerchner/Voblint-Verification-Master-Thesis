#!/usr/bin/env python3
"""Convert Isabelle unicode symbols to ASCII forms in .thy files.

I/Q's editor sometimes serialises ASCII Isabelle tokens (e.g. ``\\<lambda>``)
back as their unicode renderings (``λ``). Batch ``isabelle build`` then
rejects the result with ``Inner lexical error``.  This script normalises the
file in place.

Usage:
    normalize_isabelle_ascii.py FILE...

After running, re-open the file in jEdit (I/Q ``open_file``) so the buffer
picks up the on-disk content.  Companion to ``check_isabelle_ascii.py``.
"""
import sys
from pathlib import Path

# Unicode -> ASCII Isabelle tokens.  Extend as needed; keep in sync with
# scripts/check_isabelle_ascii.py.
REPL = {
    "‹": r"\<open>",
    "›": r"\<close>",
    "⟨": r"\<langle>",
    "⟩": r"\<rangle>",
    "⟦": r"\<lbrakk>",
    "⟧": r"\<rbrakk>",
    "⦇": r"\<lparr>",
    "⦈": r"\<rparr>",
    "⟹": r"\<Longrightarrow>",
    "⇒": r"\<Rightarrow>",
    "⟶": r"\<longrightarrow>",
    "\u290f": r"\<longlongrightarrow>",  # I/Q CFG path arrow (RIGHTWARDS ARROW WITH TIP DOWNWARDS)
    "⟷": r"\<longleftrightarrow>",
    "↔": r"\<leftrightarrow>",
    "→": r"\<rightarrow>",
    "⊇": r"\<supseteq>",
    "⋀": r"\<And>",
    "∧": r"\<and>",
    "∨": r"\<or>",
    "¬": r"\<not>",
    "∈": r"\<in>",
    "∉": r"\<notin>",
    "≠": r"\<noteq>",
    "≤": r"\<le>",
    "≥": r"\<ge>",
    "⊆": r"\<subseteq>",
    "∪": r"\<union>",
    "∩": r"\<inter>",
    "∀": r"\<forall>",
    "∃": r"\<exists>",
    "…": r"\<dots>",
    "↦": r"\<mapsto>",
    "←": r"\<leftarrow>",
    "⤜": r"\<bind>",
    "≡": r"\<equiv>",
    "⊔": r"\<squnion>",
    "⊓": r"\<sqinter>",
    "λ": r"\<lambda>",
    "Π": r"\<Pi>",
    "σ": r"\<sigma>",
    "τ": r"\<tau>",
    "α": r"\<alpha>",
    "β": r"\<beta>",
    "γ": r"\<gamma>",
    "δ": r"\<delta>",
    "ε": r"\<epsilon>",
    "ρ": r"\<rho>",
    "ν": r"\<nu>",
    "×": r"\<times>",
    "·": r"\<cdot>",
    "∘": r"\<circ>",
    "∧": r"\<and>",
    "⊢": r"\<turnstile>",
    "⋃": r"\<Union>",
    "⋂": r"\<Inter>",
    "Δ": r"\<Delta>",
    "∇": r"\<nabla>",
    "⇘": r"\<^bsub>",
    "⇙": r"\<^esub>",
    "⇗": r"\<^bsup>",
    "⇖": r"\<^esup>",
}


def normalize(path: Path) -> int:
    """Rewrite path in place; return number of replacements made."""
    text = path.read_text(encoding="utf-8")
    out = text
    for u, a in REPL.items():
        out = out.replace(u, a)
    changed = len(out) - len(text)  # heuristic; counts byte delta
    if out != text:
        path.write_text(out, encoding="utf-8")
    return changed


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    total_files = 0
    for arg in argv[1:]:
        p = Path(arg)
        if not p.is_file() or p.suffix != ".thy":
            continue
        delta = normalize(p)
        if delta:
            print(f"{p}: normalised (+{delta} bytes)")
            total_files += 1
    if total_files == 0:
        print("No changes.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
