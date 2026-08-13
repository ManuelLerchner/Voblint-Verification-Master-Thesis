#!/usr/bin/env python3
"""Reject Isabelle .thy files containing unicode symbols.

Batch `isabelle build` rejects unicode tokens that I/Q tolerates,
so we keep .thy sources ASCII-only. Run from pre-commit hook.

Usage: check_isabelle_ascii.py FILE...
Exits 1 if any file contains non-ASCII bytes outside comments,
listing the offending lines with suggested ASCII replacements.
"""
import re
import sys
from pathlib import Path

# Common Isabelle unicode -> ASCII mappings. Extend as needed.
REPL = {
    "⟹": r"\<Longrightarrow>",
    "⇒": r"\<Rightarrow>",
    "⟶": r"\<longrightarrow>",
    "→": r"\<rightarrow>",
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
    "⟨": r"\<langle>",
    "⟩": r"\<rangle>",
    "⟦": r"\<lbrakk>",
    "⟧": r"\<rbrakk>",
    "↦": r"\<mapsto>",
    "←": r"\<leftarrow>",
    "⤜": r"\<bind>",
    "∷": r"::",
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

# Strip Isabelle (* ... *) comments (non-nested approximation) before scanning.
COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.DOTALL)


def scan(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    stripped = COMMENT_RE.sub(lambda m: " " * len(m.group(0)), text)
    issues = []
    for lineno, line in enumerate(stripped.splitlines(), 1):
        for ch in line:
            if ord(ch) > 127:
                hint = REPL.get(ch, f"<U+{ord(ch):04X}>")
                issues.append(f"{path}:{lineno}: non-ASCII {ch!r} -> {hint}")
                break
    return issues


def main(argv: list[str]) -> int:
    failures: list[str] = []
    for arg in argv[1:]:
        p = Path(arg)
        if not p.is_file() or p.suffix != ".thy":
            continue
        failures.extend(scan(p))
    if failures:
        print("Isabelle .thy files must be ASCII-only "
              "(outside comments). Replace these symbols:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
