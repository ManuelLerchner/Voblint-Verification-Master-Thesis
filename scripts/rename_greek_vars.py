#!/usr/bin/env python3
"""Replace ASCII Greek variable names with Isabelle symbol escapes in .thy files.

Renames:
  pi    -> \\<Pi>    (capital: avoids clash with HOL.pi :: real)
  sigma -> \\<nu>    (\\<sigma> clashes with TD_side record field; nu is free)
  gamma -> \\<gamma>
  rho   -> \\<rho>

Only standalone identifiers are replaced.  Compound names (gamma_state,
sigma_c, to_imp2_pi, pi', rho') and already-escaped forms (\\<sigma>c) are
left untouched.

Usage:
    rename_greek_vars.py FILE...
    rename_greek_vars.py --dry-run FILE...

Run normalize_isabelle_ascii.py on the same files afterwards, then
open_file in jEdit to resync the buffer.
"""
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Replacement rules.
#
# Pattern design:
#   (?<!\\<)        — not preceded by \< (already inside an Isabelle escape)
#   (?<![a-zA-Z0-9_'])  — not preceded by word char or apostrophe (compound id)
#   <name>
#   (?![a-zA-Z0-9_'])   — not followed by word char or apostrophe (pi', sigma_c …)
# ---------------------------------------------------------------------------

def _pat(name: str) -> re.Pattern:
    return re.compile(
        r"(?<!\\<)(?<![a-zA-Z0-9_'])" + re.escape(name) + r"(?![a-zA-Z0-9_'])"
    )


RULES: list[tuple[re.Pattern, str]] = [
    (_pat("pi"),    r"\\<Pi>"),
    (_pat("sigma"), r"\\<nu>"),
    (_pat("gamma"), r"\\<gamma>"),
    (_pat("rho"),   r"\\<rho>"),
]


def rename(path: Path, dry_run: bool = False) -> int:
    text = path.read_text(encoding="utf-8")
    out = text
    for pattern, repl in RULES:
        out = pattern.sub(repl, out)
    if out == text:
        return 0
    if not dry_run:
        path.write_text(out, encoding="utf-8")
    return sum(len(pattern.findall(text)) for pattern, _ in RULES)


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    dry_run = "--dry-run" in argv
    args = [a for a in argv[1:] if not a.startswith("--")]
    total = 0
    for arg in args:
        p = Path(arg)
        if not p.is_file() or p.suffix != ".thy":
            continue
        n = rename(p, dry_run=dry_run)
        if n:
            tag = " [dry-run]" if dry_run else ""
            print(f"{p}: {n} replacement(s){tag}")
            total += 1
    if total == 0:
        print("No changes.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
