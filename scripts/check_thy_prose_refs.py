#!/usr/bin/env python3
"""Check Isabelle prose references and document-rendering safety.

Isabelle checks ``\\<^const>`` and ``@{thm ...}`` antiquotations against the
theory context, so a rename breaks the build. It does not check a plain
``\\<open>name\\<close>`` cartouche, which is how most prose in this tree cites a
constant or lemma -- and there is no short checked antiquotation for a fact
name that does not also print the whole statement. Plain cartouches are
therefore useful for prose references, and this check keeps them honest.

A reference is reported when the identifier appears nowhere in any .thy under
src/ or vendor/ outside prose. That is deliberately conservative: locale-local
names, ML identifiers, and metavariables all resolve somewhere, so the false
positives are few and the ones that remain are listed in ALLOWED below.

The check also guards the Isabelle document build against raw underscores in
ordinary document prose. Such underscores reach LaTeX unescaped and can produce
errors such as "Missing $ inserted". Isabelle symbols, antiquotations, and
nested cartouches are excluded because Isabelle renders those itself.

The LaTeX-safety check follows the same default theory selection as
``pixi run isabelle-pdf-build``: ordinary examples are excluded, except for the
end-to-end certificate appendix.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from gen_pdf_session import inventory, presentation

REPO = Path(__file__).resolve().parent.parent
OPEN, CLOSE = r"\<open>", r"\<close>"

# Names that are deliberately not Voblint constants.
ALLOWED = {
    # Goblint's own vocabulary, cited for comparison.
    "id_binary_log",
    "id_binary_pred",
    "id_unary_log",
    # Metavariable placeholders: X stands for a domain name.
    "bfilter_X_st",
    "branch_X_st_for",
    # A solver-menu label: `STR ''warrow_per_origin''` in Solver_Menu's table,
    # a string literal rather than an identifier.
    "warrow_per_origin",
    # Deliberately names something that does *not* exist -- Parity_Exec explains
    # that its branch transfer is the identity, so there is no such constant to
    # generalize.
    "branch_parity_st_for",
}

PROSE_KW = re.compile(
    r"\b(text|txt|section|subsection|subsubsection|paragraph|chapter)\b\s*"
)
REF = re.compile(re.escape(OPEN) + r"([a-z][A-Za-z0-9_']*)" + re.escape(CLOSE))
IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*")

# Isabelle encoded/control symbols, for example:
#
#   \<^theory_text>
#   \<^type>
#   \<^bold>
#
# OPEN and CLOSE also match this general shape, so callers must test them first.
ISABELLE_SYMBOL = re.compile(r"\\<[^>\n]+>")


def strip_prose(text: str) -> str:
    """Return `text` with comments and prose blocks removed."""
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)

    out: list[str] = []
    i = 0
    n = len(text)

    while i < n:
        m = PROSE_KW.match(text, i)

        if m and text.startswith(OPEN, m.end()):
            depth = 0
            k = m.end()

            while k < n:
                if text.startswith(OPEN, k):
                    depth += 1
                    k += len(OPEN)
                elif text.startswith(CLOSE, k):
                    depth -= 1
                    k += len(CLOSE)
                else:
                    k += 1

                if depth == 0:
                    break

            i = k
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def skip_antiquotation(text: str, i: int) -> int:
    """Skip an old-style Isabelle @{...} antiquotation."""
    assert text.startswith("@{", i)

    depth = 1
    i += 2
    n = len(text)

    while i < n and depth:
        # Antiquotations may themselves contain cartouches.
        if text.startswith(OPEN, i):
            cartouche_depth = 1
            i += len(OPEN)

            while i < n and cartouche_depth:
                if text.startswith(OPEN, i):
                    cartouche_depth += 1
                    i += len(OPEN)
                elif text.startswith(CLOSE, i):
                    cartouche_depth -= 1
                    i += len(CLOSE)
                else:
                    i += 1

            continue

        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1

        i += 1

    return i


def raw_prose_underscore_lines(text: str) -> set[int]:
    """Return lines containing raw '_' in outer Isabelle document prose.

    Nested cartouches, Isabelle symbols, and antiquotations are rendered by
    Isabelle and therefore do not expose their source spelling directly to
    LaTeX. Only underscores in the surrounding ordinary prose are unsafe.
    """
    bad: set[int] = set()
    i = 0
    n = len(text)

    while i < n:
        m = PROSE_KW.match(text, i)

        if not m or not text.startswith(OPEN, m.end()):
            i += 1
            continue

        depth = 0
        k = m.end()

        while k < n:
            # These must precede the generic Isabelle-symbol case below.
            if text.startswith(OPEN, k):
                depth += 1
                k += len(OPEN)
                continue

            if text.startswith(CLOSE, k):
                depth -= 1
                k += len(CLOSE)

                if depth == 0:
                    break

                continue

            # Skip encoded/control symbols such as \<^theory_text>. The
            # underscore in the symbol name is not literal document prose.
            symbol = ISABELLE_SYMBOL.match(text, k)
            if symbol:
                k = symbol.end()
                continue

            # Old-style antiquotation, for example:
            #
            #   @{const sorted_list_of_set}
            #
            # Isabelle renders its contents, so underscores there are safe.
            if depth == 1 and text.startswith("@{", k):
                k = skip_antiquotation(text, k)
                continue

            # Nested cartouches are formal/marked-up Isabelle text. Only a raw
            # underscore in the surrounding outer prose reaches LaTeX
            # unprotected.
            if depth == 1 and text[k] == "_":
                bad.add(text.count("\n", 0, k) + 1)

            k += 1

        i = k

    return bad


def default_document_sources() -> set[Path]:
    """Return theories rendered by the default Isabelle PDF build."""
    return {
        REPO / theory["path"]
        for session in presentation(inventory(), include_examples=False)
        for theory in session["theories"]
    }


def main() -> int:
    sources = {
        path: path.read_text(errors="ignore")
        for root in ("src", "vendor")
        for path in (REPO / root).rglob("*.thy")
    }

    if not sources:
        print(
            "check_thy_prose_refs: no .thy files found",
            file=sys.stderr,
        )
        return 1

    # A name defined only in the vendored solver resolves nowhere when the
    # submodule is absent, so every prose reference to one is reported as
    # dangling. That looks like a dozen broken renames rather than a missing
    # checkout, so say which it is.
    if not any(
        str(path).startswith(str(REPO / "vendor" / "td-verification"))
        for path in sources
    ):
        print(
            "check_thy_prose_refs: vendor/td-verification has no .thy "
            "files -- the submodule is not checked out.\n"
            "Prose naming a vendored constant would be reported as dangling. "
            "Run: git submodule update --init --depth 1 vendor/td-verification",
            file=sys.stderr,
        )
        return 1

    # ------------------------------------------------------------------
    # Collect identifiers that actually occur outside src/ prose.
    # ------------------------------------------------------------------

    defined: set[str] = set()

    for path, text in sources.items():
        body = strip_prose(text) if str(path).startswith(str(REPO / "src")) else text
        defined |= set(IDENT.findall(body))

    # ------------------------------------------------------------------
    # LaTeX safety
    #
    # Check exactly the theories rendered by the default PDF presentation.
    # This deliberately does not turn historical example prose into a
    # pre-commit blocker when those examples are absent from the PDF.
    # ------------------------------------------------------------------

    unsafe_prose: list[str] = []

    for path in sorted(default_document_sources()):
        text = sources.get(path)
        if text is None:
            # inventory() should already guarantee that project theories exist,
            # but do not turn this secondary check into an unrelated crash.
            continue

        lines = text.splitlines()

        for line_no in sorted(raw_prose_underscore_lines(text)):
            line = lines[line_no - 1].strip()
            unsafe_prose.append(f"{path.relative_to(REPO)}:{line_no}: {line}")

    if unsafe_prose:
        print(
            "check_thy_prose_refs: raw '_' in Isabelle document prose "
            "would be passed unescaped to LaTeX:"
        )

        for site in unsafe_prose:
            print(f"  {site}")

        print()
        print(
            r"Wrap identifiers containing '_' in \<open>...\<close> "
            "or use an Isabelle document antiquotation."
        )
        return 1

    # ------------------------------------------------------------------
    # Dangling prose references
    # ------------------------------------------------------------------

    dangling: dict[str, list[str]] = {}

    for path, text in sources.items():
        if not str(path).startswith(str(REPO / "src")):
            continue

        for match in REF.finditer(text):
            name = match.group(1)

            if name.count("_") < 2 or name in defined or name in ALLOWED:
                continue

            if name.endswith(("_def", "_defs", "_simps")):
                continue

            line = text.count("\n", 0, match.start()) + 1
            dangling.setdefault(name, []).append(f"{path.relative_to(REPO)}:{line}")

    if dangling:
        print(
            f"check_thy_prose_refs: {len(dangling)} prose reference(s) name "
            "something that no longer exists:"
        )

        for name in sorted(dangling):
            print(f"  {name}")

            for site in sorted(set(dangling[name])):
                print(f"      {site}")

        print()
        print(
            "Rename the reference, or add it to ALLOWED if it deliberately "
            "names something outside this tree."
        )
        return 1

    print("check_thy_prose_refs: prose references and LaTeX safety OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
