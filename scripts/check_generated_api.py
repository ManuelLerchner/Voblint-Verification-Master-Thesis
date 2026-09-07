#!/usr/bin/env python3
"""Fail when handwritten OCaml names something the export no longer exposes.

The generated OCaml is one module, ``Generated``, and its *signature* is
decided by the export root list in ``src/Executable_Surface/Codegen/Export/Voblint_Codegen.thy``:
Isabelle marks a constant ``Private`` unless a root reaches it, and marks a
datatype ``Opaque`` -- name visible, constructors hidden, so unmatchable --
unless a root names the constructors themselves.

That used to matter less. Under the old per-theory module split, a symbol also
went public whenever a *sibling generated module* called it, and the
handwritten OCaml rode along on those incidental exposures. Merging into one
module removed every boundary, so the root list is now the only thing putting
a name in the signature -- and a missing root breaks an OCaml consumer, not
the Isabelle build.

Two checks, against the checked-in export:

* qualified uses (``Voblint_CLI.Generated.foo``, or through a ``module C =``
  alias) must resolve in the signature -- exact, no guessing;
* a consumer that ``open``s the module must not use a name the generated
  implementation defines but the signature withholds. That one is a heuristic:
  it only reports names the export actually has and hides, and it skips
  anything the file binds itself.

Neither replaces compiling the consumers, which is the exact check and which
``cli-build``, ``codegen-regression`` and ``property-build`` already run. This
runs in a second, needs no OCaml toolchain, and names the missing export root.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
GENERATED = REPO / "codegen" / "generated" / "ml" / "Voblint_CLI.ml"
EXPORT_SOURCE = "src/Executable_Surface/Codegen/Export/Voblint_Codegen.thy"

MODULE = "Generated"

# Handwritten OCaml that links against the export. Generated or copied files
# are excluded: cli/Voblint_CLI.ml and tests/property/Voblint_CLI.ml are build
# copies of the export itself, and vimp_parser.ml/vimp_lexer.ml come from
# menhir/ocamllex at build time.
CONSUMERS = [
    "cli/main.ml",
    "cli/dot_render.ml",
    "cli/html_report.ml",
    "cli/vimp_frontend.ml",
    "cli/vimp_positions.ml",
    "cli/vimp_parser.mly",
    "codegen/regression/ocaml/main.ml",
    "tests/property/ast_driver.ml",
]

IDENT = r"[a-z_][A-Za-z0-9_']*"
CTOR = r"[A-Z][A-Za-z0-9_']*"


def split_module(text: str) -> tuple[str, str]:
    """Return the signature and implementation bodies of the export module."""
    m = re.search(
        rf"^module {MODULE} : sig\n(.*?)^end = struct\n(.*?)^end;;",
        text,
        re.S | re.M,
    )
    if not m:
        raise SystemExit(
            f"check_generated_api: no `module {MODULE}` in {GENERATED}; "
            f"has {EXPORT_SOURCE} lost its `module_name {MODULE}`?"
        )
    return m.group(1), m.group(2)


def signature_names(sig: str) -> set[str]:
    """Everything a client outside the module may name."""
    names = set(re.findall(rf"^\s*val ({IDENT})", sig, re.M))
    names |= set(re.findall(rf"^\s*type (?:\S+ )*?({IDENT})\b", sig, re.M))
    # Constructors are nameable only where the type is transparent, i.e. the
    # declaration carries its `= A | B of ...` right here.
    for decl in re.findall(r"^\s*type [^\n]*=(.*?)(?=^\s*(?:type|val)\s|\Z)", sig, re.S | re.M):
        names |= set(re.findall(rf"\b({CTOR})\b", decl))
    return names


def implementation_names(impl: str) -> set[str]:
    """Everything the module defines, exposed or not."""
    names = set(re.findall(rf"^let (?:rec )?({IDENT})", impl, re.M))
    names |= set(re.findall(rf"^type (?:\S+ )*?({IDENT})\s*=", impl, re.M))
    for decl in re.findall(r"^type [^\n]*=(.*?);;", impl, re.S | re.M):
        names |= set(re.findall(rf"\b({CTOR})\b", decl))
    return names


def aliases(text: str) -> list[str]:
    """Module paths a file uses to reach the export, longest first."""
    found = [f"Voblint_CLI.{MODULE}"]
    found += re.findall(rf"^module ({CTOR}) = Voblint_CLI\.{MODULE}\s*$", text, re.M)
    return sorted(found, key=len, reverse=True)


def strip_noise(text: str) -> str:
    """Drop comments and string literals: prose mentions a lot of these names."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def locally_bound(text: str) -> set[str]:
    """Names the file itself binds, so an `open` cannot be blamed for them.

    Deliberately generous: a false "bound" only costs a missed report, while a
    false "unbound" makes the check cry wolf over a pattern variable and gets
    the whole thing disabled.
    """
    bound = set(re.findall(rf"\b(?:let|and) (?:rec )?({IDENT})", text))
    bound |= set(re.findall(rf"^module ({CTOR})", text, re.M))
    # Binding positions that name several identifiers at once: a `let`/`fun`
    # parameter list or tuple pattern, and every `| pattern ->` arm.
    for segment in re.findall(r"\b(?:let|and) [^=\n]*=", text):
        bound |= set(re.findall(rf"\b({IDENT})", segment))
    for segment in re.findall(r"\bfun\b(.*?)->", text, re.S):
        bound |= set(re.findall(rf"\b({IDENT})", segment))
    for segment in re.findall(r"^\s*\|(.*?)->", text, re.S | re.M):
        bound |= set(re.findall(rf"\b({IDENT})", segment))
    return bound


def main() -> int:
    if not GENERATED.exists():
        print(f"check_generated_api: {GENERATED} not found; run `pixi run codegen`")
        return 1

    sig, impl = split_module(GENERATED.read_text(errors="ignore"))
    exposed = signature_names(sig)
    hidden = implementation_names(impl) - exposed

    problems: list[tuple[str, str, str]] = []

    for rel in CONSUMERS:
        path = REPO / rel
        if not path.exists():
            continue
        text = strip_noise(path.read_text(errors="ignore"))

        for alias in aliases(text):
            for name in re.findall(rf"\b{re.escape(alias)}\.({IDENT}|{CTOR})", text):
                if name not in exposed:
                    why = "hidden by the export" if name in hidden else "not in the export"
                    problems.append((rel, f"{alias}.{name}", why))

        if re.search(rf"^open Voblint_CLI\.{MODULE}\s*$", text, re.M):
            bound = locally_bound(text)
            for name in sorted(hidden - bound):
                if re.search(rf"(?<![\w.']){re.escape(name)}(?![\w'])", text):
                    problems.append((rel, name, "used unqualified, hidden by the export"))

    if not problems:
        print(
            f"check_generated_api: {len(CONSUMERS)} consumers resolve against "
            f"{MODULE} ({len(exposed)} names exposed)"
        )
        return 0

    print("check_generated_api: handwritten OCaml names what the export hides:")
    seen: set[tuple[str, str]] = set()
    for rel, name, why in problems:
        if (rel, name) in seen:
            continue
        seen.add((rel, name))
        print(f"  {rel}: {name} -- {why}")
    print()
    print(
        f"Add the constant, or a datatype's constructors, to the export roots in "
        f"{EXPORT_SOURCE} and re-run `pixi run codegen`. A name the export "
        "reaches but no root names is emitted without a signature entry, and a "
        "datatype no root names stays abstract and cannot be matched on."
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
