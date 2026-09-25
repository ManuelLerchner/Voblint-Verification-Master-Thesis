#!/usr/bin/env python3
"""Fail when the thesis names something the formalization does not define.

The thesis marks every reference to a real entity with a function that also
declares what kind of entity it is -- ``isathm``, ``isaconst``, ``isatype``,
``isalocale``, ``isasession``, ``isacmd``. That declaration is what makes
checking worth anything: a plain "does this identifier occur somewhere" test passes when a
lemma is downgraded to a definition or a locale is replaced by a class, which
is exactly the drift a reader would be misled by.

So each reference is resolved against the declaring command in the sources:

  isathm("X")      lemma / theorem / corollary / proposition named X
  isaconst("X")    definition / fun / abbreviation / primrec / inductive X
  isatype("X")     datatype / type_synonym / record X
  isalocale("X")   locale / class X
  isasession("X")  a session declared in some ROOT
  isacmd("X")      an Isabelle outer-syntax command (checked when
                   ISABELLE_HOME is reachable, skipped otherwise)

Three outcomes: resolved, missing (with a spelling suggestion), or -- the
interesting one -- found under a different command, reported as a deviation.

Usage: python3 scripts/check_thesis_refs.py [--thesis DIR]
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

import tomllib
from extract_definitions import find_matching_close, mask_comments_and_strings

REPO = Path(__file__).resolve().parent.parent

SKIP_PARTS = {".git", ".claude/worktrees", "_build", "docs/history"}


def active_path(path: Path) -> bool:
    """Ignore generated and auxiliary worktrees absent from CI checkouts."""
    rel = path.relative_to(REPO).as_posix()
    return not any(rel == part or rel.startswith(f"{part}/") for part in SKIP_PARTS)


# One kind per declaring command. A name may legitimately hold several kinds
# (an inductive predicate brings a constant and an induction rule), so the
# inventory maps name -> set of kinds.
KIND_COMMANDS = {
    "thm": ("lemma", "theorem", "corollary", "proposition", "schematic_goal"),
    "const": (
        "definition",
        "fun",
        "primrec",
        "abbreviation",
        "inductive",
        "inductive_set",
        "function",
        "partial_function",
        "lift_definition",
    ),
    "type": ("datatype", "type_synonym", "record", "typedef", "quotient_type"),
    "locale": ("locale", "class"),
}
COMMAND_KIND = {cmd: kind for kind, cmds in KIND_COMMANDS.items() for cmd in cmds}

# `record 'a domain_transfer =` and `datatype ('a, 'b) t = ...` put type
# parameters between the command and the name, so those are skipped first.
DECL = re.compile(
    r"^[ \t]*(?:qualified\s+)?("
    + "|".join(sorted(COMMAND_KIND, key=len, reverse=True))
    + r")\b\s+(?:(?:\([^)]*\)|'[A-Za-z][A-Za-z0-9_']*)\s+)*"
    + r"([A-Za-z][A-Za-z0-9_']*)",
    re.M,
)
# `lemma foo:` and `lemma foo [simp]:` both declare foo; `lemma "..."` does not.
ANON = re.compile(r'^\s*(?:lemma|theorem|corollary)\s+["\\]', re.M)
# `  field :: "type"` lines inside a record / datatype body.
FIELD = re.compile(r"^\s+([a-z][A-Za-z0-9_']*)\s*::", re.M)

# A datatype's constructors are constants too, and prose cites them as often as
# it cites the type: `EA_Assign`, `Root`, `CallEdge`.  They are capitalised and
# introduced after `=` or after a `|`, which may sit mid-line when several
# nullary constructors share one (`Sign_Analysis | Interval_Analysis | ...`).
CONSTRUCTOR = re.compile(r"(?:=|\|)\s*([A-Z][A-Za-z0-9_']*)")

# Bound bodies by commands, not indentation: constructors may start a line,
# while the next declaration may itself be indented inside a context.
BODY_END = re.compile(
    r"^[ \t]*(?:"
    + "|".join(COMMAND_KIND)
    + r"|begin|end|context|instantiation|instance|interpretation|sublocale"
    + r"|text|text_raw|chapter|section|subsection|subsubsection|paragraph)\b",
    re.M,
)
CLASS_FIX = re.compile(r"\b(?:fixes|and)\s+([A-Za-z][A-Za-z0-9_']*)\s*::")
# `assumes gamma_mono: "..."` or `and narrow_le [simp]: "..."` in a locale or
# class body names a fact of that locale, which prose cites as a law.
ASSUMPTION = re.compile(
    r"\b(?:assumes|and)\s+([A-Za-z][A-Za-z0-9_']*)\s*(?:\[[^\]]*\])?\s*:(?!:)"
)
# `Assign: "..."` or `| Call: "..."` in an inductive body names the fact
# `pstep.Call`, which a theorem statement cites.
RULE_LABEL = re.compile(r"^\s*(?:\|\s*)?([A-Za-z][A-Za-z0-9_']*)\s*:(?!:)", re.M)

TYPST_REF = re.compile(r"\bisa(thm|const|type|locale|session|cmd)\(\"([^\"]*)\"\)")

# The theorem environments in lib/theorems.typ carry the Isabelle name they
# state as `isa: "..."`, and render it in the margin.  That is a reference like
# any other and is checked the same way; it is not wrapped in an isa*() call
# only because the environment already knows it is a name.  The kind is left
# open, since a definition may name a constant, a type or a locale.
ISA_ARG = re.compile(r"\bisa:\s*\"([A-Za-z][A-Za-z0-9_.']*)\"")
# A definition environment also names the command that declares its entity
# (`cmd: "datatype"`), so the header says what kind of object it defines.
DEFINITION_ENV = re.compile(r"#definition\((.*?)\)\[", re.S)
CMD_ARG = re.compile(r"\bcmd:\s*\"([a-z_]+)\"")

# Names that deliberately do not resolve, with the reason.
ALLOWED = {
    # Goblint's own vocabulary, cited for comparison rather than claimed.
    "Spec",
    "assign",
    "ctx",
    "combine_env",
}


COMMAND_DECL = re.compile(r"command_keyword>\\<open>([A-Za-z0-9_']+)\\<close>")


def isabelle_home() -> Path | None:
    """The Isabelle distribution directory, or None when Isabelle is not reachable."""
    home = os.environ.get("ISABELLE_HOME")
    if not home:
        exe = shutil.which("isabelle")
        if exe:
            try:
                home = subprocess.run(
                    [exe, "getenv", "-b", "ISABELLE_HOME"],
                    capture_output=True,
                    text=True,
                    check=True,
                ).stdout.strip()
            except (subprocess.CalledProcessError, OSError):
                home = None
    if not home or not Path(home).is_dir():
        return None
    return Path(home)


def isabelle_commands() -> set[str] | None:
    """Outer-syntax command names, or None when Isabelle is not reachable."""
    home = isabelle_home()
    if home is None:
        return None
    names: set[str] = set()
    for sub in ("src/Pure", "src/HOL/Tools", "src/Tools"):
        for path in (home / sub).rglob("*"):
            if path.suffix in (".ML", ".thy") and path.is_file():
                names |= set(COMMAND_DECL.findall(path.read_text(errors="ignore")))
    return names or None


def build_inventory() -> tuple[
    dict[str, set[str]], set[str], set[str], dict[str, set[str]]
]:
    """Map every declared name to the kinds and commands it is declared with."""
    kinds: dict[str, set[str]] = defaultdict(set)
    declared_by: dict[str, set[str]] = defaultdict(set)
    # The background chapter cites HOL's own order and lattice classes, which
    # live in the top-level theories of the HOL session.
    home = isabelle_home()
    library = sorted((home / "src" / "HOL").glob("*.thy")) if home else []
    paths = [p for root in ("src", "vendor") for p in (REPO / root).rglob("*.thy")]
    for group in (paths, library):
        for path in group:
            original = path.read_text(errors="ignore")
            text = mask_comments_and_strings(original)
            # Cartouches contain documentation and terms, not declarations.
            # Preserve offsets/newlines while excluding their apparent commands.
            start = 0
            while (start := text.find("\\<open>", start)) != -1:
                end = find_matching_close(text, start)
                text = (
                    text[:start] + re.sub(r"[^\n]", " ", text[start:end]) + text[end:]
                )
                start = end
            for m in DECL.finditer(text):
                if ANON.match(original, m.start()):
                    continue
                kinds[m.group(2)].add(COMMAND_KIND[m.group(1)])
                declared_by[m.group(2)].add(m.group(1))
                stop = BODY_END.search(text, m.end())
                body = text[m.end() : stop.start() if stop else len(text)]
                # Selectors belong only to this declaration, not every later
                # indented type annotation or proof-local variable in the file.
                if m.group(1) in ("record", "datatype"):
                    for f in FIELD.finditer(body):
                        kinds[f.group(1)].add("const")
                if m.group(1) == "datatype":
                    for c in CONSTRUCTOR.finditer(body):
                        kinds[c.group(1)].add("const")
                    # Named selectors, `Call (ltr_caller: ltr) trace`.
                    for sel in re.finditer(r"\(([A-Za-z][A-Za-z0-9_']*)\s*:", body):
                        kinds[sel.group(1)].add("const")
                # Type-class parameters become overloaded global constants.
                # Arbitrary locale fixes do not declare such constants.
                if m.group(1) == "class":
                    for f in CLASS_FIX.finditer(body):
                        kinds[f.group(1)].add("const")
                if m.group(1) in ("locale", "class"):
                    for a in ASSUMPTION.finditer(body):
                        kinds[a.group(1)].add("thm")
                if m.group(1) in ("fun", "primrec", "function"):
                    kinds[f"{m.group(2)}.simps"].add("thm")
                if m.group(1) in ("inductive", "inductive_set"):
                    for r in RULE_LABEL.finditer(body):
                        kinds[f"{m.group(2)}.{r.group(1)}"].add("thm")

    # Without an Isabelle installation the HOL sources are not readable. The
    # committed link map was generated from HOL's rendered theories and records
    # every HOL entity the thesis links, with its kind, so it stands in for them.
    if not home:
        links = REPO / "thesis" / "shared" / "generated" / "links.json"
        if links.is_file():
            data = json.loads(links.read_text(encoding="utf-8"))
            for key, target in data.get("links", data).items():
                kind, _, name = key.partition(":")
                if target.startswith("HOL/") and kind != "any":
                    kinds[name].add(kind)

    # Theory names, so a figure that labels a node with a theory is not
    # mistaken for one naming a declaration that does not exist.
    theories: set[str] = {
        path.stem for root in ("src", "vendor") for path in (REPO / root).rglob("*.thy")
    }

    sessions: set[str] = set()
    for roots in REPO.rglob("ROOT"):
        if not active_path(roots):
            continue
        for m in re.finditer(
            r"^\s*session\s+\"?([A-Za-z0-9_]+)\"?",
            roots.read_text(errors="ignore"),
            re.M,
        ):
            sessions.add(m.group(1))
    return kinds, sessions, theories, declared_by


def collect_refs(thesis: Path) -> list[tuple[Path, int, str, str]]:
    refs = []
    for path in sorted(thesis.rglob("*")):
        if path.suffix != ".typ" or not path.is_file():
            continue
        text = path.read_text(errors="ignore")
        for m in TYPST_REF.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            refs.append((path, line, m.group(1), m.group(2)))
        for m in ISA_ARG.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            refs.append((path, line, "any", m.group(1)))
    return refs + generated_citations(thesis)


def generated_citations(thesis: Path) -> list[tuple[Path, int, str, str]]:
    """Citations the data files carry for the tables Typst renders from them."""
    refs = []
    for path in sorted((thesis / "shared" / "generated").glob("*.json")):
        data = json.loads(path.read_text())
        if isinstance(data, dict):
            refs += [(path, 1, c["kind"], c["name"]) for c in data.get("citations", [])]
    # Manifests Typst iterates: the anchor index appendix renders every
    # `anchors.toml` item, and the oracle audit table every `facts.toml` key.
    anchors = thesis / "shared" / "anchors.toml"
    if anchors.is_file():
        refs += [
            (anchors, 1, a["kind"], a["name"])
            for a in tomllib.loads(anchors.read_text()).get("anchor", [])
        ]
    facts = thesis / "shared" / "facts.toml"
    if facts.is_file():
        refs += [
            (facts, 1, "thm", name)
            for name in tomllib.loads(facts.read_text()).get("facts", {})
        ]
    return refs


# A backticked token inside a .typ file that looks like an Isabelle name.
# Figure payloads are written as raw literals (`Constraint_System`) rather than
# through isathm/isaconst/isatype/isalocale, so nothing checked them; six of
# the names in the figure gallery had gone stale unnoticed.
RAW_NAME = re.compile(r"`([A-Za-z][A-Za-z0-9_]*)`")

# Three ways to say "this literal is code, but not an Isabelle name".  They are
# mechanisms, not an exclusion list: a growing list of excused identifiers would
# decay into noise, while each of these says *why* the token is exempt.
#
#   1. a language-tagged raw block -- ```ocaml, ```c, ```sh, ... -- is another
#      language by construction;
#   2. a `raw(..., lang: "...")` call, the same thing written as a function;
#   3. `// thesis-refs: ignore` on the line or the line before it, for a one-off
#      that is genuinely code and genuinely untagged.
FENCED_RAW = re.compile(r"```[A-Za-z][A-Za-z0-9+-]*.*?```", re.S)
RAW_CALL = re.compile(
    r'raw\((?:[^()]|\([^()]*\))*?\blang:\s*"[^"]+"(?:[^()]|\([^()]*\))*?\)', re.S
)
IGNORE_MARK = re.compile(r"//\s*thesis-refs:\s*ignore")


def _blank(match: re.Match[str]) -> str:
    """Replace a span with newline-preserving blanks, so line numbers survive."""
    return re.sub(r"[^\n]", " ", match.group(0))


def collect_raw_names(thesis: Path) -> list[tuple[Path, int, str]]:
    out = []
    for path in sorted(thesis.rglob("*")):
        if path.suffix != ".typ" or not path.is_file():
            continue
        text = path.read_text(errors="ignore")
        text = FENCED_RAW.sub(_blank, text)
        text = RAW_CALL.sub(_blank, text)
        lines = text.splitlines()
        for m in RAW_NAME.finditer(text):
            name = m.group(1)
            # Only names shaped like an Isabelle declaration: a multi-word
            # identifier.  A single lowercase word is prose or pseudocode.
            if "_" not in name:
                continue
            line = text.count("\n", 0, m.start()) + 1
            near = " ".join(lines[max(0, line - 2) : line])
            if IGNORE_MARK.search(near):
                continue
            out.append((path, line, name))
    return out


# A declared name written into prose without the markup that colours and links
# it. Only names that cannot be English are considered -- an underscore or an
# inner capital (`valid_ltr`, `EA_Assign`, `FunctionEntry`) -- so a constant
# that is also a word (`intra`, `route`) never fires. Everything the markup
# helpers wrap is blanked first, as are comments, raw blocks and labels.
MARKUP_CALL = re.compile(
    r"\b(?:isa(?:thm|const|type|locale|session|cmd|name|file)|oblig|ctor|keyw|isai"
    r"|thy-badge|thy|proved|stated)\((?:[^()]|\([^()]*\))*\)"
    r"|#isa\((?:[^()]|\([^()]*\))*\)"
    r"|//[^\n]*"
    r"|<[a-z]+:[^>]*>|@[a-z]+:[A-Za-z0-9_-]+"
    # a file path handed to read()/json()/image() names a snippet, not a term
    r"|\b(?:read|json|image|toml)\((?:[^()]|\([^()]*\))*\)",
    re.S,
)
NAME_SHAPE = re.compile(r"[A-Za-z][A-Za-z0-9_']*")


def markable(name: str) -> bool:
    return "_" in name or re.match(r"^[A-Z][a-z]+[A-Z]", name) is not None


def collect_unmarked(
    thesis: Path, kinds: dict[str, set[str]]
) -> list[tuple[Path, int, str]]:
    names = {n for n in kinds if markable(n)}
    out = []
    for path in sorted((thesis / "content").glob("*.typ")):
        # The figure gallery is a draft-only catalogue of placeholder payloads
        # and is deleted before submission; a chapter's figure labels go
        # through the markup helpers and are checked like any other mention.
        if "gallery" in path.name:
            continue
        text = path.read_text(errors="ignore")
        text = FENCED_RAW.sub(_blank, text)
        text = RAW_CALL.sub(_blank, text)
        text = ISA_ARG.sub(_blank, text)
        text = MARKUP_CALL.sub(_blank, text)
        lines = text.splitlines()
        for m in NAME_SHAPE.finditer(text):
            name = m.group(0)
            if name not in names:
                continue
            line = text.count("\n", 0, m.start()) + 1
            near = " ".join(lines[max(0, line - 2) : line])
            if IGNORE_MARK.search(near):
                continue
            out.append((path, line, name))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--thesis", default="thesis", type=Path)
    args = ap.parse_args()

    thesis = (REPO / args.thesis) if not args.thesis.is_absolute() else args.thesis
    if not thesis.is_dir():
        print(f"check_thesis_refs: no such directory: {thesis}", file=sys.stderr)
        return 1

    kinds, sessions, theories, declared_by = build_inventory()
    commands = isabelle_commands()
    if not kinds:
        print(
            "check_thesis_refs: no declarations found -- is the tree checked "
            "out, including vendor/td-verification?",
            file=sys.stderr,
        )
        return 1

    raw = collect_raw_names(thesis)
    stale_raw = [
        (path, line, name)
        for path, line, name in raw
        if name not in kinds
        and name not in sessions
        and name not in theories
        and name not in ALLOWED
    ]
    unwrapped = len(raw) - len(stale_raw)

    refs = collect_refs(thesis)
    missing: list[str] = []
    deviated: list[str] = []
    skipped_cmds: list[str] = []

    for path, line, kind, name in refs:
        if name in ALLOWED:
            continue
        site = f"{path.relative_to(REPO)}:{line}"
        # `compile.simps(4)` selects one theorem of the fact `compile.simps`.
        name = re.sub(r"\([0-9]+\)$", "", name)
        if kind == "cmd":
            if commands is None:
                skipped_cmds.append(name)
            elif name not in commands:
                near = difflib.get_close_matches(name, sorted(commands), 1, 0.75)
                hint = f" -- did you mean {near[0]}?" if near else ""
                missing.append(f"  {site}: {name} is not an Isabelle command{hint}")
            continue
        if kind == "session":
            if name not in sessions:
                near = difflib.get_close_matches(name, sorted(sessions), 1, 0.7)
                hint = f" -- did you mean {near[0]}?" if near else ""
                missing.append(
                    f"  {site}: session {name} is not declared in any ROOT{hint}"
                )
            continue
        if kind == "theory":
            session, _, theory = name.rpartition(".")
            if session not in sessions or theory not in theories:
                missing.append(f"  {site}: theory {name} is not a Session.Theory pair")
            continue
        if kind == "any":
            # A theorem environment's own `isa:` name: it must exist, but the
            # environment does not claim which kind it is.
            if name not in kinds and name not in theories:
                near = difflib.get_close_matches(
                    name, sorted(set(kinds) | theories), 1, 0.7
                )
                hint = f" -- did you mean {near[0]}?" if near else ""
                missing.append(f'  {site}: isa: "{name}" does not exist{hint}')
            continue
        have = kinds.get(name)
        # `locale.name`: a constant declared inside a locale, cited qualified
        # because the short name is not unique (`admits`).
        locale, _, local = name.rpartition(".")
        if have is None and "locale" in kinds.get(locale, ()):
            have = kinds.get(local)
        if have is None:
            near = difflib.get_close_matches(name, sorted(kinds), 1, 0.75)
            hint = f" -- did you mean {near[0]}?" if near else ""
            missing.append(f'  {site}: isa{kind}("{name}") does not exist{hint}')
        elif kind not in have:
            deviated.append(
                f"  {site}: {name} is cited as a {kind}, but the sources declare "
                f"it as {'/'.join(sorted(have))}"
            )

    for path in sorted((thesis / "content").glob("*.typ")):
        text = path.read_text(errors="ignore")
        for m in DEFINITION_ENV.finditer(text):
            isa, cmd = ISA_ARG.search(m.group(1)), CMD_ARG.search(m.group(1))
            if isa is None:
                continue
            site = f"{path.relative_to(REPO)}:{text.count(chr(10), 0, m.start()) + 1}"
            have = declared_by.get(isa.group(1), set())
            if cmd is None:
                missing.append(
                    f"  {site}: definition of {isa.group(1)} needs cmd: "
                    f'"{"/".join(sorted(have)) or "?"}"'
                )
            elif cmd.group(1) not in have:
                deviated.append(
                    f'  {site}: {isa.group(1)} is cited with cmd: "{cmd.group(1)}", '
                    f"but the sources declare it with {'/'.join(sorted(have))}"
                )

    for path, line, name in collect_unmarked(thesis, kinds):
        kind = "/".join(sorted(kinds[name]))
        missing.append(
            f"  {path.relative_to(REPO)}:{line}: {name} ({kind}) is written as prose; "
            f"wrap it so it is coloured and linked"
        )

    for path, line, name in stale_raw:
        near = difflib.get_close_matches(name, sorted(set(kinds) | theories), 1, 0.7)
        hint = f" -- did you mean {near[0]}?" if near else ""
        missing.append(
            f"  {path.relative_to(REPO)}:{line}: `{name}` is written as a raw "
            f"literal and names no declaration, theory or session{hint}"
        )

    if missing or deviated:
        if missing:
            print(
                f"check_thesis_refs: {len(missing)} reference(s) name something "
                "that does not exist:"
            )
            print("\n".join(missing))
        if deviated:
            if missing:
                print()
            print(
                f"check_thesis_refs: {len(deviated)} reference(s) have deviated "
                "from what the sources declare:"
            )
            print("\n".join(deviated))
        print(
            "\nFix the reference, or add it to ALLOWED with a reason if it "
            "deliberately names something outside this tree."
        )
        return 1

    note = ""
    if unwrapped:
        note = (
            f"; {unwrapped} raw `identifier` literal(s) resolve but bypass the "
            "kind check -- wrap them in isathm/isaconst/isatype/isalocale"
        )
    print(
        f"check_thesis_refs: {len(refs)} reference(s) resolve against the sources{note}"
    )
    if skipped_cmds:
        print(
            f"  ({len(set(skipped_cmds))} \\isacmd reference(s) unchecked: "
            "Isabelle is not on PATH)"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
