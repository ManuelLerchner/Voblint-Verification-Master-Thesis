#!/usr/bin/env python3
"""Rejects a session ROOT whose theory entry cannot be loaded.

A theory entry is a theory *name*, never a path: Isabelle reads a slash there as
a malformed import and fails the whole session at load, before any theory is
processed. A subdirectory is put on the search path by `directories` instead, so
`directories "generated"` plus a bare `Sign_Assembly` is the working spelling and
`generated/Sign_Assembly` is not.

That failure is disproportionate to its cause: jEdit will not start, so the
mistake presents as a dead editor rather than as an error in the file that
caused it. It costs nothing to catch here.

A `Session.Theory` entry is the one exception to "a name, never a path": it
builds another session's theory into this heap without importing it, so it is
resolved against that session's search path instead. An entry naming a session
outside the scan (vendored, or HOL) is left alone.

Also checked: every `directories` entry exists; every theory entry resolves to a
file on that session's search path; and every .thy on that search path is
*reached* by the session that owns it, either by being listed or by being
imported from something listed. The last one is the quiet failure -- a theory
no listed theory reaches is simply not built, so it never fails and never
reaches the export.

Scans `src` by default. The vendored sessions are excluded because we do not
own them: `vendor/td-verification` has three theories nothing reaches
(`Example_Widening_Narrowing`, `Example_side`, `TD_plain_warrow`), which is
upstream's business. Pass a path to scan them anyway.

Usage: python3 scripts/check_root_entries.py [root ...]   (default: src)
"""

import re
import sys
from pathlib import Path

# A ROOT line that introduces a block, so scanning knows which block it is in.
BLOCK = re.compile(r"^\s*(sessions|theories|directories|document_files|export_files)\b")
ENTRY = re.compile(r'^\s+(?:\(\*.*\*\)\s*)?"?([A-Za-z0-9_./-]+)"?\s*(?:\(.*\))?\s*$')


COMMENT = re.compile(r"\(\*.*?\*\)", re.S)
OPTIONS = re.compile(r"\[[^\]]*\]")


def entries(text):
    """(block, entry) pairs, with comments and block options removed.

    Comments nest across lines and a block keyword may carry options
    (`theories [document = false]`), so both are stripped before scanning
    rather than per line.
    """
    block = None
    for raw in OPTIONS.sub("", COMMENT.sub("", text)).split("\n"):
        line = raw
        if not line.strip():
            continue
        head = BLOCK.match(line)
        if head:
            block = head.group(1)
            rest = line[head.end() :].strip()
            if rest:
                yield block, rest.strip('"')
            continue
        if line.lstrip() != line and block:
            m = ENTRY.match(line)
            if m:
                yield block, m.group(1)
        elif not line[:1].isspace():
            block = None


IMPORTS = re.compile(r"^\s*theory\s+\S+\s+imports\b(.*?)\bbegin\b", re.S | re.M)


def imported_names(thy):
    """The unqualified theory names this file imports. A qualified name belongs
    to another session, which owns whether it is built."""
    m = IMPORTS.search(COMMENT.sub("", thy.read_text()))
    if not m:
        return []
    return [n.strip('"') for n in m.group(1).split() if "." not in n.strip('"')]


def reached(listed, search):
    """Theory names the session actually builds: the listed ones and everything
    their imports pull in from this session's own search path."""
    seen, queue = set(), list(listed)
    while queue:
        name = queue.pop()
        if name in seen:
            continue
        seen.add(name)
        for d in search:
            f = d / f"{name}.thy"
            if f.is_file():
                queue += imported_names(f)
                break
    return seen


SESSION = re.compile(r"^session\s+([A-Za-z0-9_-]+)\b", re.M)


def session_search_paths(all_roots):
    """session name -> its search path, for resolving qualified theory entries.

    A `theories` entry may name another session's theory as `Session.Theory`,
    which builds it into this session's heap without importing it. Resolving
    that needs the *owning* session's search path, not this one's.
    """
    paths = {}
    for root_file in all_roots:
        text = root_file.read_text()
        m = SESSION.search(COMMENT.sub("", text))
        if not m:
            continue
        base = root_file.parent
        dirs = [e for b, e in entries(text) if b == "directories"]
        paths[m.group(1)] = [base] + [base / d for d in dirs]
    return paths


def owned_theories(base, dirs, all_roots):
    """The .thy files this session owns: those on its search path that no
    nested session claims first."""
    nested = {
        r.parent for r in all_roots if r.parent != base and base in r.parent.parents
    }
    found = []
    for d in [base] + [base / x for x in dirs]:
        for thy in sorted(d.glob("*.thy")):
            if not any(n == thy.parent or n in thy.parents for n in nested):
                found.append(thy)
    return found


def check(root_file, all_roots):
    problems = []
    base = root_file.parent
    text = root_file.read_text()
    dirs = [e for b, e in entries(text) if b == "directories"]
    theories = [e for b, e in entries(text) if b == "theories"]

    for d in dirs:
        if not (base / d).is_dir():
            problems.append(f"{root_file}: directories entry '{d}' is not a directory")

    search = [base] + [base / d for d in dirs]
    owners = session_search_paths(all_roots)
    for t in theories:
        if "." in t:
            # Session-qualified: another session owns the file, so resolve it
            # there. An unscanned session (vendored, or HOL) cannot be checked,
            # which is the same exemption owned_theories makes for vendor/.
            owner, name = t.rsplit(".", 1)
            if owner in owners and not any(
                (d / f"{name}.thy").is_file() for d in owners[owner]
            ):
                problems.append(
                    f"{root_file}: theory entry '{t}' has no .thy on "
                    f"{owner}'s search path"
                )
            continue
        if "/" in t:
            fix = t.rsplit("/", 1)[1]
            problems.append(
                f"{root_file}: theory entry '{t}' contains a slash; Isabelle reads that as "
                f"a malformed import and the session will not load. Put its directory in "
                f"`directories` and write '{fix}'"
            )
            continue
        if not any((d / f"{t}.thy").is_file() for d in search):
            problems.append(
                f"{root_file}: theory entry '{t}' has no .thy on the "
                f"session's search path"
            )

    # Two files of the same name on one search path. Isabelle resolves the
    # entry to one of them and the other is silently never built, so the
    # reachability check below cannot see it -- both share the stem, and the
    # stem is listed. This bites when a theory is moved into `generated` and
    # the hand-written original is not removed in the same change.
    by_stem = {}
    for thy in owned_theories(base, dirs, all_roots):
        by_stem.setdefault(thy.stem, []).append(thy)
    for stem, paths in sorted(by_stem.items()):
        if len(paths) > 1:
            where = ", ".join(str(p.relative_to(base)) for p in paths)
            problems.append(
                f"{root_file}: two theories named '{stem}' on this session's search "
                f"path ({where}); Isabelle builds one and never reports the other"
            )

    listed = reached(theories, search)
    for thy in owned_theories(base, dirs, all_roots):
        if thy.stem not in listed:
            problems.append(
                f"{root_file}: {thy.relative_to(base)} is on this session's "
                f"search path but nothing this session builds reaches it"
            )
    return problems


def main():
    roots = [Path(a) for a in sys.argv[1:]] or [Path("src")]
    problems = []
    checked = 0
    all_roots = sorted(f for r in roots for f in r.rglob("ROOT") if f.is_file())
    for root_file in all_roots:
        checked += 1
        problems += check(root_file, all_roots)
    for p in problems:
        print(p, file=sys.stderr)
    print(f"checked {checked} ROOT files")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
