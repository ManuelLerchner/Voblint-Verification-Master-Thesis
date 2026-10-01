"""isar-tools output as data, for the scripts that read the theories.

`session_graph.py` and `pages_stats.py` count what the Pages explainer shows;
the thesis checks resolve names and locale parents. Reading the theories is
isar-tools' job: its outer-syntax parser knows where a command, a comment, and
a text block start and end, which a line scanner can only approximate. What
counts as a definition or a lemma stays here, so the site's labels keep
meaning what they say.

Every call runs `isar ... --format json` from the repository root; results are
cached, because one site build asks for the same figures several times.
"""

import json
import subprocess
import sys
from functools import cache
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
TD_DIR = REPO_ROOT / "vendor" / "td-verification"

# Commands that declare something a reader looks up: the site's "definitions".
DEFINITION_COMMANDS = (
    "locale",
    "definition",
    "fun",
    "primrec",
    "inductive",
    "inductive_set",
    "abbreviation",
    "record",
    "datatype",
    "type_synonym",
    "class",
    "fun_cases",
)
# Proved statements: the site's "lemmas".
THEOREM_COMMANDS = ("theorem", "lemma", "corollary")
# Structure worth showing beside them in the declaration-kinds figure.
STRUCTURE_COMMANDS = (
    "function",
    "inductive_cases",
    "interpretation",
    "global_interpretation",
    "sublocale",
    "instantiation",
    "lemmas",
)


@cache
def isar(*args: str) -> dict:
    """`isar ARGS --format json`, parsed; exits with isar's message on failure."""
    run = subprocess.run(
        ["isar", *args, "--format", "json"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if run.returncode != 0:
        sys.exit(f"isar {' '.join(args)} failed:\n{run.stderr}")
    return json.loads(run.stdout)


def sessions(directory: str = ".") -> list[dict]:
    """The sessions of `directory` with parent and directory (`isar project sessions`)."""
    return isar("project", "sessions", directory)["sessions"]


def session_sizes(directory: str = ".") -> dict[str, dict]:
    """Per session: theories, lines, code_lines, doc_lines (`isar stats sessions`)."""
    return {
        row["session"]: row for row in isar("stats", "sessions", directory)["sessions"]
    }


def theory_sizes(directory: str = ".") -> list[dict]:
    """Per theory: session, theory, path, lines, code_lines, doc_lines."""
    return isar("stats", "theories", "--top", "0", directory)["theories"]


def command_counts(directory: str = ".") -> dict[str, dict[str, int]]:
    """Session -> command -> number of uses (`isar stats commands`)."""
    counts: dict[str, dict[str, int]] = {}
    for row in isar("stats", "commands", directory)["commands"]:
        counts.setdefault(row["session"], {})[row["command"]] = row["count"]
    return counts


def theory_command_counts(
    directory: str = ".",
) -> dict[tuple[str, str], dict[str, int]]:
    """(session, theory) -> command -> number of uses (`isar stats commands --by theory`)."""
    counts: dict[tuple[str, str], dict[str, int]] = {}
    for row in isar("stats", "commands", "--by", "theory", directory)["commands"]:
        counts.setdefault((row["session"], row["theory"]), {})[row["command"]] = row[
            "count"
        ]
    return counts


def graph(directory: str = ".", theories: bool = False, layers: bool = False) -> dict:
    """Session graph (parent and `sessions` edges), or the theory import graph.
    With `layers`, also session `imports` edges and each session's stratum."""
    flags = [*(["--theories"] if theories else []), *(["--layers"] if layers else [])]
    return isar("project", "graph", *flags, directory)


def project_directories(root: Path = REPO_ROOT) -> list[str]:
    """`root` and, where the submodule is checked out, its vendored solver: a
    project of its own, which `isar ... root` skips."""
    td = root / TD_DIR.relative_to(REPO_ROOT)
    return [str(root)] + ([str(td)] if (td / "ROOT").is_file() else [])


def names(*paths: str, derived: bool = False, statements: bool = False) -> list[dict]:
    """Declared names (`isar project names`) of a project directory (default
    the repository) or of single theory files: qualified `name`, `kind`,
    `command`, `path`, `line`, `mixfix`, `notation`, `mode`, `anchor`, ...;
    with `derived` also derived facts (`f.simps`, inductive rules) with
    `derived_from`, and with `statements` each declaration's `statement`."""
    flags = [
        *(["--derived"] if derived else []),
        *(["--statements"] if statements else []),
    ]
    return isar("project", "names", *flags, *(paths or (".",)))["names"]


def instances(directory: str = ".") -> list[dict]:
    """Class instances and interpretations (`isar project instances`): `kind`,
    `name` (`t :: c` or the qualifier), `target`, `arguments`, `path`, `line`."""
    return isar("project", "instances", directory)["instances"]


def base_name(row: dict) -> str:
    """A `names` row as the sources spell it: `f` for `Theory.loc.f`, and
    `pstep.Seq2` for the rule `VIMP_Proc.pstep.Seq2` derived from `pstep`."""
    parent = row["derived_from"]
    if parent and row["name"].startswith(parent):
        return (
            base_name({"name": parent, "derived_from": ""}) + row["name"][len(parent) :]
        )
    return row["name"].rsplit(".", 1)[-1]


def hierarchy(directory: str = ".") -> list[dict]:
    """Class and locale declarations (`isar project hierarchy`): `kind`,
    `name`, `parents`, `sorts`, `fixes`, `assumes`, `path`, `line`."""
    return isar("project", "hierarchy", directory)["declarations"]
