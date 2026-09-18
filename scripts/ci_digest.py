#!/usr/bin/env python3
"""Print the cache key digest for one CI artifact.

Four CI jobs skip expensive work when their inputs are byte-identical to a run
that already did it: the rendered HTML tree, the formalization PDF, and the
markers of a passing facts or codegen check. Each keys its cache on a digest of
what it consumes, and the keys are exact -- no restore-keys -- so a digest that
is too wide silently pays the full cost again, and one that is too narrow
presents another run's output as this one's.

Both failures are invisible in a green build, which is why the input sets live
here rather than inline in the workflow: they are readable side by side, and
`--explain` prints the file list a key was computed from.

`git ls-files -s` prints the blob SHA of every tracked file under a path and the
gitlink SHA of a submodule, so a digest covers the vendored solver's pointer
without reading its content and untracked build output cannot enter it.

    scripts/ci_digest.py html
    scripts/ci_digest.py codegen --explain
"""

from __future__ import annotations

import argparse
import hashlib
import os
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# The setup action is in every set because it pins the AFP revision and the
# Isabelle container tag. pixi.lock, never pixi.toml: the environment is what
# these outputs depend on, while pixi.toml also carries every task in the
# repository, so an unrelated task addition would invalidate an output that is
# byte-identical.
COMMON = [
    "pixi.lock",
    "vendor/td-verification",
    ".github/actions/setup-isabelle-action",
]

# Whether the digest also covers `isabelle version`: the facts and codegen
# checks drive the container's own Isabelle, and read its version before the
# setup action runs. The HTML and PDF jobs take the same information from
# ISABELLE_VERSION_SLUG, which is already part of their cache key.
INPUTS: dict[str, dict[str, object]] = {
    # sessions.sh is what decides which sessions get rendered. Its answer is
    # derived from ROOTS and the ROOT files, which are already here, but the
    # derivation is not.
    "html": {
        "paths": [
            "src",
            "ROOTS",
            "scripts/mk/html.sh",
            "scripts/mk/sessions.sh",
            "scripts/mk/require-afp.sh",
            *COMMON,
        ],
        "isabelle_version": False,
        "codegen_hash": False,
    },
    "pdf": {
        "paths": [
            "src",
            "ROOTS",
            "document",
            "README.md",
            "scripts/mk/pdf.sh",
            "scripts/mk/require-afp.sh",
            "scripts/gen_pdf_session.py",
            "scripts/build_readme_pdf.py",
            "scripts/pdf_readme.lua",
            *COMMON,
        ],
        "isabelle_version": False,
        "codegen_hash": False,
    },
    "thesis-facts": {
        "paths": [
            "src",
            "ROOTS",
            "thesis/tools/facts.py",
            "thesis/shared/facts.toml",
            "thesis/shared/generated/facts.json",
            *COMMON,
        ],
        "isabelle_version": True,
        "codegen_hash": False,
    },
    # The theories reach this digest through codegen-hash.sh, which is also what
    # the regeneration and the CLI build compare, so the three cannot define
    # codegen's inputs differently.
    "codegen": {
        "paths": [
            "codegen/generated",
            "scripts/mk/check-clean.sh",
            "scripts/mk/require-afp.sh",
            *COMMON,
        ],
        "isabelle_version": True,
        "codegen_hash": True,
    },
}


def isabelle_binary() -> str:
    """The Isabelle these jobs actually drive, readable before the setup action."""
    return (
        os.environ.get("ISABELLE")
        or shutil.which("isabelle")
        or "/home/isabelle/Isabelle/bin/isabelle"
    )


def material(name: str) -> str:
    spec = INPUTS[name]
    parts: list[str] = []
    if spec["isabelle_version"]:
        parts.append(
            subprocess.run(
                [isabelle_binary(), "version"],
                cwd=REPO,
                capture_output=True,
                text=True,
                check=True,
            ).stdout
        )
    if spec["codegen_hash"]:
        parts.append(
            subprocess.run(
                ["sh", "scripts/mk/codegen-hash.sh"],
                cwd=REPO,
                capture_output=True,
                text=True,
                check=True,
            ).stdout
        )
    parts.append(
        subprocess.run(
            ["git", "ls-files", "-s", "--", *spec["paths"]],
            cwd=REPO,
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    )
    return "".join(parts)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("artifact", choices=sorted(INPUTS))
    ap.add_argument(
        "--explain",
        action="store_true",
        help="also print what the digest was computed from",
    )
    args = ap.parse_args()

    body = material(args.artifact)
    digest = hashlib.sha256(body.encode()).hexdigest()[:32]
    if args.explain:
        print(body, end="", file=sys.stderr)
    print(digest)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
