#!/usr/bin/env python3
"""Keep the Pixi task interface and GitHub verification surface aligned.

``verify`` is the supported local aggregate. GitHub Actions schedules its
dependencies separately, but must invoke the same named tasks. This check also
keeps task descriptions complete and rejects references to retired task names.
"""

from __future__ import annotations

import re
import sys
import tomllib
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent
MANIFEST = REPO / "pixi.toml"
WORKFLOW = REPO / ".github" / "workflows" / "ci.yml"

# Pixi also exposes setup operations so local bootstrap and CI share one
# command surface. They prepare verification jobs but are not verification
# gates themselves.
CI_SETUP_TASKS = {
    "ocaml-deps-install",
}

# These tasks are CI/deployment orchestration rather than verification gates.
# They operate on generated or deployed artifacts and therefore are not part
# of the supported local `verify` aggregate.
CI_ONLY_TASKS = {
    "pages-links-live",
    "pages-site-build",
    "thesis-links-live",
    "thesis-links-write",
}

RETIRED_TASKS = {
    "bench",
    "bootstrap",
    "build",
    "ci",
    "codegen-api",
    "codegen-modules",
    "docs-lint",
    "docs-overview",
    "gen-assembly",
    "gen-grammar-isabelle",
    "gen-grammar-menhir",
    "grammar-check-isabelle",
    "grammar-check-menhir",
    "html",
    "html-config-audit",
    "html-report-audit",
    "html-report-check",
    "id-position-check",
    "jedit",
    "lefthook-install",
    "lint",
    "locale-parameters",
    "property",
    "property-build",
    "registry-check",
    "report",
    "retired-identifiers",
    "root-entries",
    "stats",
    "thy-prose-refs",
    "vendor",
}

SKIP_PARTS = {
    ".git",
    ".pixi",
    ".claude/worktrees",
    "_build",
    "docs/history",
    "codegen/generated",
    "vendor",
}

TEXT_SUFFIXES = {
    ".md",
    ".ml",
    ".mli",
    ".mll",
    ".mly",
    ".py",
    ".sh",
    ".thy",
    ".toml",
    ".yaml",
    ".yml",
}


def all_tasks(manifest: dict) -> dict[str, object]:
    tasks = dict(manifest.get("tasks", {}))
    for feature in manifest.get("feature", {}).values():
        tasks.update(feature.get("tasks", {}))
    return tasks


def task_description(spec: object) -> str | None:
    if not isinstance(spec, dict):
        return None
    description = spec.get("description")
    return description.strip() if isinstance(description, str) else None


def workflow_tasks() -> set[str]:
    # Dropping comment-only lines excludes documentation and shell comments in
    # ``run: |`` blocks while retaining every executable Pixi invocation.
    lines = [line for line in WORKFLOW.read_text().splitlines()
             if not line.lstrip().startswith("#")]
    return set(re.findall(r"\bpixi run ([a-z][a-z0-9-]*)", "\n".join(lines)))


def active_text_files():
    for path in REPO.rglob("*"):
        if not path.is_file() or (
            path.suffix not in TEXT_SUFFIXES and path.name != ".gitignore"
        ):
            continue
        rel = path.relative_to(REPO).as_posix()
        if any(rel == part or rel.startswith(f"{part}/") for part in SKIP_PARTS):
            continue
        yield path


def retired_references() -> list[str]:
    names = "|".join(re.escape(name) for name in sorted(RETIRED_TASKS, key=len, reverse=True))
    pattern = re.compile(rf"\bpixi run ({names})(?![a-z0-9-])")
    found = []
    for path in active_text_files():
        text = path.read_text(errors="ignore")
        for match in pattern.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            found.append(f"{path.relative_to(REPO)}:{line}: {match.group(1)}")
    return found


def main() -> int:
    manifest = tomllib.loads(MANIFEST.read_text())
    tasks = all_tasks(manifest)
    problems = []

    undescribed = sorted(name for name, spec in tasks.items()
                         if not task_description(spec))
    if undescribed:
        problems.append("tasks without descriptions: " + ", ".join(undescribed))

    verify = manifest.get("tasks", {}).get("verify")
    if not isinstance(verify, dict) or verify.get("cmd"):
        problems.append("verify must be a dependency-only aggregate")
        verify_tasks = set()
    else:
        verify_tasks = set(verify.get("depends-on", []))

    ci_tasks = workflow_tasks() - CI_SETUP_TASKS - CI_ONLY_TASKS
    missing_ci = sorted(verify_tasks - ci_tasks)
    extra_ci = sorted(ci_tasks - verify_tasks)
    if missing_ci:
        problems.append("verify tasks absent from GitHub CI: " + ", ".join(missing_ci))
    if extra_ci:
        problems.append("GitHub CI verification tasks absent from verify: " + ", ".join(extra_ci))

    retired = retired_references()
    if retired:
        problems.append("retired Pixi task invocations remain:\n  " + "\n  ".join(retired))

    if "opam exec -- pixi run" in WORKFLOW.read_text():
        problems.append("GitHub CI activates opam outside Pixi tasks")

    if problems:
        print("check_verification_surface:")
        for problem in problems:
            print(f"  {problem}")
        return 1

    print(
        f"check_verification_surface: {len(tasks)} described tasks; "
        f"{len(verify_tasks)} verification tasks match GitHub CI"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
