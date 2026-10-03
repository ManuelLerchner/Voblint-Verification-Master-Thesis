#!/usr/bin/env python3
"""Record which OCaml packages the analyzer needs are on conda-forge.

manifests/conda-forge-ocaml.toml lists the packages, their dependencies and the
oldest version known to build Voblint. A package is available when conda-forge
publishes it at that version or later for every platform of the manifest
(a noarch build counts for all).

    thesis/tools/conda_forge.py --write    ask conda-forge, record the answer
    thesis/tools/conda_forge.py --check    offline: the record matches the manifest
    thesis/tools/conda_forge.py --live     ask again; fail if the record is outdated

The answer changes as recipes are merged, so the record carries the date it
was taken and is committed; the thesis prints that date. `--check` never
touches the network and fails only when the record and the manifest disagree
about the packages. `--live` fails when conda-forge now answers differently
than the record says, so CI notices a merged recipe; the pre-push hook runs
`--write` and fails on a changed record, so the refresh is committed. Without
network access both skip with a note and never overwrite the record.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.error
import urllib.request
from datetime import date
from pathlib import Path

import tomllib

REPO = Path(__file__).resolve().parent.parent.parent
MANIFEST = REPO / "manifests" / "conda-forge-ocaml.toml"
RECORD = REPO / "thesis" / "shared" / "generated" / "conda-forge.json"
API = "https://api.anaconda.org/package/conda-forge/{}"


def load() -> dict:
    return tomllib.loads(MANIFEST.read_text())


def version_key(v: str) -> tuple[int, ...]:
    """Numeric fields of a version, so that v0.17.0 < 0.17.1 and 121 > 119."""
    return tuple(int(n) for n in re.findall(r"\d+", v))


def published(name: str) -> list[tuple[str, str]]:
    """(subdir, version) of every file conda-forge serves for `name`."""
    try:
        with urllib.request.urlopen(API.format(name), timeout=30) as r:
            data = json.load(r)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return []
        raise
    return [
        (f["attrs"].get("subdir", "noarch"), f["version"])
        for f in data.get("files", [])
    ]


def status(name: str, need: str, platforms: list[str]) -> dict:
    files = [(s, v) for s, v in published(name) if version_key(v) >= version_key(need)]
    subdirs = {s for s, _ in files}
    missing = [] if "noarch" in subdirs else [p for p in platforms if p not in subdirs]
    newest = max((v for _, v in files), key=version_key, default=None)
    return {
        "available": bool(files) and not missing,
        "newest": newest,
        "missing": missing,
    }


def skeleton(manifest: dict) -> dict:
    """What the record must agree with, independent of the network."""
    return {
        name: {k: p.get(k) for k in ("opam", "version", "tier", "deps", "for", "via")}
        for name, p in manifest["package"].items()
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--live", action="store_true")
    args = ap.parse_args()

    manifest = load()
    packages = manifest["package"]
    for name, p in packages.items():
        for d in p["deps"]:
            if d not in packages:
                sys.exit(
                    f"conda_forge: {name} depends on {d}, which the manifest lacks"
                )
            if packages[d]["tier"] >= p["tier"]:
                sys.exit(
                    f"conda_forge: {name} (tier {p['tier']}) depends on {d} of a tier not below"
                )

    if args.write or args.live:
        try:
            answers = {
                name: status(name, p["version"], manifest["platforms"])
                for name, p in packages.items()
            }
        except (urllib.error.URLError, TimeoutError) as e:
            print(f"conda_forge: conda-forge unreachable ({e}); record left as it is")
            return 0

    if args.live:
        record = (
            json.loads(RECORD.read_text()) if RECORD.is_file() else {"packages": {}}
        )
        keys = ("available", "newest", "missing")
        changed = [
            name
            for name, a in answers.items()
            if {k: record["packages"].get(name, {}).get(k) for k in keys} != a
        ]
        if changed:
            print(
                f"conda_forge: conda-forge changed since the record of {record.get('date')}: "
                f"{', '.join(changed)}; run pixi run thesis-conda-write",
                file=sys.stderr,
            )
            return 1
        print(
            f"conda_forge: the record of {record['date']} is what conda-forge publishes"
        )
        return 0

    if args.write:
        old = json.loads(RECORD.read_text()) if RECORD.is_file() else None
        record = {
            "date": date.today().isoformat(),
            "platforms": manifest["platforms"],
            "packages": {
                name: {**fields, **answers[name]}
                for name, fields in skeleton(manifest).items()
            },
        }
        # Keep the date when nothing changed, so a refresh alone is no diff.
        if old and {k: v for k, v in old.items() if k != "date"} == {
            k: v for k, v in record.items() if k != "date"
        }:
            record["date"] = old["date"]
        RECORD.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
        done = sum(p["available"] for p in record["packages"].values())
        print(
            f"conda_forge: {done} of {len(packages)} package(s) available, recorded {record['date']}"
        )
        return 0

    if not RECORD.is_file():
        print(
            "conda_forge: no record; run thesis/tools/conda_forge.py --write",
            file=sys.stderr,
        )
        return 1
    record = json.loads(RECORD.read_text())
    stored = {
        name: {k: p.get(k) for k in ("opam", "version", "tier", "deps", "for", "via")}
        for name, p in record["packages"].items()
    }
    if stored != skeleton(manifest) or record.get("platforms") != manifest["platforms"]:
        print(
            "conda_forge: the record does not describe manifests/conda-forge-ocaml.toml; "
            "run thesis/tools/conda_forge.py --write",
            file=sys.stderr,
        )
        return 1
    print(f"conda_forge: record of {record['date']} matches the manifest")
    return 0


if __name__ == "__main__":
    sys.exit(main())
