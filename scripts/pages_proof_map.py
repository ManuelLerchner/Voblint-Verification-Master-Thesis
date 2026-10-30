#!/usr/bin/env python3
"""Package the Isabelle entity export for the standalone corpus wheel.

Run `pixi run proof-map-data` after refreshing Isabelle heaps and HTML.
Edges describe statements/specifications, never proof dependencies. The generated
artifact is served beside the Isabelle HTML; its export date remains visible.
"""

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote

from isabelle_html import Source, generic_sources

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "thesis/tools"))
from entity_deps import project_theories  # noqa: E402
from isar_json import graph  # noqa: E402


def package(raw, html_root, cited, owners=None):
    theories = []
    theory_ids = {}
    anchors = {}
    used_theories = {n["theory"] for n in raw.values()}
    # Old builds can leave the same session under Unsorted after it gains a group.
    for path in sorted(
        html_root.glob("*/*/*.html"),
        key=lambda path: (path.relative_to(html_root).parts[0] == "Unsorted", path),
    ):
        if path.stem not in used_theories or (
            owners and path.stem in owners and path.parent.name != owners[path.stem]
        ):
            continue
        if path.stem in theory_ids:
            continue
        parser = Source(path.read_text())
        theory_ids[path.stem] = len(theories)
        theories.append(
            [path.stem, path.parent.name, path.relative_to(html_root).as_posix()]
        )
        anchors[path.stem] = parser
    missing = sorted({n["theory"] for n in raw.values()} - theory_ids.keys())
    if missing:
        raise ValueError(
            f"Render Isabelle HTML before exporting the map; missing: {missing}"
        )
    ids = {name: i for i, name in enumerate(sorted(raw))}
    origins = generic_sources(raw, anchors)
    nodes = []
    locations = {}
    for name, i in ids.items():
        node = raw[name]
        kind, entity = name.split(":", 1)
        anchor = entity + "|" + ("fact" if kind == "thm" else kind)
        deps = sorted({ids[d] for d in node["deps"] if d in ids and ids[d] != i})
        nodes.append(
            [
                name,
                theory_ids[node["theory"]],
                deps,
                len(set(node["deps"]) - ids.keys()),
                anchor in anchors[node["theory"]].anchors,
                anchor in cited,
            ]
        )
        location = anchors[node["theory"]].location(anchor)
        if location == "interpretation":
            locations[name] = {"kind": location}
            if name in origins:
                locations[name]["generic"] = ids[origins[name]]
    return {"theories": theories, "nodes": nodes, "locations": locations}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw", type=Path, default=REPO / "build/entity-deps/raw.json")
    parser.add_argument("--html", type=Path, default=REPO / "build/isabelle-html")
    parser.add_argument(
        "--out", type=Path, default=REPO / "build/isabelle-html/assets/proof-map.json"
    )
    args = parser.parse_args()
    links = json.loads((REPO / "thesis/shared/generated/links.json").read_text())[
        "links"
    ]
    cited = {unquote(url.split("#", 1)[1]) for url in links.values() if "#" in url}
    content = args.raw.read_bytes()
    owners = {
        name.split(".", 1)[1]: name.split(".", 1)[0] for name in project_theories()
    }
    data = package(json.loads(content), args.html, cited, owners)
    data["layers"] = graph(layers=True)["layers"]
    data["exported"] = (
        datetime.fromtimestamp(args.raw.stat().st_mtime, timezone.utc)
        .date()
        .isoformat()
    )
    data["sha256"] = hashlib.sha256(content).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(
        f"Proof map: {len(data['nodes'])} entities, {len(data['theories'])} theories → {args.out}"
    )


if __name__ == "__main__":
    main()
