#!/usr/bin/env python3
"""Fill profiling metadata from the default snapshot before serving HTML."""

import argparse
import html
import json
import re
from pathlib import Path


def fill_profiling(source: str, pages: Path) -> str:
    index = pages / "data/profiling/index.json"
    if not index.exists():
        return source
    snapshots = json.loads(index.read_text())["snapshots"]
    if not snapshots:
        return source
    entry = snapshots[0]
    snapshot = (pages / entry["file"]).resolve()
    if not snapshot.is_relative_to(pages.resolve()):
        raise ValueError("Profiling snapshot must stay inside the site")
    meta = json.loads(snapshot.read_text())["meta"]
    values = {"reps": str(meta["reps"]), "timeout_s": f"{meta['timeout_s']} s"}
    source = re.sub(
        r'<span data-meta="(reps|timeout_s)">[^<]*</span>',
        lambda m: f'<span data-meta="{m[1]}">{html.escape(values[m[1]])}</span>',
        source,
    )
    device = meta.get("device", {})
    summary = (
        f"Default snapshot: {entry['label']}; measured {meta['date']} at "
        f"{meta['commit']} on {device.get('cpu', meta.get('machine', 'unspecified hardware'))}. "
        f"Median of {meta['reps']} runs; time limit {meta['timeout_s']} s. "
        "The snapshot records any later partial re-runs and their revisions. "
    )
    summary = (
        "<li data-snapshot-summary>"
        + html.escape(summary)
        + f'<a href="{html.escape(entry["file"], quote=True)}">Raw snapshot and metadata</a>.</li>'
    )
    return re.sub(r"<li data-snapshot-summary>.*?</li>", lambda _: summary, source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fill", type=Path, required=True)
    parser.add_argument(
        "--pages", type=Path, default=Path(__file__).resolve().parent.parent / "pages"
    )
    args = parser.parse_args()
    args.fill.write_text(fill_profiling(args.fill.read_text(), args.pages))


if __name__ == "__main__":
    main()
