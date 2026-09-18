#!/usr/bin/env python3
"""Delete the heap caches that keep this repository at its cache ceiling.

isabelle-build writes one 200 MB heap entry per commit, keyed on the SHA so a
later run can restore the exact state that commit built. Nothing ever removes
the older ones, and GitHub's per-repository budget is 10 GB, so the heaps grow
until eviction starts -- and eviction is least-recently-used, which takes the
small, rarely-written entries first: the rendered HTML tree, the PDF, the
markers of a passing check. Those are exactly the caches whose whole value is
surviving between the runs that need them.

Only the newest few heaps are reachable anyway: the restore falls back to a
prefix key, so it lands on the most recent entry regardless of how many older
ones exist.

    scripts/prune_ci_caches.py                 # report what would go
    scripts/prune_ci_caches.py --apply         # delete it

Needs GITHUB_TOKEN with `actions: write` and GITHUB_REPOSITORY, both of which a
workflow job already has.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request

API = "https://api.github.com"
PREFIX = "isabelle-heaps-"
KEEP = 3


def call(method: str, path: str, token: str) -> dict | None:
    request = urllib.request.Request(
        API + path,
        method=method,
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        body = response.read()
    return json.loads(body) if body else None


def heaps(repo: str, token: str) -> list[dict]:
    """Every heap cache, newest first."""
    found: list[dict] = []
    page = 1
    while True:
        query = urllib.parse.urlencode(
            {"per_page": 100, "page": page, "sort": "created_at", "direction": "desc"}
        )
        data = call("GET", f"/repos/{repo}/actions/caches?{query}", token) or {}
        batch = data.get("actions_caches", [])
        found.extend(c for c in batch if c["key"].startswith(PREFIX))
        if len(batch) < 100:
            return found
        page += 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", type=int, default=KEEP, help="heaps to leave in place")
    ap.add_argument(
        "--apply", action="store_true", help="delete; otherwise only report"
    )
    args = ap.parse_args()

    token = os.environ.get("GITHUB_TOKEN")
    repo = os.environ.get("GITHUB_REPOSITORY")
    if not token or not repo:
        print(
            "prune_ci_caches: GITHUB_TOKEN and GITHUB_REPOSITORY are required",
            file=sys.stderr,
        )
        return 1

    found = heaps(repo, token)
    stale = found[args.keep :]
    freed = sum(c["size_in_bytes"] for c in stale) / 2**30
    print(
        f"prune_ci_caches: {len(found)} heap cache(s), {len(stale)} beyond the newest {args.keep}"
    )
    for cache in stale:
        print(f"  {cache['key']} ({cache['size_in_bytes'] / 2**20:.0f} MiB)")
        if not args.apply:
            continue
        try:
            call("DELETE", f"/repos/{repo}/actions/caches/{cache['id']}", token)
        # A concurrent run may have removed it, or evicted it out from under us.
        except urllib.error.HTTPError as error:
            print(f"    not deleted: HTTP {error.code}")
    print(f"prune_ci_caches: {'freed' if args.apply else 'would free'} {freed:.2f} GiB")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
