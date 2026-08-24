#!/usr/bin/env python3
"""Render whisker and histogram plots from a hyperfine --export-json result.

Companion to scripts/mk/bench.sh's --plot flag (hyperfine itself only
exports JSON; plotting is a documented add-on, modeled on the plot_whisker
and plot_histogram helper scripts in hyperfine's own repository). One box
and one histogram series per benchmarked command on a shared time axis,
labeled by the command's -L parameter values when present (for bench.sh
that is the abstract domain) so the labels stay readable next to long
command lines.
"""

import argparse
import json


def label(result: dict) -> str:
    params = result.get("parameters") or {}
    if params:
        return ", ".join(params[k] for k in sorted(params))
    return result["command"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_file", help="hyperfine --export-json output")
    parser.add_argument("output", help="plot image path (e.g. bench.png)")
    parser.add_argument("--title", default=None, help="plot title")
    args = parser.parse_args()

    with open(args.json_file) as f:
        results = json.load(f)["results"]

    import matplotlib  # deferred: parse/read errors should not need a backend

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    times = [r["times"] for r in results]
    labels = [label(r) for r in results]

    fig, (ax_box, ax_hist) = plt.subplots(
        2, 1, sharex=True, figsize=(8, 3.5 + 0.8 * len(results)),
        height_ratios=[len(results), 3],
    )
    ax_box.boxplot(times, orientation="horizontal", tick_labels=labels, showmeans=True)
    if args.title:
        ax_box.set_title(args.title)

    # Shared bin edges keep the per-command histograms comparable.
    edges = np.histogram_bin_edges(np.concatenate(times), bins="auto")
    for series, name in zip(times, labels):
        ax_hist.hist(series, bins=edges, alpha=0.5, label=name)
    ax_hist.set_xlabel("Time [s]")
    ax_hist.set_ylabel("Runs")
    ax_hist.set_xlim(left=0)
    ax_hist.legend()

    fig.tight_layout()
    fig.savefig(args.output, dpi=150)
    print(f"plot written to {args.output}")


if __name__ == "__main__":
    main()
