/* The four states, the current unknown and the step's edges, on top of the CFG's own style. */
export function replayStyle(cssToken) {
  return [
    // Pointer activation must not add Cytoscape's broad grey overlay: replay
    // already marks the trace's active edges explicitly with r-active.
    { selector: "edge", style: { "overlay-opacity": 0 } },
    /* A step replaces the previous step's marks at once; a fade would blend the two. */
    { selector: "node.point", style: { "transition-duration": 0 } },
    {
      selector: "node.point.r-unseen",
      style: {
        "border-style": "dashed",
        "border-width": 1,
        "border-color": cssToken("--text-faint"),
        "background-color": cssToken("--surface-muted"),
        color: cssToken("--text-faint"),
      },
    },
    {
      selector: "node.point.r-seen",
      style: {
        "border-width": 1,
        "border-color": cssToken("--border-strong"),
        "background-color": cssToken("--surface"),
      },
    },
    {
      selector: "node.point.r-stable",
      style: {
        "border-width": 2,
        "border-color": cssToken("--primary"),
        "background-color": cssToken("--primary-soft"),
      },
    },
    {
      selector: "node.point.r-solving",
      style: {
        "border-width": 2,
        "border-color": cssToken("--accent"),
        "background-color": cssToken("--accent-soft"),
        "underlay-opacity": 0.25,
      },
    },
    {
      selector: "node.point.r-current",
      style: {
        "border-width": 4,
        "border-color": cssToken("--accent"),
        "background-color": cssToken("--accent-soft"),
        "underlay-opacity": 0.25,
      },
    },
    {
      selector: "node.point.r-destabilized",
      style: { "border-style": "dotted", "border-width": 2 },
    },
    {
      selector: "node.point.r-target",
      style: { "outline-color": cssToken("--primary"), "outline-width": 3, "outline-offset": 3 },
    },
    {
      selector: "node.point.r-changed",
      style: { "underlay-color": cssToken("--success"), "underlay-opacity": 0.35 },
    },
    {
      selector: "node.point.r-wpoint",
      style: { "border-style": "double", "border-width": 4 },
    },
    {
      selector: "node.point.r-widened",
      style: { "underlay-color": cssToken("--accent"), "underlay-opacity": 0.35 },
    },
    {
      selector: "node.seed.r-unseen",
      style: {
        "background-color": cssToken("--surface-muted"),
        "border-color": cssToken("--text-faint"),
        "border-style": "dashed",
      },
    },
    {
      selector: "node.seed.r-seen",
      style: { "background-color": cssToken("--surface"), "border-color": cssToken("--warning") },
    },
    {
      selector: "node.seed.r-seed-set",
      style: { "background-color": cssToken("--warning"), "border-color": cssToken("--warning") },
    },
    {
      selector: "node.global.r-unseen",
      style: {
        "background-color": cssToken("--surface-muted"),
        "border-color": cssToken("--text-faint"),
        "border-style": "dashed",
      },
    },
    {
      selector: "node.global.r-seen",
      style: {
        "background-color": cssToken("--surface"),
        "border-color": cssToken("--global-link"),
      },
    },
    {
      selector: "node.global.r-seed-set",
      style: {
        "background-color": cssToken("--global-link"),
        "border-color": cssToken("--global-link"),
      },
    },
    {
      selector: "node.seed.r-changed, node.global.r-changed",
      style: {
        "border-color": cssToken("--success"),
        "border-width": 4,
      },
    },
    {
      selector: "node.seed.r-target, node.global.r-target",
      style: { "outline-color": cssToken("--primary"), "outline-width": 3, "outline-offset": 3 },
    },
    {
      selector: "edge.r-infl, edge.r-event",
      style: {
        width: 1.5,
        "line-style": "dotted",
        "curve-style": "unbundled-bezier",
        "line-color": cssToken("--text-faint"),
        "target-arrow-shape": "triangle",
        "target-arrow-color": cssToken("--text-faint"),
        "z-index": 5,
      },
    },
    {
      selector: "edge.r-active",
      style: {
        width: 4,
        "line-style": "solid",
        "line-color": cssToken("--accent"),
        "target-arrow-color": cssToken("--accent"),
        "z-index": 10,
      },
    },
  ];
}
