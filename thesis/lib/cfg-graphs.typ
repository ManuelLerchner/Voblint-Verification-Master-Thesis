// The compiled graph of the recursive sum/dec program, shared by the
// compiled-graph figure and the trace figure. Node names and edge labels are
// read from registered `--dot` output, so a drawing fails to build when the
// compiler's output changes. Lines are matched up to the context suffix, which
// numbers the analysis contexts and does not change the graph.
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "theme.typ": vb
#import "math.typ": signval

#let dot-label(line) = (
  line.match(regex("[\\[,]label=\"([^\"\\\\]*)")).captures.at(0)
)
#let dot-edge-line(snap, claim, src, dst) = {
  let pat = regex("^  " + src + "_ctx[0-9]+ -> " + dst + "_ctx[0-9]+ \\[")
  let line = snap.find(l => l.match(pat) != none)
  assert(line != none, message: claim + " has no edge " + src + " -> " + dst)
  line
}
#let dot-node-line(snap, claim, id) = {
  let pat = regex("^    " + id + "_ctx[0-9]+ \\[")
  let line = snap.find(l => l.match(pat) != none)
  assert(line != none, message: claim + " has no node " + id)
  line
}
#let sum-graph = {
  set text(size: 7.5pt, font: "DejaVu Sans Mono")
  let dot = read("/shared/generated/cfg-sum-dec-dot.txt").split("\n")
  let edge-line(a, b) = dot-edge-line(dot, "cfg-sum-dec-dot", a, b)
  let n(pos, id, boundary: false) = node(
    pos,
    dot-label(dot-node-line(dot, "cfg-sum-dec-dot", id)),
    stroke: 0.8pt + (if boundary { vb.accent } else { vb.neutral }),
    fill: if boundary { vb.accent.lighten(90%) } else { white },
    corner-radius: if boundary { 2pt } else { 6pt },
    inset: 3.5pt,
    name: label(id),
  )
  let lab(body, fill: vb.neutral) = text(size: 7pt, fill: fill, body)
  let intra(a, b, ..args) = edge(
    label(a),
    label(b),
    "-|>",
    stroke: 0.7pt + vb.neutral,
    label: lab(dot-label(edge-line(a, b))),
    label-sep: 2pt,
    ..args,
  )
  let call(a, b, via: (), ..args) = edge(
    label(a),
    ..via,
    label(b),
    "-|>",
    stroke: (paint: vb.called, thickness: 0.9pt, dash: "dashed"),
    label: lab(dot-label(edge-line(a, b)), fill: vb.called),
    label-sep: 2pt,
    ..args,
  )
  let cont(a, b, ..args) = {
    assert(edge-line(a, b).contains("label=\"continuation\""))
    edge(
      label(a),
      label(b),
      stroke: (paint: vb.called, thickness: 0.8pt, dash: "dotted"),
      ..args,
    )
  }
  let resume(a, b, via: (), ..args) = {
    assert(edge-line(a, b).contains("xlabel=\"resume"))
    edge(
      label(a),
      ..via,
      label(b),
      "-|>",
      stroke: (paint: vb.accent, thickness: 0.6pt),
      ..args,
    )
  }
  let head(pos, name) = node(pos, text(weight: "bold", fill: vb.muted, name), stroke: none)
  diagram(
    spacing: (7.8mm, 5.6mm),
    head((0, -0.7), "main"),
    head((2.5, -0.7), "sum"),
    head((5.6, 1.2), "dec"),
    n((0, 0), "main_entry_main", boundary: true),
    n((0, 1), "main_pp9"),
    n((0, 3), "main_pp10"),
    n((0, 4), "main_pp11"),
    n((0, 5), "main_exit_main", boundary: true),
    n((2.5, 0), "sum_entry_sum", boundary: true),
    n((2.5, 1), "sum_pp2"),
    n((1.8, 2), "sum_pp3"),
    n((3.2, 2), "sum_pp5"),
    n((3.2, 3), "sum_pp6"),
    n((3.2, 4), "sum_pp7"),
    n((2.5, 5), "sum_exit_sum", boundary: true),
    n((5.6, 2), "dec_entry_dec", boundary: true),
    n((5.6, 3), "dec_pp0"),
    n((5.6, 4), "dec_exit_dec", boundary: true),
    intra("main_entry_main", "main_pp9", label-side: right),
    cont("main_pp9", "main_pp10"),
    intra("main_pp10", "main_pp11", label-side: left),
    intra("main_pp11", "main_exit_main", label-side: left),
    intra("sum_entry_sum", "sum_pp2", label-side: left),
    intra("sum_pp2", "sum_pp3", label-side: right),
    intra("sum_pp2", "sum_pp5", label-side: left),
    intra("sum_pp3", "sum_exit_sum", label-side: left),
    cont("sum_pp5", "sum_pp6"),
    cont("sum_pp6", "sum_pp7"),
    intra("sum_pp7", "sum_exit_sum", label-side: left, label-pos: 0.35, label-sep: 4pt),
    intra("dec_entry_dec", "dec_pp0", label-side: left),
    intra("dec_pp0", "dec_exit_dec", label-side: left),
    call(
      "main_pp9",
      "sum_entry_sum",
      label-side: right,
      label-pos: 0.55,
      label-sep: 5pt,
      bend: 12deg,
    ),
    call("sum_pp5", "dec_entry_dec", label-side: right, label-pos: 0.55, label-sep: 3pt),
    call(
      "sum_pp6",
      "sum_entry_sum",
      via: ((3.9, 3), (3.9, 0)),
      corner-radius: 4pt,
      label-pos: 0.5,
      label-side: right,
    ),
    resume(
      "sum_exit_sum",
      "main_pp10",
      via: ((2.5, 5.8), (1.35, 5.8), (1.35, 3)),
      corner-radius: 4pt,
    ),
    resume("sum_exit_sum", "sum_pp7", bend: 50deg),
    resume("dec_exit_dec", "sum_pp6", bend: 25deg),
  )
}

// The value that `origin` publishes to the global unknown of Gx, and the
// value that unknown settles at, read from the registered solver trace.
#let _mixed-flow-trace = read("/shared/generated/mixed-flow-shared-trace.txt").split("\n")
#let mixed-flow-published(origin) = {
  let key = "side: side to Global Gx from (" + origin + ", unit); value: sign: Gx="
  let line = _mixed-flow-trace.find(l => l.contains(key))
  assert(line != none, message: "mixed-flow-shared-trace has no side effect from " + origin)
  line.split(key).at(1).trim()
}
#let mixed-flow-final = {
  let updates = _mixed-flow-trace.filter(l => l.contains("update: side to Global Gx from"))
  assert(updates.len() > 0, message: "mixed-flow-shared-trace never updates Gx")
  updates.last().split("new: sign: Gx=").at(1).trim()
}

// The set/get program with its program global on the shared channel. Nodes and
// edge labels come from registered `--dot` output, and the values published to
// the global unknown from the registered solver trace, so the drawing fails to
// build when either changes.
#let mixed-flow-graph = {
  set text(size: 7.5pt, font: "DejaVu Sans Mono")
  let claim = "mixed-flow-shared-dot"
  let dot = read("/shared/generated/mixed-flow-shared-dot.txt").split("\n")
  let published = mixed-flow-published
  let final = mixed-flow-final
  let edge-line(a, b) = dot-edge-line(dot, claim, a, b)
  let n(pos, id, boundary: false) = node(
    pos,
    dot-label(dot-node-line(dot, claim, id)),
    stroke: 0.8pt + (if boundary { vb.accent } else { vb.neutral }),
    fill: if boundary { vb.accent.lighten(90%) } else { white },
    corner-radius: if boundary { 2pt } else { 6pt },
    inset: 3.5pt,
    name: label(id),
  )
  let lab(body, fill: vb.neutral) = text(size: 7pt, fill: fill, body)
  let intra(a, b, ..args) = edge(
    label(a),
    label(b),
    "-|>",
    stroke: 0.7pt + vb.neutral,
    label: lab(dot-label(edge-line(a, b))),
    label-sep: 2pt,
    label-side: left,
    ..args,
  )
  let call(a, b, ..args) = edge(
    label(a),
    label(b),
    "-|>",
    stroke: (paint: vb.called, thickness: 0.9pt, dash: "dashed"),
    label: lab(dot-label(edge-line(a, b)), fill: vb.called),
    label-sep: 2pt,
    ..args,
  )
  let cont(a, b) = {
    assert(edge-line(a, b).contains("label=\"continuation\""))
    edge(label(a), label(b), stroke: (paint: vb.called, thickness: 0.8pt, dash: "dotted"))
  }
  let side(a, b, body, via: (), ..args) = edge(
    label(a),
    ..via,
    label(b),
    "-|>",
    stroke: 1pt + vb.sign,
    label: body,
    label-sep: 2pt,
    corner-radius: 4pt,
    ..args,
  )
  let head(pos, name) = node(pos, text(weight: "bold", fill: vb.muted, name), stroke: none)
  diagram(
    spacing: (8mm, 4.5mm),
    head((0, -0.8), "main"),
    head((2.6, -0.8), "set"),
    head((2.6, 3.7), "get"),
    n((0, 0), "main_entry_main", boundary: true),
    n((0, 1), "main_pp4"),
    n((0, 2), "main_pp5"),
    n((0, 3), "main_pp6"),
    n((0, 4), "main_pp7"),
    n((0, 5), "main_exit_main", boundary: true),
    n((2.6, 0), "set_entry_set", boundary: true),
    n((2.6, 1), "set_pp0"),
    n((2.6, 2), "set_pp1"),
    n((2.6, 3), "set_exit_set", boundary: true),
    n((2.6, 4.5), "get_entry_get", boundary: true),
    n((2.6, 5.5), "get_pp2"),
    n((2.6, 6.5), "get_exit_get", boundary: true),
    node(
      (4.6, 2.6),
      stack(spacing: 2pt, text(weight: "bold", fill: vb.sign)[Gx], signval(final)),
      shape: fletcher.shapes.diamond,
      stroke: 1pt + vb.sign,
      fill: vb.sign.lighten(92%),
      inset: 2pt,
      name: <gx>,
    ),
    intra("main_entry_main", "main_pp4", label-side: right),
    intra("main_pp4", "main_pp5", label-side: right),
    cont("main_pp5", "main_pp6"),
    cont("main_pp6", "main_pp7"),
    intra("main_pp7", "main_exit_main", label-side: right),
    intra("set_entry_set", "set_pp0"),
    intra("set_pp0", "set_pp1"),
    intra("set_pp1", "set_exit_set"),
    intra("get_entry_get", "get_pp2"),
    intra("get_pp2", "get_exit_get"),
    call("main_pp5", "set_entry_set", label-side: right, label-pos: 0.4),
    call("main_pp6", "get_entry_get", label-side: left, label-pos: 0.62, label-sep: 5pt),
    side(
      "main_entry_main",
      "gx",
      signval(published("entry_main")),
      via: ((1.3, 0), (1.3, -1.2), (4.6, -1.2)),
      label-pos: 0.62,
      label-side: left,
    ),
    side("set_pp1", "gx", signval(published("pp1")), label-side: left),
    side("gx", "get_pp2", [read], via: ((4.6, 5.5),), label-side: left),
  )
}
