// The compiled graph of the recursive sum/dec program, shared by the
// compiled-graph figure and the trace figure. Node names and edge labels are
// read from registered `--dot` output, so a drawing fails to build when the
// compiler's output changes. Lines are matched up to the context suffix, which
// numbers the analysis contexts and does not change the graph.
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "theme.typ": vb

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
