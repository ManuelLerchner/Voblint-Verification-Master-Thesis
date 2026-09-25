// Readers for registered analyzer claims (shared/claims.toml). A figure that
// states analyzer output reads it here, from the file `tools/claims.py`
// regenerates and diffs, so no verdict, state or count is typed by hand.

#let claim-text(name) = read("/shared/generated/" + name + ".txt")

// The run was stopped by `--timeout`: the report is the CLI's rejection line.
#let claim-timed-out(name) = claim-text(name).contains("did not finish within")

// One row of the check table of a textual report:
// (location, point, condition, verdict, state).
#let claim-check(name, cond) = {
  let cells = claim-text(name)
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    .find(c => c.len() == 5 and c.at(2) == cond)
  assert(cells != none, message: "claim " + name + " has no check " + cond)
  cells
}

// A `--graph-snapshot` report, parsed into
//   clusters: ((id, proc, ctx, nodes), ...)   one per procedure copy
//   nodes:    id -> (label, status, lines)    status is the bracketed marker
//   edges:    ((src, dst, label), ...)
// Frontend diagnostics printed before the snapshot are skipped.
#let claim-snapshot(name) = {
  let clusters = ()
  let nodes = (:)
  let edges = ()
  let section = none
  let current = none
  for line in claim-text(name).split("\n") {
    if line == "clusters:" or line == "nodes:" or line == "edges:" {
      section = line.slice(0, -1)
      continue
    }
    if section == "clusters" {
      let m = line.match(regex("^  (cluster_ctx_\d+): (\S+) / (.*)$"))
      if m != none {
        clusters.push((
          id: m.captures.at(0),
          proc: m.captures.at(1),
          ctx: m.captures.at(2),
          nodes: (),
        ))
      } else if line.starts-with("    ") and clusters.len() > 0 {
        clusters.last().nodes.push(line.trim())
      }
    } else if section == "nodes" {
      let m = line.match(regex("^  (\S+): (\S+)(?: \[([a-z]+)\])?$"))
      if m != none {
        current = m.captures.at(0)
        nodes.insert(current, (label: m.captures.at(1), status: m.captures.at(2), lines: ()))
      } else if line.starts-with("      ") and current != none {
        nodes.at(current).lines.push(line.trim())
      }
    } else if section == "edges" {
      let m = line.match(regex("^  (\S+) -> (\S+): (.*)$"))
      if m != none {
        edges.push((src: m.captures.at(0), dst: m.captures.at(1), label: m.captures.at(2)))
      }
    }
  }
  (clusters: clusters, nodes: nodes, edges: edges)
}

// The cluster holding a node id.
#let snapshot-cluster-of(snap, id) = snap.clusters.find(c => id in c.nodes)

// The verdict of a check across every copy that lists it: UNKNOWN if some copy
// leaves it open, otherwise the one marker all copies agree on.
#let snapshot-verdict(snap, cond) = {
  let marks = snap.nodes.values().filter(n => ("check " + cond) in n.lines).map(n => n.status)
  assert(marks.len() > 0, message: "no node checks " + cond)
  if "unknown" in marks { "UNKNOWN" } else if marks.all(m => m == marks.first()) {
    upper(marks.first())
  } else { "UNKNOWN" }
}
