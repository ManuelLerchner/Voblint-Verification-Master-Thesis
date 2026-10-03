// Readers for registered analyzer claims (shared/claims.toml). A figure that
// states analyzer output reads it here, from the file `tools/claims.py`
// regenerates and diffs, so no verdict, state or count is typed by hand.

#import "code.typ": claim-playground

#let claim-text(name) = read("/shared/generated/" + name + ".txt")

// A claim named in prose, linked to the playground running its program at its
// settings. A pattern such as `dom-stride2-*`, and a claim the playground cannot
// replay (one stopped by a timeout, say), link to the declarations instead.
#let claim-blob = "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/writing/thesis/shared/"
#let _replayable = json("/shared/generated/vimp-claims.json")
#let claim-ref(name) = if name.contains("*") or name not in _replayable {
  link(claim-blob + "claims.toml", raw(name))
} else {
  let _ = claim-text(name)
  link(claim-playground(name), raw(name))
}

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
        // The CLI heads each active analysis's part of a state with its
        // name; the figures read single-analysis runs, whose values follow.
        if line.match(regex("^      [a-z]+:$")) == none {
          nodes.at(current).lines.push(line.trim())
        }
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

// A `--trace --format jsonl` report, split into the phases a thesis table
// narrates. Phase boundaries follow the solver's own structure:
//   descent    the first queries, before any global is read
//   root-seed  the program entry reads its seed
//   pass       one evaluation of a call's continuation (starts at a route, or
//              at the re-evaluation after a flush); a seed published before
//              the call's first local query belongs to its pass
//   flush      a buffered side effect that changes its seed, issued after the
//              call's queries
// Contexts are named c0, c1, ... in order of appearance; `arrows` maps
// "source -> target" (queries and side effects) to the phases that took it.
#let claim-trace(name) = {
  let events = claim-text(name)
    .split("\n")
    .filter(l => l.starts-with("{\"step\""))
    .map(l => json(bytes(l)))
  let ctx-key(c) = if c.kind == "entry_state" {
    "entry:" + c.values.join(",", default: "")
  } else if (
    c.kind == "call_string"
  ) { "call:" + c.sites.join(",", default: "") } else if c.kind == "unit" { "unit" } else {
    panic("unknown trace context kind: " + c.kind)
  }
  let ctxs = ()
  for ev in events {
    for f in ("current", "target", "unknown", "call", "context") {
      let v = ev.at(f, default: none)
      let c = if v == none { none } else if f == "context" { v } else {
        v.at("context", default: none)
      }
      if c != none and ctx-key(c) not in ctxs { ctxs.push(ctx-key(c)) }
    }
  }
  let ctx(c) = "c" + str(ctxs.position(k => k == ctx-key(c)))
  let unknown(u) = if u.kind == "local" { u.node + "@" + ctx(u.context) } else if (
    u.kind == "activation_seed"
  ) { "Seed(" + u.procedure + ")@" + ctx(u.context) } else { u.kind }
  let phases = ()
  let arrows = (:)
  for (i, ev) in events.enumerate() {
    let k = ev.event
    let last = if phases.len() > 0 { phases.last() } else { none }
    let next = events.at(i + 1, default: (event: none)).event
    let start = if last == none { "descent" } else if (
      k == "query_global" and last.kind == "descent"
    ) {
      "root-seed"
    } else if k == "route" and not (last.kind == "pass" and last.route == none) {
      "pass"
    } else if k == "query_local" and last.kind == "flush" { "pass" } else if (
      k == "side"
        and next == "update_global"
        and not (
          last.kind == "pass"
            and last.route != none
            and not last.events.any(e => e.event == "query_local")
        )
    ) { "flush" } else { none }
    if start != none {
      phases.push((kind: start, route: none, events: ()))
    }
    let ev = ev
    for f in ("current", "target", "unknown", "call") {
      if f in ev { ev.insert(f, unknown(ev.at(f))) }
    }
    if k == "route" {
      ev.insert("context", ctx(ev.context))
      phases.last().route = ev
    }
    phases.last().events.push(ev)
    if k in ("query_local", "query_global", "side") {
      let key = ev.current + " -> " + ev.target
      let seen = arrows.at(key, default: ())
      if phases.len() not in seen { seen.push(phases.len()) }
      arrows.insert(key, seen)
    }
  }
  (phases: phases, arrows: arrows)
}
