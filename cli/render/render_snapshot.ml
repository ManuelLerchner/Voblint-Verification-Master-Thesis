(* The regression snapshot of a contextual CFG: deterministic plain text, one fact per
   line, so a fixture diff names exactly what changed. Clusters list their members,
   nodes their status and state lines, edges their role and wording. *)

module G = Context_graph

let status_text = function
  | None -> ""
  | Some G.Proved -> " [proved]"
  | Some G.Refuted -> " [refuted]"
  | Some G.Unknown -> " [unknown]"
  | Some G.Unreachable -> " [unreachable]"

let edge_kind_text = function
  | G.Intra -> ""
  | G.Enter -> "enter "
  | G.Combine -> "combine "
  | G.Call_to_return -> "call-to-return "

let render (graph : G.t) =
  let buf = Buffer.create 4096 in
  let line fmt = Printf.ksprintf (fun s -> Buffer.add_string buf s; Buffer.add_char buf '\n') fmt in
  line "clusters:";
  List.iter
    (fun (c : G.cluster) ->
      line "  %s: %s" c.cluster_id c.cluster_label;
      List.iter (line "    %s") c.members)
    graph.clusters;
  line "";
  line "nodes:";
  List.iter
    (fun (n : G.node) ->
      line "  %s: %s%s" n.id n.label (status_text n.status);
      List.iter (line "      %s") n.lines)
    graph.nodes;
  line "";
  line "edges:";
  List.iter
    (fun (e : G.edge) ->
      line "  %s -> %s: %s%s" e.src e.dst (edge_kind_text e.kind) e.text)
    graph.edges;
  Buffer.contents buf
