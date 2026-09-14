(* GraphViz rendering of a contextual CFG.

   Draws the Context_graph built from a run result. Presentation is deliberately
   on this side of the trust boundary: no soundness theorem covers how a graph is
   drawn. The graph carries structure and findings -- identifiers, labels, state
   lines, a status, an edge role and its wording -- and every styling decision below
   is this file's own.

   One drawing serves every consumer -- --dot, the browser and the HTML report's graph
   pane: each node carries its state and findings, and the id/URL hooks the report
   frontend selects nodes by are emitted always, since a consumer that does not
   listen for them ignores them.

   Layout is driven primarily by local control flow. Intra-procedural and
   continuation edges strongly constrain ranks, while call-entry edges provide
   a weaker cross-context ordering. Resume and global dependency edges are
   overlays and do not affect ranking. This keeps each context cluster primarily
   vertical while still arranging callees near their callers.
*)

module G = Context_graph

(* DOT's own line separator inside a quoted label: a literal backslash-n. *)
let esc_nl = "\\n"

let escape s = String.concat "\\\"" (String.split_on_char '"' s)

let boxed = "shape=box,style=\"rounded,filled\""

(* Only a semantic finding overrides a node's structural appearance. *)
let node_attrs (n : G.node) =
  match n.status, n.kind with
  | Some G.Proved, _ -> boxed ^ ",color=darkgreen,penwidth=2,fillcolor=palegreen"
  | Some G.Refuted, _ -> boxed ^ ",color=firebrick,penwidth=2,fillcolor=mistyrose"
  | Some G.Unknown, _ -> boxed ^ ",color=darkgoldenrod,penwidth=2,fillcolor=lightgoldenrod1"
  | Some G.Unreachable, _ ->
      "shape=box,style=\"rounded,dashed,filled\",color=gray45,fillcolor=gray90,fontcolor=gray35"
  | None, G.Point -> "shape=box,style=filled,fillcolor=lightgreen"
  | None, _ -> "shape=doublecircle,color=orange,style=filled,fillcolor=lightyellow"

let node_label (n : G.node) =
  "\"" ^ String.concat esc_nl (List.map escape (n.label :: n.lines)) ^ "\""

(* Ranking priorities are deliberately asymmetric: intra and call-to-return edges
   strongly order local flow, enter edges weakly place callees near their calls,
   and combine edges are return overlays that do not constrain ranks. *)
let edge_attrs (e : G.edge) =
  let text = escape e.text in
  match e.kind with
  | G.Intra -> Printf.sprintf "weight=20,label=\"%s\"" text
  | G.Enter ->
      Printf.sprintf "color=purple,penwidth=2,weight=6,minlen=2,label=\"call %s\"" text
  | G.Combine ->
      let label = if e.text = "" then "resume" else "resume / " ^ text in
      Printf.sprintf
        "style=dashed,color=blue,constraint=false,weight=0,arrowsize=0.65,penwidth=1,xlabel=\"%s\""
        label
  | G.Call_to_return -> "style=dashed,color=gray40,weight=20,label=\"continuation\""

let render (graph : G.t) : string =
  let by_id = Hashtbl.create 64 in
  List.iter (fun (n : G.node) -> Hashtbl.replace by_id n.id n) graph.nodes;
  let buf = Buffer.create 4096 in
  Buffer.add_string buf "digraph AnalysisCFG {\n";
  (* No newrank: each context cluster should follow its own top-to-bottom CFG. *)
  Buffer.add_string buf
    "  graph \
     [rankdir=TB,ordering=out,splines=polyline,nodesep=0.5,ranksep=0.8,remincross=true,mclimit=4,fontname=\"Menlo\"];\n";
  (* graphviz turns id/URL into <g id="a_N"><a xlink:href="javascript:show_info('N')">,
     the handle the report frontend loads and highlights a node by. *)
  Buffer.add_string buf
    "  node \
     [shape=box,style=filled,fillcolor=lightgreen,fontname=\"Menlo\",id=\"\\N\",URL=\"javascript:show_info('\\N');\"];\n";
  Buffer.add_string buf "  edge [fontname=\"Menlo\",fontsize=10,arrowsize=0.8];\n";
  List.iter
    (fun (c : G.cluster) ->
      Buffer.add_string buf (Printf.sprintf "  subgraph %s {\n" c.cluster_id);
      Buffer.add_string buf (Printf.sprintf "    label=\"%s\";\n" (escape c.cluster_label));
      Buffer.add_string buf "    style=rounded; color=gray70; penwidth=1;\n";
      List.iter
        (fun id ->
          let n = Hashtbl.find by_id id in
          Buffer.add_string buf
            (Printf.sprintf "    %s [%s,label=%s];\n" id (node_attrs n) (node_label n)))
        c.members;
      Buffer.add_string buf "  }\n")
    graph.clusters;
  List.iter
    (fun (e : G.edge) ->
      Buffer.add_string buf (Printf.sprintf "  %s -> %s [%s];\n" e.src e.dst (edge_attrs e)))
    graph.edges;
  Buffer.add_string buf "}\n";
  Buffer.contents buf
