(* GraphViz rendering of a solved analysis graph.

   Consumes the export_graph the Isabelle side returns
   (State_Report_Graph's *_export_auto family) and produces the same DOT
   the Isabelle renderer used to produce. Presentation is deliberately on this
   side of the trust boundary: no soundness theorem covers how a graph is
   drawn, and DOT syntax built inside Isabelle compiled to per-character
   literal lists that dominated the generated OCaml without buying anything.

   What the export carries is structure and findings -- identifiers, labels,
   state lines, a node_status, an edge role and its payload. Every styling
   decision below is this file's own.

   Source nodes remain part of the exported graph structure but are not drawn.
   Source text is presented separately by frontends that need it.

   Layout is driven primarily by local control flow. Intra-procedural and
   continuation edges strongly constrain ranks, while call-entry edges provide
   a weaker cross-context ordering. Resume and global dependency edges are
   overlays and do not affect ranking. This keeps each context cluster primarily
   vertical while still arranging callees near their callers.
*)

module C = Voblint_CLI.Generated

(* DOT's own line separator inside a quoted label: a literal backslash-n, not
   a newline. The same two characters the export joins label lines with
   (join_esc_nl), so a multi-line label survives the round trip. *)
let esc_nl = "\\n"
let label_text s = String.concat esc_nl (String.split_on_char '\n' s)

let style_of_status = function
  | C.NS_Plain ->
      "shape=box,style=\"rounded,filled\",color=gray35,fillcolor=lightgreen"
  | C.NS_Proved ->
      "shape=box,style=\"rounded,filled\",color=darkgreen,penwidth=2,fillcolor=palegreen"
  | C.NS_Refuted ->
      "shape=box,style=\"rounded,filled\",color=firebrick,penwidth=2,fillcolor=mistyrose"
  | C.NS_Unknown ->
      "shape=box,style=\"rounded,filled\",color=darkgoldenrod,penwidth=2,fillcolor=lightgoldenrod1"
  | C.NS_Unreachable ->
      "shape=box,style=\"rounded,dashed,filled\",color=gray45,fillcolor=gray90,fontcolor=gray35"
  | C.NS_Exit ->
      "shape=doublecircle,color=orange,style=filled,fillcolor=lightyellow"

(* An annotation overrides the structural styling, which is why xn_status is
   consulted first; the export leaves it None on global and source nodes, where
   the structural role is the only thing that decides. *)
let structural_attrs node =
  match C.xn_kind node with
  | C.XN_Entry | C.XN_ProcEntry ->
      "shape=doublecircle,color=orange,style=filled,fillcolor=lightyellow"
  | C.XN_Exit | C.XN_ProcExit ->
      "shape=doublecircle,color=orange,style=filled,fillcolor=lightyellow"
  | C.XN_Point -> "shape=box,style=filled,fillcolor=lightgreen"
  | C.XN_Global -> "shape=note,width=2.2,fixedsize=false"
  | C.XN_Source -> "shape=plain"

(* NS_Plain carries content, not a semantic finding. In particular the
   unit-context/full-state path annotates every live node with NS_Plain, while
   the entry-state and call-string builders carry ordinary state in xn_lines
   and leave xn_status unset. Treating NS_Plain as a style override therefore
   made the same structural node render differently solely because of the
   context policy: entries/exits became ordinary green boxes in Ctx_None.

   Only an actual semantic status overrides the node's structural appearance.
   Plain state annotations and absent annotations share the same structural
   style. *)
let is_dead node =
  C.xn_status node = Some C.NS_Unreachable
  || List.mem "unreachable" (C.xn_lines node)

let node_attrs node =
  if is_dead node then style_of_status C.NS_Unreachable
  else
    match C.xn_status node with
    | None | Some C.NS_Plain -> structural_attrs node
    | Some status -> style_of_status status

(* xe_label carries the edge's content without the wording that names its role
   -- "f(x)", not "call f(x)" -- so the phrasing below is this renderer's.

   Ranking priorities are deliberately asymmetric:

     - intra edges strongly determine ordinary local CFG flow;
     - call-to-return edges strongly keep the caller's continuation ordered;
     - enter edges weakly order callees below and near their call sites;
     - combine edges are visual return overlays and do not constrain ranks;
     - global dependencies are likewise non-ranking overlays.

   The weight difference lets local CFG structure dominate while still giving
   GraphViz enough cross-cluster information to avoid packing every context
   independently. *)
let edge_attrs edge =
  let payload = C.xe_label edge in

  match C.xe_kind edge with
  | C.XE_Intra -> Printf.sprintf "weight=20,label=\"%s\"" payload
  | C.XE_Enter ->
      Printf.sprintf
        "color=purple,penwidth=2,weight=6,minlen=2,label=\"call %s\"" payload
  | C.XE_Combine ->
      let text = if payload = "" then "resume" else "resume / " ^ payload in
      Printf.sprintf
        "style=dashed,color=blue,constraint=false,weight=0,arrowsize=0.65,penwidth=1,xlabel=\"%s\""
        text
  | C.XE_CallToReturn ->
      "style=dashed,color=gray40,weight=20,label=\"continuation\""
  | C.XE_GlobalRead ->
      "style=dotted,color=gray,constraint=false,label=\"read global\""
  | C.XE_GlobalWrite ->
      "style=dotted,color=gray,constraint=false,label=\"write global\""

(* A node's full DOT label is its name line followed by its content lines,
   which is how the two arrive split in the export. *)
let node_label node =
  let lines = C.xn_label node :: C.xn_lines node in

  "\"" ^ label_text (String.concat esc_nl lines) ^ "\""

let has_duplicates xs =
  let seen = Hashtbl.create 64 in

  List.exists
    (fun x ->
      if Hashtbl.mem seen x then true
      else begin
        Hashtbl.add seen x ();
        false
      end)
    xs

(* The same well-formedness gate the Isabelle renderer applied before drawing:
   distinct clusters and nodes, and no edge pointing outside the node set.

   This checks the complete exported graph before presentation filtering.
   Source nodes are intentionally still part of that graph even though the
   renderer does not draw them. *)
let well_formed graph =
  let nodes = C.xg_nodes graph in

  let ids = List.map C.xn_id nodes in

  let known = Hashtbl.create 64 in

  List.iter (fun id -> Hashtbl.replace known id ()) ids;

  (not (has_duplicates ids))
  && (not (has_duplicates (List.map C.xc_id (C.xg_clusters graph))))
  && List.for_all
       (fun edge ->
         Hashtbl.mem known (C.xe_src edge) && Hashtbl.mem known (C.xe_dst edge))
       (C.xg_edges graph)

(* Raising rather than emitting a well-formed-looking placeholder: the only
   assertion the suite makes about --dot is that stdout starts with
   "digraph AnalysisCFG", which a placeholder satisfies at exit 0, so the
   guard's failure was undetectable by the test that exists to check it. *)
let render (graph : unit C.export_graph_ext) : string =
  if not (well_formed graph) then
    failwith
      "analysis graph is not well formed: duplicate node or cluster id, or an \
       edge outside the node set"
  else begin
    let by_id = Hashtbl.create 64 in

    List.iter
      (fun node -> Hashtbl.replace by_id (C.xn_id node) node)
      (C.xg_nodes graph);

    let is_source_node id =
      match Hashtbl.find_opt by_id id with
      | Some node -> C.xn_kind node = C.XN_Source
      | None -> false
    in

    let buf = Buffer.create 4096 in

    Buffer.add_string buf "digraph AnalysisCFG {\n";

    (* Do not use newrank here. Cross-cluster rank unification works against
       the desired presentation: each context cluster should primarily follow
       its own local top-to-bottom CFG. *)
    Buffer.add_string buf
      "  graph \
       [rankdir=TB,ordering=out,splines=polyline,nodesep=0.5,ranksep=0.8,remincross=true,mclimit=4,fontname=\"Menlo\"];\n";

    Buffer.add_string buf
      "  node [shape=box,style=filled,fillcolor=lightgreen,fontname=\"Menlo\"];\n";

    Buffer.add_string buf
      "  edge [fontname=\"Menlo\",fontsize=10,arrowsize=0.8];\n";

    List.iter
      (fun cluster ->
        let visible_nodes =
          List.filter
            (fun node_id -> not (is_source_node node_id))
            (C.xc_nodes cluster)
        in

        (* Do not emit an empty cluster. In particular, this removes the
            source-only cluster instead of leaving an empty "Source" box. *)
        if visible_nodes <> [] then begin
          Buffer.add_string buf
            (Printf.sprintf "  subgraph %s {\n" (C.xc_id cluster));

          Buffer.add_string buf
            (Printf.sprintf "    label=\"%s\";\n" (C.xc_label cluster));

          Buffer.add_string buf "    style=rounded; color=gray70; penwidth=1;\n";

          List.iter
            (fun node_id ->
              match Hashtbl.find_opt by_id node_id with
              | None -> ()
              | Some node ->
                  Buffer.add_string buf
                    (Printf.sprintf "    %s [%s,label=%s];\n" node_id
                       (node_attrs node) (node_label node)))
            visible_nodes;

          Buffer.add_string buf "  }\n"
        end)
      (C.xg_clusters graph);

    List.iter
      (fun edge ->
        (* GraphViz creates undeclared nodes implicitly when an edge mentions
            them, so suppress edges touching hidden source nodes as well. *)
        if not (is_source_node (C.xe_src edge) || is_source_node (C.xe_dst edge))
        then
          Buffer.add_string buf
            (Printf.sprintf "  %s -> %s [%s];\n" (C.xe_src edge) (C.xe_dst edge)
               (edge_attrs edge)))
      (C.xg_edges graph);

    Buffer.add_string buf "}\n";

    Buffer.contents buf
  end
