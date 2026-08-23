(* GraphViz rendering of a solved analysis graph.

   Consumes the export_graph the Isabelle side returns
   (State_Report_GraphViz's *_export_auto family) and produces the same DOT
   the Isabelle renderer used to produce. Presentation is deliberately on this
   side of the trust boundary: no soundness theorem covers how a graph is
   drawn, and DOT syntax built inside Isabelle compiled to per-character
   literal lists that dominated the generated OCaml without buying anything.

   What the export carries is structure and findings -- identifiers, labels,
   state lines, a node_status, an edge role and its payload. Every styling
   decision below is this file's own. *)

module C = Voblint_CLI.Core

(* DOT's own line separator inside a quoted label: a literal backslash-n, not
   a newline. Matches join_gv_nl/graphviz_label_text. *)
let gv_nl = "\\n"

let label_text s = String.concat gv_nl (String.split_on_char '\n' s)

let html_text s =
  let buf = Buffer.create (String.length s * 2) in
  String.iter
    (fun ch ->
       Buffer.add_string buf
         (match ch with
          | '\n' -> "<BR ALIGN=\"LEFT\"/>"
          | ' ' -> "&#160;"
          | '&' -> "&amp;"
          | '<' -> "&lt;"
          | '>' -> "&gt;"
          | c -> String.make 1 c))
    s;
  Buffer.contents buf

let ensure_trailing_nl s =
  if s = "" || s.[String.length s - 1] <> '\n' then s ^ "\n" else s

(* The source box is a GraphViz HTML-like label, so it is spliced unquoted. *)
let source_html_label src =
  "<<TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLPADDING=\"8\"><TR><TD ALIGN=\"LEFT\" \
   WIDTH=\"260\" FIXEDSIZE=\"FALSE\"><FONT FACE=\"Menlo\" POINT-SIZE=\"10\">"
  ^ html_text (ensure_trailing_nl src)
  ^ "</FONT></TD></TR></TABLE>>"

let style_of_status = function
  | C.NS_Plain -> "shape=box,style=filled,fillcolor=lightgreen"
  | C.NS_Proved -> "shape=box,style=filled,fillcolor=darkgreen,fontcolor=white"
  | C.NS_Refuted -> "shape=box,style=filled,fillcolor=red,fontcolor=white"
  | C.NS_Unknown -> "shape=box,style=filled,fillcolor=gray70"
  | C.NS_Unreachable -> "shape=box,style=filled,fillcolor=gray40,fontcolor=white"
  | C.NS_Exit -> "shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray"

(* An annotation overrides the structural styling, which is why xn_status is
   consulted first; the export leaves it None on global and source nodes, where
   the structural role is the only thing that decides. *)
let node_attrs node =
  match C.xn_status node with
  | Some status -> style_of_status status
  | None ->
    (match C.xn_kind node with
     | C.XN_Entry | C.XN_ProcEntry ->
       "shape=doublecircle,color=green,style=filled,fillcolor=lightyellow"
     | C.XN_Exit | C.XN_ProcExit ->
       "shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray"
     | C.XN_Point -> "shape=box,style=filled,fillcolor=lightgreen"
     | C.XN_Global -> "shape=note,width=2.2,fixedsize=false"
     | C.XN_Source -> "shape=plain")

(* xe_label carries the edge's content without the wording that names its role
   -- "f(x)", not "call f(x)" -- so the phrasing below is this renderer's. *)
let edge_attrs edge =
  let payload = C.xe_label edge in
  match C.xe_kind edge with
  | C.XE_Intra -> Printf.sprintf "label=\"%s\"" payload
  | C.XE_Enter ->
    Printf.sprintf "color=purple,penwidth=2,weight=10,label=\"call %s\"" payload
  | C.XE_Combine ->
    let text = if payload = "" then "resume" else "resume / " ^ payload in
    Printf.sprintf "style=dashed,color=blue,constraint=false,xlabel=\"%s\"" text
  | C.XE_CallToReturn ->
    "style=dotted,color=gray40,constraint=false,label=\"resume-site\""
  | C.XE_GlobalRead -> "style=dotted,color=gray,label=\"read global\""
  | C.XE_GlobalWrite -> "style=dotted,color=gray,label=\"write global\""

(* A node's full DOT label is its name line followed by its content lines,
   which is how the two arrive split in the export. The HTML report puts them
   in different places; here they are one attribute again. *)
let node_label node =
  match C.xn_kind node with
  | C.XN_Source -> source_html_label (String.concat "\n" (C.xn_lines node))
  | _ ->
    let lines = C.xn_label node :: C.xn_lines node in
    "\"" ^ label_text (String.concat gv_nl lines) ^ "\""

let has_duplicates xs =
  let seen = Hashtbl.create 64 in
  List.exists
    (fun x -> if Hashtbl.mem seen x then true else (Hashtbl.add seen x (); false))
    xs

(* The same well-formedness gate the Isabelle renderer applied before drawing:
   distinct clusters and nodes, and no edge pointing outside the node set. *)
let well_formed graph =
  let nodes = C.xg_nodes graph in
  let ids = List.map C.xn_id nodes in
  let known = Hashtbl.create 64 in
  List.iter (fun i -> Hashtbl.replace known i ()) ids;
  (not (has_duplicates ids))
  && (not (has_duplicates (List.map C.xc_id (C.xg_clusters graph))))
  && List.for_all
       (fun e -> Hashtbl.mem known (C.xe_src e) && Hashtbl.mem known (C.xe_dst e))
       (C.xg_edges graph)

let render (graph : unit C.export_graph_ext) : string =
  if not (well_formed graph) then "digraph AnalysisCFG { invalid_graph }\n"
  else begin
    let by_id = Hashtbl.create 64 in
    List.iter (fun n -> Hashtbl.replace by_id (C.xn_id n) n) (C.xg_nodes graph);
    let buf = Buffer.create 4096 in
    Buffer.add_string buf "digraph AnalysisCFG {\n";
    Buffer.add_string buf
      "  graph [rankdir=TB,newrank=true,splines=polyline,nodesep=0.5,\
       ranksep=0.7,fontname=\"Menlo\"];\n";
    Buffer.add_string buf
      "  node [shape=box,style=filled,fillcolor=lightgreen,fontname=\"Menlo\"];\n";
    Buffer.add_string buf
      "  edge [fontname=\"Menlo\",fontsize=10,arrowsize=0.8];\n";
    List.iter
      (fun cluster ->
         Buffer.add_string buf (Printf.sprintf "  subgraph %s {\n" (C.xc_id cluster));
         Buffer.add_string buf
           (Printf.sprintf "    label=\"%s\";\n" (C.xc_label cluster));
         Buffer.add_string buf "    style=rounded; color=gray70; penwidth=1;\n";
         List.iter
           (fun nid ->
              match Hashtbl.find_opt by_id nid with
              | None -> ()
              | Some node ->
                Buffer.add_string buf
                  (Printf.sprintf "    %s [%s,label=%s];\n" nid (node_attrs node)
                     (node_label node)))
           (C.xc_nodes cluster);
         Buffer.add_string buf "  }\n")
      (C.xg_clusters graph);
    List.iter
      (fun e ->
         Buffer.add_string buf
           (Printf.sprintf "  %s -> %s [%s];\n" (C.xe_src e) (C.xe_dst e) (edge_attrs e)))
      (C.xg_edges graph);
    Buffer.add_string buf "}\n";
    Buffer.contents buf
  end
