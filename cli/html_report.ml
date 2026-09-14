(* A result directory that goblint's HTML frontend can browse.

   The frontend is g2html's resources/ (vendor/g2html), used unmodified. This module
   decides which documents a report consists of and where each goes; Xml_render
   writes the documents, and the graph pane's DOT is drawn here with the short
   labels and click hooks the frontend's script drives.

   Abstract states live in nodes/<id>.xml, never in DOT node labels: a product
   domain's state makes a CFG node unreadably wide when inlined.

   Everything is built from the Analysis_graph of one run result per domain, so
   nothing re-derives the CFG or parses a rendering back. *)

module G = Analysis_graph
module X = Xml_render

type file = { path : string; content : string }

(* Fill colour by finding, not by structural role: this graph exists to be
   read for verdicts. Dead nodes take goblint's own orange (cfgTools'
   fprint_fundec_html_dot paints unreachable nodes that colour). *)
let node_fill (node : G.node) =
  match node.status with
  | Some G.Proved -> "#cdebc5"
  | Some G.Refuted -> "#f5b8b8"
  | Some G.Unknown -> "#e8e8e8"
  | Some G.Unreachable -> "orange"
  | None -> (match node.kind with G.Point -> "white" | _ -> "#eef2f7")

let node_shape (node : G.node) =
  match node.kind with G.Point -> "shape=box" | _ -> "shape=oval"

let dot_escape s = String.concat "\\\"" (String.split_on_char '"' s)

let source_fragment lines (line, column, end_line, end_column, _) =
  if line < 1 || end_line < line || end_line > Array.length lines then None
  else
    let pieces =
      List.init
        (end_line - line + 1)
        (fun i ->
          let text = lines.(line + i - 1) in
          let first = if i = 0 then column - 1 else 0 in
          let last =
            if line + i = end_line then end_column - 1 else String.length text
          in
          if first < 0 || last < first || last > String.length text then None
          else Some (String.trim (String.sub text first (last - first))))
    in
    if List.exists Option.is_none pieces then None
    else Some (String.concat " " (List.filter_map Fun.id pieces))

(* Short labels only, plus the id/URL hooks goblint's script.js drives:
   graphviz turns them into <g id="a_N"><a xlink:href="javascript:show_info('N')">,
   which is the handle it selects on to load and highlight a node. *)
let html_dot ~source_text ~positions graph =
  let by_id = Hashtbl.create 64 in
  List.iter (fun (n : G.node) -> Hashtbl.replace by_id n.id n) graph.G.nodes;
  (* A routed call is explained by its enter/combine edges. Only unrouted
     calls need a source annotation to keep their operation visible. *)
  let call_sites = Hashtbl.create 32 in
  let routed_calls = Hashtbl.create 32 in
  List.iter
    (fun (e : G.edge) ->
      match e.kind with
      | G.Call_to_return -> Hashtbl.replace call_sites e.src ()
      | G.Enter -> Hashtbl.replace routed_calls e.src ()
      | _ -> ())
    graph.G.edges;
  let source_lines = Array.of_list (String.split_on_char '\n' source_text) in
  let node_label (node : G.node) =
    let name = node.label in
    if
      (not (Hashtbl.mem call_sites node.id))
      || Hashtbl.mem routed_calls node.id
    then dot_escape name
    else
      match
        Option.bind (X.node_line positions node) (source_fragment source_lines)
      with
      | None | Some "" -> dot_escape name
      | Some call -> dot_escape name ^ "\\n" ^ dot_escape call
  in
  let buf = Buffer.create 4096 in
  Buffer.add_string buf "digraph AnalysisCFG {\n";
  Buffer.add_string buf
    "  graph \
     [rankdir=TB,newrank=true,splines=polyline,nodesep=0.4,ranksep=0.5,fontname=\"Menlo\"];\n";
  Buffer.add_string buf
    "  node \
     [shape=box,style=filled,fillcolor=white,fontname=\"Menlo\",fontsize=11,id=\"\\N\",URL=\"javascript:show_info('\\N');\"];\n";
  Buffer.add_string buf
    "  edge [fontname=\"Menlo\",fontsize=9,arrowsize=0.7];\n";
  List.iter
    (fun (cluster : G.cluster) ->
      let visible_nodes = cluster.members in
      if visible_nodes <> [] then begin
        Buffer.add_string buf
          (Printf.sprintf "  subgraph %s {\n" cluster.cluster_id);
        Buffer.add_string buf
          (Printf.sprintf "    label=\"%s\";\n"
             (dot_escape cluster.cluster_label));
        Buffer.add_string buf "    style=rounded; color=gray70;\n";
        List.iter
          (fun nid ->
            match Hashtbl.find_opt by_id nid with
            | None -> ()
            | Some node ->
                Buffer.add_string buf
                  (Printf.sprintf "    %s [%s,fillcolor=\"%s\",label=\"%s\"];\n"
                     nid (node_shape node) (node_fill node) (node_label node)))
          visible_nodes;
        Buffer.add_string buf "  }\n"
      end)
    graph.G.clusters;
  List.iter
    (fun (e : G.edge) ->
      let label =
        match e.kind with
        | G.Enter -> "call " ^ e.text
        | G.Combine -> if e.text = "" then "resume" else "resume / " ^ e.text
        | G.Call_to_return -> "continuation"
        | G.Intra -> e.text
      in
      let style = if e.kind = G.Call_to_return then "style=dashed,color=gray40," else "" in
      Buffer.add_string buf
        (Printf.sprintf "  %s -> %s [%slabel=\"%s\"];\n" e.src e.dst style
           (dot_escape label)))
    graph.G.edges;
  Buffer.add_string buf "}\n";
  Buffer.contents buf

(* graphs is (domain name, graph), the first being the one the CFG is drawn
   from. Node identifiers are built from the CFG and the context, both of which
   every listed domain shares, so merging the others' states in by identifier is
   sound -- and a node one domain does not cover simply contributes no block. *)
let emit ~graphs ~source_file ~source_text ~fn ~checks ~positions ~globals =
  let seg = X.xmlify source_file in
  let _, graph = List.hd graphs in
  let index =
    List.map
      (fun (name, g) ->
        let by_id = Hashtbl.create 64 in
        List.iter (fun (n : G.node) -> Hashtbl.replace by_id n.id n) g.G.nodes;
        (name, by_id))
      graphs
  in
  let nodes = graph.G.nodes in
  let node_files =
    List.map
      (fun (node : G.node) ->
        let id = node.id in
        let blocks =
          List.filter_map
            (fun (name, by_id) ->
              Option.map (fun n -> (name, n)) (Hashtbl.find_opt by_id id))
            index
        in
        {
          path = Printf.sprintf "nodes/%s.xml" id;
          content =
            X.node_xml ~source_file ~fn ~loc:(X.node_line positions node) ~blocks;
        })
      nodes
  in
  let dead = List.length (List.filter X.is_dead nodes) in
  (* Grouped once here rather than searched per line: the listing walks every
     line of the file, and most lines have no node at all. *)
  let line_nodes = Hashtbl.create 64 in
  List.iter
    (fun node ->
      match X.node_line positions node with
      | None -> ()
      | Some (l, _, _, _, _) ->
          Hashtbl.replace line_nodes l
            (node.G.id
            :: Option.value ~default:[] (Hashtbl.find_opt line_nodes l)))
    nodes;
  let line_nodes =
    Hashtbl.fold (fun l ids acc -> (l, List.rev ids) :: acc) line_nodes []
  in
  let dead_lines =
    List.filter_map
      (fun (l, ids) ->
        if
          List.for_all
            (fun id -> List.exists (fun (n : G.node) -> n.id = id && X.is_dead n) nodes)
            ids
        then Some l
        else None)
      line_nodes
  in
  (* One graph per run covers the whole program -- procedures are clusters in it,
     not separate CFGs -- so the index names that one entry rather than listing a
     function whose own graph does not exist. *)
  ( { path = "index.xml"; content = X.index_xml ~source_file ~fns:[ fn ] }
    :: { path = "nodes/globals.xml"; content = X.globals_xml ~blocks:globals }
    :: {
         path = Printf.sprintf "files/%s.xml" seg;
         content = X.file_xml ~source_text ~checks ~line_nodes ~dead_lines;
       }
    :: {
         path = Printf.sprintf "dot/%s/%s.dot" seg fn;
         content = html_dot ~source_text ~positions graph;
       }
    :: (node_files
       @ List.mapi
           (fun k c ->
             {
               path = Printf.sprintf "warn/warn%d.xml" (k + 1);
               content = X.warn_xml ~source_file c;
             })
           checks),
    List.length nodes,
    dead )
