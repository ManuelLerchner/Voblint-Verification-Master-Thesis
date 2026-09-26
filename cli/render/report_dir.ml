(* A result directory that goblint's HTML frontend can browse.

   The frontend is g2html's resources/ (vendor/g2html), used unmodified. This module
   decides which documents a report consists of and where each goes; Render_xml
   writes the documents, and the graph pane's DOT is drawn here with the short
   labels and click hooks the frontend's script drives.

   Abstract states live in nodes/<id>.xml, never in DOT node labels: a product
   domain's state makes a CFG node unreadably wide when inlined.

   Everything is built from the Context_graph of the one run result, so nothing
   re-derives the CFG or parses a rendering back. *)

module G = Context_graph
module X = Render_xml

type file = { path : string; content : string }

let emit ~graph ~source_file ~source_text ~fn ~checks ~positions ~globals =
  let seg = X.xmlify source_file in
  let nodes = graph.G.nodes in
  let node_files =
    List.map
      (fun (node : G.node) ->
        {
          path = Printf.sprintf "nodes/%s.xml" node.id;
          content =
            X.node_xml ~source_file ~fn ~loc:(X.node_line positions node) ~node;
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
            (fun id ->
              List.exists (fun (n : G.node) -> n.id = id && X.is_dead n) nodes)
            ids
        then Some l
        else None)
      line_nodes
  in
  (* One graph per run covers the whole program -- procedures are clusters in it,
     not separate CFGs -- so the index names that one entry rather than listing a
     function whose own graph does not exist. *)
  ( { path = "index.xml"; content = X.index_xml ~source_file ~fns:[ fn ] }
    :: { path = "nodes/globals.xml"; content = X.globals_xml ~globals }
    :: {
         path = Printf.sprintf "files/%s.xml" seg;
         content = X.file_xml ~source_text ~checks ~line_nodes ~dead_lines;
       }
    :: {
         path = Printf.sprintf "dot/%s/%s.dot" seg fn;
         content = Render_dot.render graph;
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
