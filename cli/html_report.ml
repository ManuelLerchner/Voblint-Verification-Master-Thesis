(* A result directory that goblint's HTML frontend can browse.

   The frontend is g2html's resources/ (vendor/g2html), used unmodified: this
   module writes only the XML and graph artifacts its stylesheets already
   consume, in the layout goblint's own result=html output produces.

     index.xml                  report.xsl   -- entry point
     nodes/<id>.xml             node.xsl     -- one document per CFG node
     nodes/globals.xml          globals.xsl
     files/<src>.xml            file.xsl     -- source listing
     dot/<src>/<fun>.dot                     -- rendered to cfgs/ by `dot`

   Abstract states live in nodes/<id>.xml, never in DOT node labels. That
   separation is the point: a product domain's state makes a CFG node
   unreadably wide when inlined, and unreadable is what --dot-full is.

   Everything here is built from the export_graph the Isabelle side returns,
   so nothing re-derives the CFG or parses a rendered rendering back. *)

module C = Voblint_CLI.Core

type file = { path : string; content : string }

let escape s =
  let buf = Buffer.create (String.length s + 16) in
  String.iter
    (fun ch ->
       Buffer.add_string buf
         (match ch with
          | '&' -> "&amp;"
          | '<' -> "&lt;"
          | '>' -> "&gt;"
          | '"' -> "&quot;"
          | '\'' -> "&apos;"
          | c -> String.make 1 c))
    s;
  Buffer.contents buf

(* goblint's xsltResultOutput.xmlify_file_name: a file name doubles as a
   directory name under dot/ and cfgs/, so its separators are escaped. *)
let xmlify name =
  String.concat "%2F" (String.split_on_char '/' name)

let is_ident_char c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
  || c = '_' || c = '#' || c = '\''

(* A node's content line is either "<var>=<value>", written by state_line, or
   a note the annotation added ("unreachable", "check x == 2 [REFUTED]").
   Only the first shape splits; a note has no '=' before its first
   non-identifier character. *)
let split_binding line =
  match String.index_opt line '=' with
  | None -> None
  | Some i ->
    let name = String.sub line 0 i in
    if name <> "" && String.for_all is_ident_char name then
      Some (name, String.sub line (i + 1) (String.length line - i - 1))
    else None

(* A product domain renders one variable as "sign=Top, ivl=[-inf,+inf],
   parity=Top, congruence==0 (mod 1)". Splitting it into components gives
   node.xsl a nested <map> to fold instead of one very wide line. The split
   only fires before a "<word>=", which leaves interval bounds like
   [-inf,+inf] intact. *)
let split_components value =
  let n = String.length value in
  let starts_binding i =
    let j = ref i in
    while !j < n && is_ident_char value.[!j] do incr j done;
    !j > i && !j < n && value.[!j] = '='
  in
  let parts = ref [] and start = ref 0 and i = ref 0 in
  while !i < n do
    if !i + 1 < n && value.[!i] = ',' && value.[!i + 1] = ' ' && starts_binding (!i + 2)
    then begin
      parts := String.sub value !start (!i - !start) :: !parts;
      i := !i + 2;
      start := !i
    end
    else incr i
  done;
  parts := String.sub value !start (n - !start) :: !parts;
  let parts = List.rev !parts in
  let split p =
    match String.index_opt p '=' with
    | None -> None
    | Some k -> Some (String.sub p 0 k, String.sub p (k + 1) (String.length p - k - 1))
  in
  let split_parts = List.map split parts in
  if List.length parts > 1 && List.for_all (fun x -> x <> None) split_parts then
    Some (List.filter_map Fun.id split_parts)
  else None

let status_note = function
  | C.NS_Proved -> "PROVED"
  | C.NS_Refuted -> "REFUTED"
  | C.NS_Unknown -> "UNKNOWN"
  | C.NS_Unreachable -> "dead"
  | C.NS_Plain | C.NS_Exit -> ""

let is_dead node =
  match C.xn_status node with Some C.NS_Unreachable -> true | _ -> false

(* Which source position a node came from, when it came from one at all.

   A point node's label is "pp<N>", the Statement index compile allocated for
   that command; entry, exit and global nodes have no command behind them and
   so no position. The label is the handle rather than the id because the id
   also carries the procedure and the context, which are what make it unique
   per rendering rather than per source construct. *)
let node_line positions node =
  let l = C.xn_label node in
  let n = String.length l in
  if n > 2 && l.[0] = 'p' && l.[1] = 'p' then
    Option.bind (int_of_string_opt (String.sub l 2 (n - 2)))
      (fun i -> List.assoc_opt i positions)
  else None

(* <map> is alternating <key>/value siblings, <analysis name=> wraps one
   analysis's value, and node.xsl folds a value holding a nested <map>. That
   is goblint's vocabulary, unchanged -- which is why its stylesheets render
   this without adaptation. *)
let state_map node =
  let buf = Buffer.create 512 in
  let bindings, notes =
    List.partition_map
      (fun line ->
         match split_binding line with
         | Some (k, v) -> Left (k, v)
         | None -> Right line)
      (C.xn_lines node)
  in
  Buffer.add_string buf "<map>\n";
  List.iter
    (fun (var, value) ->
       Buffer.add_string buf (Printf.sprintf "<key>%s</key>\n" (escape var));
       match split_components value with
       | Some comps ->
         Buffer.add_string buf "<value><map>";
         List.iter
           (fun (k, v) ->
              Buffer.add_string buf
                (Printf.sprintf "<key>%s</key><value>%s</value>" (escape k) (escape v)))
           comps;
         Buffer.add_string buf "</map></value>\n"
       | None -> Buffer.add_string buf (Printf.sprintf "<value>%s</value>\n" (escape value)))
    bindings;
  Buffer.add_string buf "</map>";
  let notes =
    notes @ (match C.xn_status node with Some s -> [ status_note s ] | None -> [])
  in
  (Buffer.contents buf, List.filter (fun s -> s <> "") notes)

(* One <analysis> element per domain in the same node document. That is what
   the element was for: Goblint runs several analyses at once and each
   contributes its own block here, which is why its frontend already stacks
   them. Voblint runs one domain per invocation, so a multi-domain report is
   several solves feeding one document. *)
let node_xml ~source_file ~fn ~loc ~blocks =
  let _, primary = List.hd blocks in
  let rendered = List.map (fun (name, node) -> (name, state_map node)) blocks in
  let notes =
    List.concat_map
      (fun (name, (_, notes)) ->
         List.map (fun n -> if List.length blocks > 1 then name ^ ": " ^ n else n) notes)
      rendered
  in
  let note_xml =
    if notes = [] then ""
    else
      Printf.sprintf
        "<analysis name=\"status\"><value><set>%s</set></value></analysis>\n"
        (String.concat ""
           (List.map (fun n -> Printf.sprintf "<value>%s</value>" (escape n)) notes))
  in
  let node = primary in
  let analyses =
    String.concat ""
      (List.map
         (fun (name, (body, _)) ->
            Printf.sprintf "<analysis name=\"%s\"><value>\n%s\n</value></analysis>\n"
              (escape name) body)
         rendered)
  in
  (* line/column/endLine/endColumn are display-only in node.xsl. VIMP has no
     multi-line command, so a command's span ends on the line it starts on and
     endLine repeats line; endColumn would need the command's own text length,
     which the parser does not record, so it repeats column. A node with no
     command behind it -- an entry, an exit, a global -- reports zero, which is
     what goblint emits for a location it does not have. *)
  let line, column = match loc with Some (l, c) -> (l, c) | None -> (0, 0) in
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../node.xsl\"?>\n\
     <loc><call id=\"%s\" file=\"%s\" fun=\"%s\" line=\"%d\" order=\"%d\" column=\"%d\" \
     endLine=\"%d\" endColumn=\"%d\" synthetic=\"false\">\n\
     <context><analysis name=\"program point\"><value>%s</value></analysis></context>\n\
     <path>\n\
     %s%s\
     </path>\n\
     </call></loc>\n"
    (escape (C.xn_id node)) (escape source_file) (escape fn) line line column line column
    (escape (C.xn_label node))
    note_xml analyses

let index_xml ~source_file ~fns =
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"report.xsl\"?>\n\
     <report><file name=\"%s\">\n%s\n</file></report>\n"
    (escape source_file)
    (String.concat "\n"
       (List.map (fun f -> Printf.sprintf "<function name=\"%s\"/>" (escape f)) fns))

(* goblint's globals pane shows the solution of its global constraint system.
   VIMP has no separate global unknown to show: since the Base-style migration
   a global lives in the same reachability-lifted local unknown as any local,
   so its value is part of a program point's state rather than beside it.

   The nearest thing carrying the same meaning is each declared global's value
   where the program ends, read off the entry procedure's exit node -- the
   point every terminating execution arrives at. A program whose exit is
   unreachable has no such state, and the pane stays empty rather than
   reporting a value no execution reaches.

   globals.xsl walks globs/glob, taking each glob's <key> as the variable and
   its <analysis name=> children as the per-analysis values -- one row per
   global, not one map per analysis. That is a different shape from the node
   documents' <map>, and a document in the map shape renders as a blank pane
   rather than as an error. *)
let globals_xml ~globals ~blocks =
  let value_of var node =
    List.find_map
      (fun line ->
         match split_binding line with Some (k, v) when k = var -> Some v | _ -> None)
      (C.xn_lines node)
  in
  let row var =
    match
      List.filter_map
        (fun (name, node) -> Option.map (fun v -> (name, v)) (value_of var node))
        blocks
    with
    | [] -> ""
    | per_domain ->
      Printf.sprintf "<glob><key>%s</key>%s</glob>\n" (escape var)
        (String.concat ""
           (List.map
              (fun (name, v) ->
                 (* A product domain's components fold here exactly as they do
                    in a node document: globals.xsl gives a value holding a
                    nested map its own toggle. *)
                 let rendered =
                   match split_components v with
                   | Some comps ->
                     "<map>"
                     ^ String.concat ""
                         (List.map
                            (fun (k, c) ->
                               Printf.sprintf "<key>%s</key><value>%s</value>" (escape k)
                                 (escape c))
                            comps)
                     ^ "</map>"
                   | None -> escape v
                 in
                 Printf.sprintf "<analysis name=\"%s\"><value>%s</value></analysis>"
                   (escape name) rendered)
              per_domain))
  in
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../globals.xsl\"?>\n\
     <globs>\n%s</globs>\n"
    (String.concat "" (List.map row globals))

(* One check's source-level finding. Positions come from the parser, which
   notes each __voblint_check token as it consumes it; the verdict comes from
   the same report the text output prints. *)
type check = { line : int; column : int; verdict : string; cond : string }

(* g2html's file.xsl turns <sht type="X"> into <span class="sh X">, and its
   stylesheet defines exactly these classes. Anything outside them renders
   unstyled, so the tokenizer below maps VIMP onto this palette rather than
   inventing names. *)
let kw_statement = [ "if"; "else"; "while"; "return"; "skip" ]
let kw_declaration = [ "void"; "global" ]
let kw_special = [ "__voblint_check" ]
let kw_literal = [ "true"; "false" ]

let is_ident_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_ident_rest c = is_ident_start c || (c >= '0' && c <= '9') || c = '\''
let is_digit c = c >= '0' && c <= '9'
let is_op c = String.contains ":+-*<=&|!{}();," c

let sht cls text = Printf.sprintf "<sht type=\"%s\">%s</sht>" cls (escape text)

(* Highlights one source line. VIMP has no multi-line construct -- comments run
   to end of line and there are no string literals -- so a line is a complete
   lexical context and needs no carry-over state. *)
let highlight_line line =
  let n = String.length line in
  let buf = Buffer.create (n * 2) in
  let i = ref 0 in
  while !i < n do
    let c = line.[!i] in
    if !i + 1 < n && c = '/' && line.[!i + 1] = '/' then begin
      Buffer.add_string buf (sht "cm" (String.sub line !i (n - !i)));
      i := n
    end
    else if is_ident_start c then begin
      let j = ref !i in
      while !j < n && is_ident_rest line.[!j] do incr j done;
      let word = String.sub line !i (!j - !i) in
      let cls =
        if List.mem word kw_special then Some "sp"
        else if List.mem word kw_statement then Some "sk"
        else if List.mem word kw_declaration then Some "tk"
        else if List.mem word kw_literal then Some "nr"
        else None
      in
      (match cls with
       | Some cls -> Buffer.add_string buf (sht cls word)
       | None -> Buffer.add_string buf (escape word));
      i := !j
    end
    else if is_digit c then begin
      let j = ref !i in
      while !j < n && is_digit line.[!j] do incr j done;
      Buffer.add_string buf (sht "nr" (String.sub line !i (!j - !i)));
      i := !j
    end
    else if is_op c then begin
      let j = ref !i in
      while !j < n && is_op line.[!j] do incr j done;
      Buffer.add_string buf (sht "op" (String.sub line !i (!j - !i)));
      i := !j
    end
    else begin
      Buffer.add_string buf (escape (String.make 1 c));
      incr i
    end
  done;
  Buffer.contents buf

(* Goblint's own phrasing, because this renders in Goblint's own frontend. *)
let warn_text c =
  match c.verdict with
  | "PROVED" -> Printf.sprintf "Assertion \"%s\" will succeed" c.cond
  | "REFUTED" -> Printf.sprintf "Assertion \"%s\" will fail" c.cond
  | _ -> Printf.sprintf "Assertion \"%s\" is unknown" c.cond

let warn_xml ~source_file c =
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../warn.xsl\"?>\n\
     <warning>\n<text file=\"%s\" line=\"%d\" column=\"%d\">%s</text></warning>\n"
    (escape source_file) c.line c.column (escape (warn_text c))

(* file.xsl splices ns/wrn straight into an onclick="select_line(nr,ns,wrn)"
   attribute, so they have to read as JS array literals -- and script.js builds
   ../warn/<entry>.xml and ../nodes/<entry>.xml from those entries, so both are
   quoted strings.

   ns is what makes the source listing a navigation surface rather than a
   pretty-printed file: clicking a line selects the CFG nodes compiled from it.
   A line can hold several, since a node is one program point and a line can
   carry more than one command.

   ded greys a line out. It is set only when the line has nodes and every one
   of them is unreachable -- a line with no node at all (a brace, a comment, a
   blank) is not dead code, it is not code. *)
let file_xml ~source_text ~checks ~line_nodes ~dead_lines =
  (* A file ending in a newline splits into a trailing empty element, which the
     listing would render as one more line than the file has. *)
  let lines =
    match List.rev (String.split_on_char '\n' source_text) with
    | "" :: rest when source_text <> "" -> List.rev rest
    | _ -> String.split_on_char '\n' source_text
  in
  let body =
    List.mapi
      (fun i line ->
         let nr = i + 1 in
         (* warnN.xml is numbered by the check's position in the report, so
            the index is taken before filtering to this line. *)
         let here =
           checks
           |> List.mapi (fun k c -> (k + 1, c))
           |> List.filter (fun (_, c) -> c.line = nr)
         in
         let wrn =
           if here = [] then "[]"
           else
             "["
             ^ String.concat ","
                 (List.map (fun (k, _) -> Printf.sprintf "&quot;warn%d&quot;" k) here)
             ^ "]"
         in
         let ns =
           match List.assoc_opt nr line_nodes with
           | None | Some [] -> "[]"
           | Some ids ->
             "["
             ^ String.concat ","
                 (List.map (fun id -> Printf.sprintf "&quot;%s&quot;" (escape id)) ids)
             ^ "]"
         in
         let ded = if List.mem nr dead_lines then "true" else "false" in
         Printf.sprintf "<ln nr=\"%d\" ns=\"%s\" wrn=\"%s\" ded=\"%s\">%s</ln>" nr ns wrn ded
           (highlight_line line))
      lines
  in
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../file.xsl\"?>\n\
     <file>\n%s\n</file>\n"
    (String.concat "\n" body)

(* Fill colour by finding, not by structural role: this graph exists to be
   read for verdicts. Dead nodes take goblint's own orange (cfgTools'
   fprint_fundec_html_dot paints unreachable nodes that colour). *)
let node_fill node =
  match C.xn_status node with
  | Some C.NS_Proved -> "#cdebc5"
  | Some C.NS_Refuted -> "#f5b8b8"
  | Some C.NS_Unknown -> "#e8e8e8"
  | Some C.NS_Unreachable -> "orange"
  | _ ->
    (match C.xn_kind node with
     | C.XN_Entry | C.XN_ProcEntry | C.XN_Exit | C.XN_ProcExit -> "#eef2f7"
     | _ -> "white")

let node_shape node =
  match C.xn_kind node with
  | C.XN_Entry | C.XN_ProcEntry | C.XN_Exit | C.XN_ProcExit -> "shape=oval"
  | _ -> "shape=box"

let dot_escape s = String.concat "\\\"" (String.split_on_char '"' s)

(* Short labels only, plus the id/URL hooks goblint's script.js drives:
   graphviz turns them into <g id="a_N"><a xlink:href="javascript:show_info('N')">,
   which is the handle it selects on to load and highlight a node. *)
let html_dot graph =
  let by_id = Hashtbl.create 64 in
  List.iter (fun n -> Hashtbl.replace by_id (C.xn_id n) n) (C.xg_nodes graph);
  let buf = Buffer.create 4096 in
  Buffer.add_string buf "digraph AnalysisCFG {\n";
  Buffer.add_string buf
    "  graph [rankdir=TB,newrank=true,splines=polyline,nodesep=0.4,ranksep=0.5,\
     fontname=\"Menlo\"];\n";
  Buffer.add_string buf
    "  node [shape=box,style=filled,fillcolor=white,fontname=\"Menlo\",fontsize=11,\
     id=\"\\N\",URL=\"javascript:show_info('\\N');\"];\n";
  Buffer.add_string buf "  edge [fontname=\"Menlo\",fontsize=9,arrowsize=0.7];\n";
  List.iter
    (fun cluster ->
       Buffer.add_string buf (Printf.sprintf "  subgraph %s {\n" (C.xc_id cluster));
       Buffer.add_string buf
         (Printf.sprintf "    label=\"%s\";\n" (dot_escape (C.xc_label cluster)));
       Buffer.add_string buf "    style=rounded; color=gray70;\n";
       List.iter
         (fun nid ->
            match Hashtbl.find_opt by_id nid with
            | None -> ()
            | Some node ->
              if C.xn_kind node <> C.XN_Source then
                Buffer.add_string buf
                  (Printf.sprintf "    %s [%s,fillcolor=\"%s\",label=\"%s\"];\n" nid
                     (node_shape node) (node_fill node)
                     (dot_escape (C.xn_label node))))
         (C.xc_nodes cluster);
       Buffer.add_string buf "  }\n")
    (C.xg_clusters graph);
  List.iter
    (fun e ->
       let label =
         match C.xe_kind e with
         | C.XE_Enter -> "call " ^ C.xe_label e
         | C.XE_Combine -> "resume"
         | C.XE_CallToReturn -> "resume-site"
         | C.XE_GlobalRead -> "read global"
         | C.XE_GlobalWrite -> "write global"
         | C.XE_Intra -> C.xe_label e
       in
       Buffer.add_string buf
         (Printf.sprintf "  %s -> %s [label=\"%s\"];\n" (C.xe_src e) (C.xe_dst e)
            (dot_escape label)))
    (C.xg_edges graph);
  Buffer.add_string buf "}\n";
  Buffer.contents buf

(* graphs is (domain name, graph), the first being the one the CFG is drawn
   from. Node identifiers are built from the CFG and the context, both of which
   every listed domain shares, so merging the others' states in by identifier is
   sound -- and a node one domain does not cover simply contributes no block. *)
let emit ~graphs ~source_file ~source_text ~fn ~checks ~positions ~globals =
  let seg = xmlify source_file in
  let _, graph = List.hd graphs in
  let index =
    List.map
      (fun (name, g) ->
         let by_id = Hashtbl.create 64 in
         List.iter (fun n -> Hashtbl.replace by_id (C.xn_id n) n) (C.xg_nodes g);
         (name, by_id))
      graphs
  in
  let nodes = List.filter (fun n -> C.xn_kind n <> C.XN_Source) (C.xg_nodes graph) in
  (* The entry procedure's exit, by label rather than by kind: every procedure
     contributes an XN_ProcExit, and only this one is where the program ends. *)
  let exit_label = "exit_" ^ fn in
  let exit_blocks =
    match List.find_opt (fun n -> C.xn_label n = exit_label) (C.xg_nodes graph) with
    | None -> []
    | Some node ->
      List.filter_map
        (fun (name, by_id) ->
           Option.map (fun n -> (name, n)) (Hashtbl.find_opt by_id (C.xn_id node)))
        index
  in
  let node_files =
    List.map
      (fun node ->
         let id = C.xn_id node in
         let blocks =
           List.filter_map
             (fun (name, by_id) ->
                Option.map (fun n -> (name, n)) (Hashtbl.find_opt by_id id))
             index
         in
         { path = Printf.sprintf "nodes/%s.xml" id;
           content = node_xml ~source_file ~fn ~loc:(node_line positions node) ~blocks })
      nodes
  in
  let dead = List.length (List.filter is_dead nodes) in
  (* Grouped once here rather than searched per line: the listing walks every
     line of the file, and most lines have no node at all. *)
  let line_nodes = Hashtbl.create 64 in
  List.iter
    (fun node ->
       match node_line positions node with
       | None -> ()
       | Some (l, _) ->
         Hashtbl.replace line_nodes l (C.xn_id node :: Option.value ~default:[] (Hashtbl.find_opt line_nodes l)))
    nodes;
  let line_nodes = Hashtbl.fold (fun l ids acc -> (l, List.rev ids) :: acc) line_nodes [] in
  let dead_lines =
    List.filter_map
      (fun (l, ids) ->
         if List.for_all (fun id -> List.exists (fun n -> C.xn_id n = id && is_dead n) nodes) ids
         then Some l
         else None)
      line_nodes
  in
  ( { path = "index.xml"; content = index_xml ~source_file ~fns:[ fn ] }
    :: { path = "nodes/globals.xml"; content = globals_xml ~globals ~blocks:exit_blocks }
    :: { path = Printf.sprintf "files/%s.xml" seg; content = file_xml ~source_text ~checks ~line_nodes ~dead_lines }
    :: { path = Printf.sprintf "dot/%s/%s.dot" seg fn; content = html_dot graph }
    :: (node_files
        @ List.mapi
            (fun k c ->
               { path = Printf.sprintf "warn/warn%d.xml" (k + 1);
                 content = warn_xml ~source_file c })
            checks),
    List.length nodes,
    dead )
