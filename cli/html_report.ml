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
let node_xml ~source_file ~fn ~blocks =
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
  (* line/column/endLine/endColumn are display-only in node.xsl. VIMP carries
     no source spans yet, so they stay at zero and the source view stays
     unlinked. *)
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../node.xsl\"?>\n\
     <loc><call id=\"%s\" file=\"%s\" fun=\"%s\" line=\"0\" order=\"0\" column=\"0\" \
     endLine=\"0\" endColumn=\"0\" synthetic=\"false\">\n\
     <context><analysis name=\"program point\"><value>%s</value></analysis></context>\n\
     <path>\n\
     %s%s\
     </path>\n\
     </call></loc>\n"
    (escape (C.xn_id node)) (escape source_file) (escape fn) (escape (C.xn_label node))
    note_xml analyses

let index_xml ~source_file ~fns =
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"report.xsl\"?>\n\
     <report><file name=\"%s\">\n%s\n</file></report>\n"
    (escape source_file)
    (String.concat "\n"
       (List.map (fun f -> Printf.sprintf "<function name=\"%s\"/>" (escape f)) fns))

let globals_xml =
  "<?xml version=\"1.0\" ?>\n\
   <?xml-stylesheet type=\"text/xsl\" href=\"../globals.xsl\"?>\n\
   <globs><analysis name=\"globals\"><value><map></map></value></analysis></globs>\n"

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
   ../warn/<entry>.xml from each wrn entry, so those entries are quoted strings.
   ns stays empty until VIMP carries per-node source spans: with no positions
   there is nothing to map a line back to a CFG node with. *)
let file_xml ~source_text ~checks =
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
         Printf.sprintf "<ln nr=\"%d\" ns=\"[]\" wrn=\"%s\" ded=\"false\">%s</ln>" nr wrn
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
let emit ~graphs ~source_file ~source_text ~fn ~checks =
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
           content = node_xml ~source_file ~fn ~blocks })
      nodes
  in
  let dead = List.length (List.filter is_dead nodes) in
  ( { path = "index.xml"; content = index_xml ~source_file ~fns:[ fn ] }
    :: { path = "nodes/globals.xml"; content = globals_xml }
    :: { path = Printf.sprintf "files/%s.xml" seg; content = file_xml ~source_text ~checks }
    :: { path = Printf.sprintf "dot/%s/%s.dot" seg fn; content = html_dot graph }
    :: (node_files
        @ List.mapi
            (fun k c ->
               { path = Printf.sprintf "warn/warn%d.xml" (k + 1);
                 content = warn_xml ~source_file c })
            checks),
    List.length nodes,
    dead )
