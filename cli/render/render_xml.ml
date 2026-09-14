(* The XML documents of a result directory, in the vocabulary goblint's HTML frontend
   (g2html's stylesheets, used unmodified) already reads:

     index.xml          report.xsl   -- entry point
     nodes/<id>.xml     node.xsl     -- one document per graph node
     nodes/globals.xml  globals.xsl
     files/<src>.xml    file.xsl     -- highlighted source listing
     warn/warn<N>.xml                -- one finding

   Each function turns part of one run's Context_graph, its checks and the parsed
   source positions into one document. Which documents a report consists of, and
   where they go, is Report_dir's business. *)

module G = Context_graph

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
let xmlify name = String.concat "%2F" (String.split_on_char '/' name)

let is_ident_char c =
  (c >= 'a' && c <= 'z')
  || (c >= 'A' && c <= 'Z')
  || (c >= '0' && c <= '9')
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
    while !j < n && is_ident_char value.[!j] do
      incr j
    done;
    !j > i && !j < n && value.[!j] = '='
  in
  let parts = ref [] and start = ref 0 and i = ref 0 in
  while !i < n do
    if
      !i + 1 < n
      && value.[!i] = ','
      && value.[!i + 1] = ' '
      && starts_binding (!i + 2)
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
    | Some k ->
        Some (String.sub p 0 k, String.sub p (k + 1) (String.length p - k - 1))
  in
  let split_parts = List.map split parts in
  if List.length parts > 1 && List.for_all (fun x -> x <> None) split_parts then
    Some (List.filter_map Fun.id split_parts)
  else None

let status_note = function
  | G.Proved -> "PROVED"
  | G.Refuted -> "REFUTED"
  | G.Unknown -> "UNKNOWN"
  | G.Unreachable -> "dead"

let is_dead (node : G.node) = node.status = Some G.Unreachable

(* Which source position a node came from, when it came from one at all.

   A point node's label is "pp<N>", the Statement index compile allocated for
   that command; entry, exit and global nodes have no command behind them and
   so no position. The label is the handle rather than the id because the id
   also carries the procedure and the context, which are what make it unique
   per rendering rather than per source construct. *)
let node_line positions (node : G.node) =
  let l = node.label in
  let n = String.length l in
  if n > 2 && l.[0] = 'p' && l.[1] = 'p' then
    Option.bind
      (int_of_string_opt (String.sub l 2 (n - 2)))
      (fun i ->
        Option.map
          (fun (a, b, c, d) -> (a, b, c, d, i))
          (List.assoc_opt i positions))
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
      (G.lines node)
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
                (Printf.sprintf "<key>%s</key><value>%s</value>" (escape k)
                   (escape v)))
            comps;
          Buffer.add_string buf "</map></value>\n"
      | None ->
          Buffer.add_string buf
            (Printf.sprintf "<value>%s</value>\n" (escape value)))
    bindings;
  Buffer.add_string buf "</map>";
  let notes =
    notes
    @ match node.G.status with Some s -> [ status_note s ] | None -> []
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
        List.map
          (fun n -> if List.length blocks > 1 then name ^ ": " ^ n else n)
          notes)
      rendered
  in
  let note_xml =
    if notes = [] then ""
    else
      Printf.sprintf
        "<analysis name=\"status\"><value><set>%s</set></value></analysis>\n"
        (String.concat ""
           (List.map
              (fun n -> Printf.sprintf "<value>%s</value>" (escape n))
              notes))
  in
  let node = primary in
  let analyses =
    String.concat ""
      (List.map
         (fun (name, (body, _)) ->
           Printf.sprintf
             "<analysis name=\"%s\"><value>\n%s\n</value></analysis>\n"
             (escape name) body)
         rendered)
  in
  (* The command's own span, both ends recorded by the parser. order is
     goblint's sequence number within the function, and the Statement index is
     exactly that -- the counter compile allocates in source order. A node with
     no command behind it -- an entry, an exit, a global -- reports zero
     throughout, which is what goblint emits for a location it does not have. *)
  let line, column, end_line, end_column, order =
    match loc with
    | Some (l, c, el, ec, o) -> (l, c, el, ec, o)
    | None -> (0, 0, 0, 0, 0)
  in
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../node.xsl\"?>\n\
     <loc><call id=\"%s\" file=\"%s\" fun=\"%s\" line=\"%d\" order=\"%d\" \
     column=\"%d\" endLine=\"%d\" endColumn=\"%d\" synthetic=\"false\">\n\
     <context><analysis name=\"program \
     point\"><value>%s</value></analysis></context>\n\
     <path>\n\
     %s%s</path>\n\
     </call></loc>\n"
    (escape node.G.id)
    (escape source_file) (escape fn) line order column end_line end_column
    (escape node.G.label)
    note_xml analyses

let index_xml ~source_file ~fns =
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"report.xsl\"?>\n\
     <report><file name=\"%s\">\n\
     %s\n\
     </file></report>\n"
    (escape source_file)
    (String.concat "\n"
       (List.map
          (fun f -> Printf.sprintf "<function name=\"%s\"/>" (escape f))
          fns))

(* goblint's globals pane shows the solution of its global constraint system --
   GHT.iter over every GVar, unfiltered. Ours holds the two kinds a routed D/G
   system side-effects: the shared slot, and one seed per callee entry carrying the
   state a call pushes into that callee. Both come straight from the solve, so this
   renders what the equation system holds rather than a source variable's value --
   which lives in the local state here exactly as it does in goblint's CPA.

   Values arrive already rendered, in the same "var=value" form a node document
   shows, so a product domain's components fold here the way they do there.

   globals.xsl walks globs/glob, taking each glob's <key> as the unknown and its
   <analysis name=> children as the per-analysis values -- one row per unknown, not
   one map per analysis. That is a different shape from the node documents' <map>,
   and a document in the map shape renders as a blank pane rather than as an error. *)
let globals_xml ~blocks =
  let state_xml lines =
    let bindings, notes =
      List.partition_map
        (fun line ->
          match split_binding line with
          | Some (k, v) -> Left (k, v)
          | None -> Right line)
        lines
    in
    if bindings = [] then
      Printf.sprintf "<value>%s</value>"
        (escape
           (if notes = [] then "\xe2\x88\x85" else String.concat ", " notes))
    else
      "<value><map>"
      ^ String.concat ""
          (List.map
             (fun (var, value) ->
               Printf.sprintf "<key>%s</key><value>%s</value>" (escape var)
                 (match split_components value with
                 | Some comps ->
                     "<map>"
                     ^ String.concat ""
                         (List.map
                            (fun (k, c) ->
                              Printf.sprintf "<key>%s</key><value>%s</value>"
                                (escape k) (escape c))
                            comps)
                     ^ "</map>"
                 | None -> escape value))
             bindings)
      ^ "</map></value>"
  in
  let keys = match blocks with [] -> [] | (_, gvs) :: _ -> List.map fst gvs in
  let row key =
    match
      List.filter_map
        (fun (name, gvs) ->
          Option.map (fun l -> (name, l)) (List.assoc_opt key gvs))
        blocks
    with
    | [] -> ""
    | per_domain ->
        Printf.sprintf "<glob><key>%s</key>%s</glob>\n" (escape key)
          (String.concat ""
             (List.map
                (fun (name, lines) ->
                  Printf.sprintf "<analysis name=\"%s\">%s</analysis>"
                    (escape name) (state_xml lines))
                per_domain))
  in
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../globals.xsl\"?>\n\
     <globs>\n\
     %s</globs>\n"
    (String.concat "" (List.map row keys))

(* One check's source-level finding. Positions come from the parser, which
   notes each __voblint_check token as it consumes it; the verdict comes from
   the same report the text output prints. *)
type check = {
  line : int;
  column : int;
  verdict : string;
  cond : string;
  message : string option;
}

(* g2html's file.xsl turns <sht type="X"> into <span class="sh X">, and its
   stylesheet defines exactly these classes. Anything outside them renders
   unstyled, so the tokenizer below maps VIMP onto this palette rather than
   inventing names. *)
let kw_statement = [ "if"; "else"; "while"; "return"; "skip" ]
let kw_declaration = [ "fun"; "global" ]
let kw_special = [ "__voblint_check" ]
let kw_literal = [ "true"; "false" ]

let is_ident_start c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'

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
      while !j < n && is_ident_rest line.[!j] do
        incr j
      done;
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
      while !j < n && is_digit line.[!j] do
        incr j
      done;
      Buffer.add_string buf (sht "nr" (String.sub line !i (!j - !i)));
      i := !j
    end
    else if is_op c then begin
      let j = ref !i in
      while !j < n && is_op line.[!j] do
        incr j
      done;
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
  match (c.message, c.verdict) with
  | Some message, _ -> message
  | None, "PROVED" -> Printf.sprintf "Assertion \"%s\" will succeed" c.cond
  | None, "REFUTED" -> Printf.sprintf "Assertion \"%s\" will fail" c.cond
  | _ -> Printf.sprintf "Assertion \"%s\" is unknown" c.cond

let warn_xml ~source_file c =
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../warn.xsl\"?>\n\
     <warning>\n\
     <text file=\"%s\" line=\"%d\" column=\"%d\">%s</text></warning>\n"
    (escape source_file) c.line c.column
    (escape (warn_text c))

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
                (List.map
                   (fun (k, _) -> Printf.sprintf "&quot;warn%d&quot;" k)
                   here)
            ^ "]"
        in
        let ns =
          match List.assoc_opt nr line_nodes with
          | None | Some [] -> "[]"
          | Some ids ->
              "["
              ^ String.concat ","
                  (List.map
                     (fun id -> Printf.sprintf "&quot;%s&quot;" (escape id))
                     ids)
              ^ "]"
        in
        let ded = if List.mem nr dead_lines then "true" else "false" in
        Printf.sprintf "<ln nr=\"%d\" ns=\"%s\" wrn=\"%s\" ded=\"%s\">%s</ln>"
          nr ns wrn ded (highlight_line line))
      lines
  in
  Printf.sprintf
    "<?xml version=\"1.0\" ?>\n\
     <?xml-stylesheet type=\"text/xsl\" href=\"../file.xsl\"?>\n\
     <file>\n\
     %s\n\
     </file>\n"
    (String.concat "\n" body)

