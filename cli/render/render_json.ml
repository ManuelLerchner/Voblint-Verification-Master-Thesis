(* The JSON payload the browser playground reads: status, timing, the check column,
   diagnostics, the drawn graph, and the graph's nodes keyed back to source
   statements, all from one run result. *)

module C = Voblint_CLI.Generated
module A = Result_text
module G = Context_graph

(* -------------------------------------------------------------------------- *)

let json_escape value =
  let buffer = Buffer.create (String.length value + 16) in

  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | c -> Buffer.add_char buffer c)
    value;

  Buffer.contents buffer

let json_string value = "\"" ^ json_escape value ^ "\""

let error_json ?raw message =
  Printf.sprintf "{\"status\":\"error\",\"message\":%s%s}" (json_string message)
    (match raw with Some r -> ",\"raw\":" ^ r | None -> "")

let parse_error_json ~line ~column message =
  Printf.sprintf
    "{\"status\":\"error\",\"message\":%s,\"line\":%d,\"column\":%d}"
    (json_string message) line column

(* Editor annotations key on these; a check or diagnostic the parser gave no
   position omits them rather than guessing one. *)
let location_fields = function
  | Some (line, column) ->
      Printf.sprintf ",\"line\":%d,\"column\":%d" line column
  | None -> ""

let check_json result (check, position) =
  let point = C.check_point check and cnd = C.check_exp check in
  let state =
    match C.check_verdict check with
    | C.Bot -> ""
    | C.Lifted _ -> A.state_slice result point cnd
  in
  Printf.sprintf "{\"point\":%s,\"condition\":%s,\"verdict\":%s,\"state\":%s%s}"
    (json_string (A.point_name point))
    (json_string (Vimp_printer.string_of_exp cnd))
    (json_string (A.contextual_verdict_name (C.check_verdict check)))
    (json_string state) (location_fields position)

let diagnostic_json stmt_positions diagnostic =
  Printf.sprintf "{\"severity\":%s,\"message\":%s%s}"
    (json_string (Render_text.diagnostic_severity diagnostic))
    (json_string (A.diagnostic_message diagnostic))
    (location_fields
       (Render_text.diagnostic_location stmt_positions diagnostic))

(* Unlike the text report, a label shared by two checks drops the positions
   instead of failing: the verdicts are still correct, only their placement is
   not. *)
let positioned_checks checks =
  match Render_text.located_checks checks with
  | located ->
      List.map (fun (check, position) -> (check, Some position)) located
  | exception Failure _ -> List.map (fun check -> (check, None)) checks

let json_list f xs = "[" ^ String.concat "," (List.map f xs) ^ "]"
let json_option f = function Some x -> f x | None -> "null"

(* Every command the parser placed, keyed by the point name nodes carry. A point
   with no node at all is one the solver never reached in any context. *)
let statement_json (index, (line, column, end_line, end_column)) =
  Printf.sprintf
    "{\"point\":%s,\"line\":%d,\"column\":%d,\"end_line\":%d,\"end_column\":%d}"
    (json_string
       (A.point_name (C.Statement (C.nat_of_integer (Z.of_int index)))))
    line column end_line end_column

let binding_json (x, v) = "[" ^ json_string x ^ "," ^ json_string v ^ "]"

let status_name = function
  | G.Proved -> "proved"
  | G.Refuted -> "refuted"
  | G.Unknown -> "unknown"
  | G.Unreachable -> "unreachable"

let kind_name = function
  | G.Program_entry -> "program_entry"
  | G.Program_exit -> "program_exit"
  | G.Proc_entry -> "proc_entry"
  | G.Proc_exit -> "proc_exit"
  | G.Point -> "point"

(* A zero divisor at a node, and the finding line that names it, so a drawing can
   mark the node compactly and still find the full message among its findings. *)
let division_json (verdict, message) =
  Printf.sprintf "{\"verdict\":%s,\"message\":%s}"
    (json_string
       (match verdict with C.Check_Refuted -> "definite" | _ -> "possible"))
    (json_string message)

(* A node's outgoing steps within its own context: the edges whose target state is
   this node's state after one command. [join] marks a target that other live steps
   also flow into -- a loop head or the point after a branch -- whose state is a join
   and so is not the effect of this step alone. A step out of an unreachable node
   contributes nothing and is not counted, nor is a combine edge: that is how a
   call's own continuation receives its result, not a second path. *)
let node_json (graph : G.t) context_of context_key incoming entered exit_of
    step_state divisions (n : G.node) =
  let step (e : G.edge) =
    Printf.sprintf "{\"id\":%s,\"action\":%s,\"writes\":%s,\"join\":%b%s}"
      (json_string e.dst)
      (json_string
         (match e.kind with
         | G.Call_to_return -> "after call " ^ e.text
         | _ -> e.text))
      (json_option json_string e.writes)
      (Option.value ~default:0 (Hashtbl.find_opt incoming e.dst) > 1)
      (match step_state n e with
      | Some C.Bot -> ",\"state\":null"
      | Some (C.Lifted bindings) ->
          ",\"state\":" ^ json_list binding_json bindings
      | None -> "")
  in
  let steps =
    List.filter
      (fun (e : G.edge) ->
        e.src = n.id && (e.kind = G.Intra || e.kind = G.Call_to_return))
      graph.edges
  in
  (* The callee entries a call reaches from this node. [join] marks an entry other
     calls enter too: its state then holds their arguments as well as this call's. *)
  let enter (e : G.edge) =
    Printf.sprintf "{\"id\":%s,\"exit\":%s,\"join\":%b}" (json_string e.dst)
      (json_option json_string (exit_of e.dst))
      (Option.value ~default:0 (Hashtbl.find_opt entered e.dst) > 1)
  in
  let enters =
    List.filter
      (fun (e : G.edge) -> e.src = n.id && e.kind = G.Enter)
      graph.edges
  in
  Printf.sprintf
    "{\"id\":%s,\"point\":%s,\"kind\":%s,\"context\":%s,\"context_key\":%s,\"status\":%s,\"bindings\":%s,\"globals\":%s,\"ret\":%s,\"findings\":%s,\"divisions\":%s,\"next\":%s,\"enters\":%s}"
    (json_string n.id) (json_string n.label)
    (json_string (kind_name n.kind))
    (json_string (context_of n.id))
    (json_string (context_key n))
    (json_option (fun s -> json_string (status_name s)) n.status)
    (json_list binding_json n.bindings)
    (json_list binding_json n.globals)
    (json_option json_string n.ret)
    (json_list json_string n.findings)
    (json_list division_json (divisions n))
    (json_list step steps) (json_list enter enters)

(* A short name for a node's context, to tell contexts apart where their values sit
   side by side. A call string names its call sites by source line, most recent
   first as the string itself orders them; an entry-state context, whose full
   rendering is a whole state, by its number within the procedure. *)
let context_key contexts stmt_positions (n : G.node) =
  let site p =
    match p with
    | C.Statement k -> (
        match List.assoc_opt (A.int_of_nat k) stmt_positions with
        | Some (line, _, _, _) -> "L" ^ string_of_int line
        | None -> A.point_name p)
    | _ -> A.point_name p
  in
  match contexts.(n.context) with
  | C.Context_Unit -> ""
  | C.Context_Call_String [] -> "root"
  | C.Context_Call_String points ->
      String.concat "\u{2190}" (List.map site points)
  | C.Context_Entry _ -> "#" ^ string_of_int n.local_context

(* Where each procedure's parameters are shown: its header span and formals, and
   whether any of its returns carries a value -- without one, the return slot a
   call reads back holds nothing the program put there. *)
let procedure_json program returns_value
    (name, (line, column, end_line, end_column)) =
  let formals =
    match C.prog_table program name with
    | Some (C.Proc_decl_ext (formals, _, ())) when name <> "main" -> formals
    | _ -> []
  in
  Printf.sprintf
    "{\"name\":%s,\"entry\":%s,\"line\":%d,\"column\":%d,\"end_line\":%d,\"end_column\":%d,\"formals\":%s,\"returns_value\":%b}"
    (json_string name)
    (json_string (A.point_name (C.FunctionEntry name)))
    line column end_line end_column
    (json_list json_string formals)
    (returns_value name)

(* What an intra step makes of its source's state, as run_voblint publishes it beside
   that state. A point's steps follow its outgoing intra edges in CFG order, so they
   are paired with those edges and a drawn edge finds its own by action and target;
   the state is null when the step has no successor. A call step has none, since
   its continuation's state is the call's combine rather than one edge's effect. *)
let step_states result =
  let g = C.res_cfg result in
  let table = Hashtbl.create 64 in
  List.iter
    (fun st ->
      let p = C.state_point st in
      let edges = List.filter (fun (u, _, _) -> u = p) (A.intra_edges g) in
      let steps = C.state_steps st in
      if List.length edges = List.length steps then
        Hashtbl.replace table
          (p, A.int_of_nat (C.state_context st))
          (List.map2
             (fun (_, a, _) (w, s) -> (A.action_text a, w, s))
             edges steps))
    (C.res_states result);
  table

let nodes_json result (graph : G.t) context_key =
  let context = Hashtbl.create 64 in
  List.iter
    (fun (c : G.cluster) ->
      List.iter (fun id -> Hashtbl.replace context id c.cluster_label) c.members)
    graph.clusters;
  let dead = Hashtbl.create 64 in
  List.iter
    (fun (n : G.node) ->
      if n.status = Some G.Unreachable then Hashtbl.replace dead n.id ())
    graph.nodes;
  let incoming = Hashtbl.create 64 in
  List.iter
    (fun (e : G.edge) ->
      if
        (e.kind = G.Intra || e.kind = G.Call_to_return)
        && not (Hashtbl.mem dead e.src)
      then
        Hashtbl.replace incoming e.dst
          (1 + Option.value ~default:0 (Hashtbl.find_opt incoming e.dst)))
    graph.edges;
  let entered = Hashtbl.create 16 in
  List.iter
    (fun (e : G.edge) ->
      if e.kind = G.Enter then
        Hashtbl.replace entered e.dst
          (1 + Option.value ~default:0 (Hashtbl.find_opt entered e.dst)))
    graph.edges;
  (* A callee entry's own context exits at that procedure's exit node in the same
     context. *)
  let exits = Hashtbl.create 16 and owners = Hashtbl.create 64 in
  List.iter
    (fun (n : G.node) ->
      Hashtbl.replace owners n.id (n.owner, n.context);
      if n.kind = G.Proc_exit then
        Hashtbl.replace exits (n.owner, n.context) n.id)
    graph.nodes;
  let exit_of entry =
    Option.bind (Hashtbl.find_opt owners entry) (Hashtbl.find_opt exits)
  in
  let points = Hashtbl.create 64 in
  List.iter
    (fun (n : G.node) -> Hashtbl.replace points n.id n.point)
    graph.nodes;
  let steps = step_states result in
  let step_state (n : G.node) (e : G.edge) =
    match (e.kind, Hashtbl.find_opt points e.dst) with
    | G.Intra, Some w ->
        Option.bind
          (Hashtbl.find_opt steps (n.point, n.context))
          (fun entries ->
            List.find_map
              (fun (text, w', s) ->
                if w' = w && text = e.text then Some s else None)
              entries)
    | _ -> None
  in
  let states = Hashtbl.create 64 in
  List.iter
    (fun st ->
      Hashtbl.replace states
        (C.state_point st, A.int_of_nat (C.state_context st))
        st)
    (C.res_states result);
  (* The same divisions, verdicts and messages Context_graph lists as findings. *)
  let divisions (n : G.node) =
    match Hashtbl.find_opt states (n.point, n.context) with
    | None -> []
    | Some st ->
        List.filter_map
          (fun (obligation, verdict) ->
            match verdict with
            | C.Lifted ((C.Check_Refuted | C.Check_Unknown) as v) ->
                Some
                  (v, A.division_message v (C.arithmetic_operation obligation))
            | _ -> None)
          (C.state_diagnostics st)
  in
  let context_of id = Option.value ~default:"" (Hashtbl.find_opt context id) in
  json_list
    (node_json graph context_of context_key incoming entered exit_of step_state
       divisions)
    graph.nodes

(* The drawing's structure: which nodes share a context box, and every edge with its
   role. The browser lays it out and styles it; the DOT rendering stays the CLI's. *)
let edge_kind_name = function
  | G.Intra -> "intra"
  | G.Enter -> "enter"
  | G.Combine -> "combine"
  | G.Call_to_return -> "call_to_return"

let graph_json (graph : G.t) =
  let cluster (c : G.cluster) =
    Printf.sprintf "{\"id\":%s,\"label\":%s,\"members\":%s}"
      (json_string c.cluster_id)
      (json_string c.cluster_label)
      (json_list json_string c.members)
  in
  let edge (e : G.edge) =
    Printf.sprintf "{\"source\":%s,\"target\":%s,\"kind\":%s,\"text\":%s}"
      (json_string e.src) (json_string e.dst)
      (json_string (edge_kind_name e.kind))
      (json_string e.text)
  in
  Printf.sprintf "{\"clusters\":%s,\"edges\":%s}"
    (json_list cluster graph.clusters)
    (json_list edge graph.edges)

(* -------------------------------------------------------------------------- *)
(* The run_voblint call, as data                                              *)
(* -------------------------------------------------------------------------- *)

(* What run_voblint was given and what it answered, serialized without
   interpretation: records become objects keyed by their Isabelle field names,
   a datatype value is its constructor's name when it takes no arguments and
   otherwise an object with that name as its one key, an option is null or its
   value, and a pair is a two-element array. Association lists stay arrays of
   pairs, so their order and any repeated key survive. Abstract values arrive
   as the strings run_voblint's own rendering produced, after Value_symbols
   has replaced their ASCII symbol names with glyphs. The export keeps these
   records abstract, so every field is read through the accessor it publishes. *)

let json_pair f g (a, b) = "[" ^ f a ^ "," ^ g b ^ "]"

let json_object fields =
  "{"
  ^ String.concat "," (List.map (fun (k, v) -> json_string k ^ ":" ^ v) fields)
  ^ "}"

let tagged tag = function
  | [] -> json_string tag
  | [ arg ] -> json_object [ (tag, arg) ]
  | args -> json_object [ (tag, "[" ^ String.concat "," args ^ "]") ]

let nat_json n = string_of_int (A.int_of_nat n)
let check_label_json (line, column) = json_list nat_json [ line; column ]

(* JSON readers parse numbers as doubles, so an integer outside what a double
   holds exactly is written as its digit string rather than silently rounded. *)
let int_json (C.Int_of_integer z) =
  let exact = Z.shift_left Z.one 53 in
  if Z.lt (Z.abs z) exact then Z.to_string z else json_string (Z.to_string z)

let rec exp_json e =
  let bin tag a b = tagged tag [ exp_json a; exp_json b ] in
  match e with
  | C.N i -> tagged "N" [ int_json i ]
  | C.V x -> tagged "V" [ json_string x ]
  | C.Plus (a, b) -> bin "Plus" a b
  | C.Minus (a, b) -> bin "Minus" a b
  | C.Times (a, b) -> bin "Times" a b
  | C.Div (a, b) -> bin "Div" a b
  | C.Mod (a, b) -> bin "Mod" a b
  | C.Less (a, b) -> bin "Less" a b
  | C.LessEq (a, b) -> bin "LessEq" a b
  | C.Greater (a, b) -> bin "Greater" a b
  | C.GreaterEq (a, b) -> bin "GreaterEq" a b
  | C.NotEq (a, b) -> bin "NotEq" a b
  | C.Eq (a, b) -> bin "Eq" a b
  | C.And (a, b) -> bin "And" a b
  | C.Or (a, b) -> bin "Or" a b
  | C.Not a -> tagged "Not" [ exp_json a ]

let rec com_json = function
  | C.SKIP -> tagged "SKIP" []
  | C.Assign (x, e) -> tagged "Assign" [ json_string x; exp_json e ]
  | C.Check (l, e) -> tagged "Check" [ check_label_json l; exp_json e ]
  | C.Seq (c, d) -> tagged "Seq" [ com_json c; com_json d ]
  | C.If (b, c, d) -> tagged "If" [ exp_json b; com_json c; com_json d ]
  | C.While (b, c) -> tagged "While" [ exp_json b; com_json c ]
  | C.Call (dst, f, args) ->
      tagged "Call"
        [ json_option json_string dst; json_string f; json_list exp_json args ]
  | C.Return e -> tagged "Return" [ json_option exp_json e ]
  | C.Restore -> tagged "Restore" []
  | C.Unwind -> tagged "Unwind" []

let cfg_node_json = function
  | C.Statement n -> tagged "Statement" [ nat_json n ]
  | C.FunctionEntry f -> tagged "FunctionEntry" [ json_string f ]
  | C.FunctionResult f -> tagged "FunctionResult" [ json_string f ]

let special_json = function
  | C.Nondet_Int -> tagged "Nondet_Int" []
  | C.Min (a, b) -> tagged "Min" [ exp_json a; exp_json b ]
  | C.Max (a, b) -> tagged "Max" [ exp_json a; exp_json b ]

let edge_action_json = function
  | C.EA_Nop -> tagged "EA_Nop" []
  | C.EA_Assign (x, e) -> tagged "EA_Assign" [ json_string x; exp_json e ]
  | C.EA_Special (sc, x) ->
      tagged "EA_Special" [ special_json sc; json_string x ]
  | C.EA_Assume b -> tagged "EA_Assume" [ exp_json b ]
  | C.EA_AssumeNot b -> tagged "EA_AssumeNot" [ exp_json b ]
  | C.EA_Body f -> tagged "EA_Body" [ json_string f ]
  | C.EA_Ret (e, x) -> tagged "EA_Ret" [ json_option exp_json e; json_string x ]
  | C.EA_Check (l, b) -> tagged "EA_Check" [ check_label_json l; exp_json b ]

let call_action_json (C.CallEdge (dst, formals, args)) =
  tagged "CallEdge"
    [
      json_option json_string dst;
      json_list json_string formals;
      json_list exp_json args;
    ]

let lifted_json f = function
  | C.Bot -> tagged "Bot" []
  | C.Lifted v -> tagged "Lifted" [ f v ]

let check_result_json = function
  | C.Check_Proved -> tagged "Check_Proved" []
  | C.Check_Refuted -> tagged "Check_Refuted" []
  | C.Check_Unknown -> tagged "Check_Unknown" []

let obligation_json o =
  json_object
    [
      ("arithmetic_operation", exp_json (C.arithmetic_operation o));
      ("arithmetic_divisor", exp_json (C.arithmetic_divisor o));
    ]

let cfg_json g =
  json_object
    [
      ("cfg_entry", cfg_node_json (C.cfg_entry g));
      ("cfg_node_list", json_list cfg_node_json (C.cfg_node_list g));
      ( "cfg_intra_list",
        json_list
          (json_pair cfg_node_json (json_pair edge_action_json cfg_node_json))
          (C.cfg_intra_list g) );
      ( "cfg_calls_list",
        json_list
          (json_pair cfg_node_json
             (json_pair call_action_json
                (json_pair cfg_node_json cfg_node_json)))
          (C.cfg_calls_list g) );
    ]

let context_json = function
  | C.Context_Unit -> tagged "Context_Unit" []
  | C.Context_Entry vs -> tagged "Context_Entry" [ json_list json_string vs ]
  | C.Context_Call_String us ->
      tagged "Context_Call_String" [ json_list cfg_node_json us ]

let state_json st =
  json_object
    [
      ("state_point", cfg_node_json (C.state_point st));
      ("state_context", nat_json (C.state_context st));
      ( "state_value",
        lifted_json
          (json_list (json_pair json_string json_string))
          (C.state_value st) );
      ( "state_checks",
        json_list
          (json_pair exp_json (lifted_json check_result_json))
          (C.state_checks st) );
      ( "state_diagnostics",
        json_list
          (json_pair obligation_json (lifted_json check_result_json))
          (C.state_diagnostics st) );
      ( "state_steps",
        json_list
          (json_pair cfg_node_json
             (lifted_json (json_list (json_pair json_string json_string))))
          (C.state_steps st) );
    ]

let route_json r =
  json_object
    [
      ("route_point", cfg_node_json (C.route_point r));
      ("route_context", nat_json (C.route_context r));
      ("route_callee", json_string (C.route_callee r));
      ("route_targets", json_list nat_json (C.route_targets r));
    ]

let result_check_json c =
  json_object
    [
      ("check_point", cfg_node_json (C.check_point c));
      ("check_label", check_label_json (C.check_label c));
      ("check_exp", exp_json (C.check_exp c));
      ("check_verdict", lifted_json check_result_json (C.check_verdict c));
    ]

let result_global_key_json = function
  | C.Global_Shared -> tagged "Global_Shared" []
  | C.Global_Seed (f, i) ->
      tagged "Global_Seed" [ json_string f; json_option nat_json i ]

let result_global_json g =
  json_object
    [
      ("global_key", result_global_key_json (C.global_key g));
      ( "global_state",
        lifted_json
          (json_list (json_pair json_string json_string))
          (C.global_state g) );
    ]

let arithmetic_diagnostic_json d =
  json_object
    [
      ("diagnostic_point", cfg_node_json (C.diagnostic_point d));
      ("diagnostic_occurrence", nat_json (C.diagnostic_occurrence d));
      ("diagnostic_obligation", obligation_json (C.diagnostic_obligation d));
      ("diagnostic_verdict", check_result_json (C.diagnostic_verdict d));
    ]

let run_result_json r =
  json_object
    [
      ("res_cfg", cfg_json (C.res_cfg r));
      ("res_contexts", json_list context_json (C.res_contexts r));
      ("res_states", json_list state_json (C.res_states r));
      ("res_routes", json_list route_json (C.res_routes r));
      ("res_checks", json_list result_check_json (C.res_checks r));
      ("res_globals", json_list result_global_json (C.res_globals r));
      ( "res_diagnostics",
        json_list arithmetic_diagnostic_json (C.res_diagnostics r) );
    ]

let analysis_answer_json = function
  | C.Malformed_Program -> tagged "Malformed_Program" []
  | C.Analysed r -> tagged "Analysed" [ run_result_json r ]

let domain_json d =
  tagged
    (match d with
    | C.Sign_Analysis -> "Sign_Analysis"
    | C.Interval_Analysis -> "Interval_Analysis"
    | C.Int_Analysis -> "Int_Analysis"
    | C.Parity_Analysis -> "Parity_Analysis"
    | C.Congruence_Analysis -> "Congruence_Analysis")
    []

let globals_rule_json r =
  tagged
    (match r with
    | C.Globals_Join -> "Globals_Join"
    | C.Globals_Per_Origin -> "Globals_Per_Origin"
    | C.Globals_Warrow -> "Globals_Warrow"
    | C.Globals_Warrow_Per_Origin -> "Globals_Warrow_Per_Origin")
    []

let context_mode_json = function
  | C.Ctx_None -> tagged "Ctx_None" []
  | C.Ctx_EntryState -> tagged "Ctx_EntryState" []
  | C.Ctx_CallString k -> tagged "Ctx_CallString" [ nat_json k ]

(* A program is read through the export's accessors: main's body, then every other
   procedure's declaration, in the order the program lists them. *)
let program_json p =
  let decl name =
    match C.prog_table p name with
    | Some (C.Proc_decl_ext (formals, body, ())) ->
        json_object
          [
            ("formals", json_list json_string formals); ("body", com_json body);
          ]
    | None -> "null"
  in
  json_object
    [
      ("declared_global_vars", json_list json_string (C.declared_global_vars p));
      ("prog_main", com_json (C.prog_main p));
      ( "prog_table",
        json_list (fun f -> json_pair json_string decl (f, f)) (C.prog_procs p)
      );
    ]

let run_voblint_json ~kind ~globals ~ctx program answer =
  json_object
    [
      ( "input",
        json_object
          [
            ("kind", domain_json kind);
            ("rule", globals_rule_json globals);
            ("ctx", context_mode_json ctx);
            ("p", program_json program);
          ] );
      ("output", analysis_answer_json answer);
    ]

let returns_value result =
  let g = C.res_cfg result in
  let owner_of = A.owners g in
  fun name ->
    List.exists
      (fun (u, a, _) ->
        match a with C.EA_Ret (Some _, _) -> owner_of u = name | _ -> false)
      (A.intra_edges g)

(* One row per procedure entry per context: the seed a call publishes and the callee
   entry reads back, named exactly as every other report names it. The analyses
   run_voblint runs keep every variable in the local state, so the analysis-wide
   slot is never side-effected and is left out.

   A seed holds the whole entered frame, whose other locals the entry has just reset
   to top; only the callee's formals and the program's globals carry information, so
   only those lines are kept. Each row also names the graph node it feeds: its
   procedure's entry in the context it is keyed by, absent when no solved context
   enters that procedure. *)
let seeds_json program result (graph : G.t) =
  let entry_of f i =
    List.find_map
      (fun (n : G.node) ->
        match n.point with
        | C.FunctionEntry g when g = f && n.context = i -> Some n.id
        | _ -> None)
      graph.nodes
  in
  let globals = C.declared_global_vars program in
  let shown f line =
    let formals =
      match C.prog_table program f with
      | Some (C.Proc_decl_ext (formals, _, ())) -> formals
      | None -> []
    in
    match String.index_opt line '=' with
    | Some i ->
        let name = String.sub line 0 i in
        List.mem name formals || List.mem name globals
    | None -> false
  in
  let seed (g, (key, lines)) =
    match C.global_key g with
    | C.Global_Shared -> None
    | C.Global_Seed (f, i) ->
        let entry = Option.bind i (fun i -> entry_of f (A.int_of_nat i)) in
        let reachable =
          match C.global_state g with C.Bot -> false | C.Lifted _ -> true
        in
        let lines = if reachable then List.filter (shown f) lines else lines in
        Some
          (Printf.sprintf
             "{\"key\":%s,\"procedure\":%s,\"entry\":%s,\"reachable\":%b,\"lines\":%s}"
             (json_string key) (json_string f)
             (json_option json_string entry)
             reachable
             (json_list json_string lines))
  in
  "["
  ^ String.concat ","
      (List.filter_map seed
         (List.combine (C.res_globals result) (A.global_rows result)))
  ^ "]"

let result_json analysis_ms program ~stmt_positions ~header_positions ~raw
    result =
  let checks =
    positioned_checks (C.res_checks result)
    |> List.map (check_json result)
    |> String.concat ","
  in
  let diagnostics =
    C.res_diagnostics result
    |> List.map (diagnostic_json stmt_positions)
    |> String.concat ","
  in
  let graph = Context_graph.build program result in
  let contexts = Array.of_list (C.res_contexts result) in
  Printf.sprintf
    "{\"status\":\"ok\",\"timing\":{\"analysis_ms\":%.3f},\"checks\":[%s],\"diagnostics\":[%s],\"statements\":%s,\"procedures\":%s,\"nodes\":%s,\"seeds\":%s,\"raw\":%s,\"graph\":%s}"
    analysis_ms checks diagnostics
    (json_list statement_json stmt_positions)
    (json_list (procedure_json program (returns_value result)) header_positions)
    (nodes_json result graph (context_key contexts stmt_positions))
    (seeds_json program result graph)
    raw (graph_json graph)
