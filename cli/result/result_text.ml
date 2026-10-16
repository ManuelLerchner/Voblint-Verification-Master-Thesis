(* Reading a run result: the readings every renderer shares.

   A run result is render_report's projection of the analysis report -- CFG
   nodes, edge actions, verdicts, context indices, and values each domain's
   printer rendered. Naming a
   point, spelling a verdict, labelling a context and wording an edge action are
   decisions made once here, so the text report, the graph, the regression
   snapshot, the HTML report and the browser all read the same result the same
   way. Nothing here can change what the analysis concluded. *)

module C = Voblint

let int_of_nat n = Z.to_int (C.integer_of_nat n)

let point_name = function
  | C.Statement n -> "pp" ^ string_of_int (int_of_nat n)
  | C.FunctionEntry p -> "entry_" ^ p
  | C.FunctionResult p -> "exit_" ^ p

let verdict_name = function
  | C.Check_Proved -> "PROVED"
  | C.Check_Refuted -> "REFUTED"
  | C.Check_Unknown -> "UNKNOWN"

(* Bot is the check no execution reaches in any context the table covers. *)
let contextual_verdict_name = function
  | C.Bot -> "DEAD"
  | C.Lifted v -> verdict_name v

(* A library result's obligation holds the conversion of its first argument and, as
   operand, its second; it prints as the converted call. *)
let obligation_text obligation =
  let operation = C.arithmetic_operation obligation in
  let call name =
    match operation with
    | C.TCast (k, a) ->
        "("
        ^ Vimp_printer.string_of_kind k
        ^ ") " ^ name ^ "("
        ^ Typed_printer.string_of_texp a
        ^ ", "
        ^ Typed_printer.string_of_texp (C.arithmetic_operand obligation)
        ^ ")"
    | _ -> Typed_printer.string_of_texp operation
  in
  match C.arithmetic_hazard obligation with
  | C.Min_Conversion_Overflow -> call "min"
  | C.Max_Conversion_Overflow -> call "max"
  | _ -> Typed_printer.string_of_texp operation

(* What a diagnostic reports, worded after Goblint's messages: a division or
   remainder whose divisor is, or may be, zero; a signed operation whose
   mathematical result lies, or may lie, outside its kind, which for a remainder means
   its quotient, as for INT_MIN % -1; a conversion whose value the target kind does,
   or may, not represent, including a library min or max result written to its
   destination. A REFUTED verdict holds for every execution that
   evaluates the operation; an UNKNOWN one is only possible. *)
let obligation_message verdict obligation =
  let operation = C.arithmetic_operation obligation in
  let text = obligation_text obligation in
  let what =
    match (C.arithmetic_hazard obligation, operation) with
    | C.Division_By_Zero, C.TArith (_, C.AMod, _, _) -> "remainder by zero"
    | C.Division_By_Zero, _ -> "division by zero"
    | (C.Signed_Overflow | C.Remainder_Overflow), C.TArith (_, op, _, _) ->
        "signed integer overflow in "
        ^ (Typed_printer.aop_op op).Vimp_printer.infix
    | (C.Signed_Overflow | C.Remainder_Overflow), _ -> "signed integer overflow"
    | ( ( C.Conversion_Overflow | C.Min_Conversion_Overflow
        | C.Max_Conversion_Overflow ),
        (C.TCast (k, _) | C.TN (k, _)) ) ->
        (if C.ik_signed k then "signed" else "unsigned")
        ^ " integer overflow in conversion"
    | ( ( C.Conversion_Overflow | C.Min_Conversion_Overflow
        | C.Max_Conversion_Overflow ),
        _ ) ->
        "integer overflow in conversion"
  in
  match verdict with
  | C.Check_Refuted -> what ^ " whenever this operation is evaluated: " ^ text
  | _ -> "possible " ^ what ^ ": " ^ text

let diagnostic_message d =
  obligation_message (C.diagnostic_verdict d) (C.diagnostic_obligation d)

(* The name an analysis goes by on the command line and in every report. *)
let analysis_label = Analysis_request.name_of_analysis

(* A local's label is qualified by its procedure; a report shows it by its own name. *)
let display label =
  match String.rindex_opt label ':' with
  | Some i -> String.sub label (i + 1) (String.length label - i - 1)
  | None -> label

(* One active analysis's part of a state, as the run result shows it: a value per
   variable, or one value for a state that relates variables. *)
type section = Store of (string * string) list | Whole of string

let sections_of view =
  List.map
    (fun (a, field) ->
      ( analysis_label a,
        match field with
        | C.Field_Store bindings -> Store bindings
        | C.Field_Whole v -> Whole v ))
    view

(* A section's lines under its analysis's name: one per variable [names] keeps, or
   the whole value. *)
let section_lines ?names (label, section) =
  let keep x = match names with None -> true | Some ns -> List.mem x ns in
  (label ^ ":")
  ::
  (match section with
  | Store bindings ->
      List.filter_map
        (fun (x, v) ->
          if keep x then Some ("  " ^ display x ^ "=" ^ v) else None)
        bindings
  | Whole v -> [ "  " ^ v ])

let context_label = function
  | C.Context_Unit -> "unit"
  | C.Context_Entry [] | C.Context_Call_String [] -> "root context"
  | C.Context_Entry values -> String.concat ", " values
  | C.Context_Call_String points ->
      "call-string=" ^ String.concat " " (List.map point_name points)

(* One row per global unknown: its name, then each active analysis's part of the state
   it holds, or [None] where it holds none. A seed is named by its procedure and, when a
   run has several contexts, by the context it was entered at. *)
let global_sections result =
  let contexts = Array.of_list (C.res_contexts result) in
  List.map
    (fun g ->
      let key =
        match C.global_unknown g with
        | C.Global_Named x -> "global " ^ C.var_label x
        | C.Global_Seed (f, None) -> "enter " ^ f
        | C.Global_Seed (f, Some i) -> (
            match contexts.(int_of_nat i) with
            | C.Context_Unit -> "enter " ^ f
            | ctx -> "enter " ^ f ^ " @ " ^ context_label ctx)
      in
      ( key,
        match C.global_state g with
        | C.Bot -> None
        | C.Lifted view -> Some (sections_of view) ))
    (C.res_globals result)

(* The same rows as text lines. *)
let global_rows result =
  List.map
    (fun (key, sections) ->
      ( key,
        match sections with
        | None -> [ "unreachable" ]
        | Some sections -> List.concat_map section_lines sections ))
    (global_sections result)

let exp_text = Typed_printer.string_of_texp
let var_text x = display (C.var_label x)

let special_text dst = function
  | C.Nondet_Int -> dst ^ " := __voblint_nondet_int()"
  | C.Min (a, b) ->
      Printf.sprintf "%s := min(%s, %s)" dst (exp_text a) (exp_text b)
  | C.Max (a, b) ->
      Printf.sprintf "%s := max(%s, %s)" dst (exp_text a) (exp_text b)

let action_text = function
  | C.EA_Nop -> "nop"
  | C.EA_Assign (x, e) -> var_text x ^ " := " ^ exp_text e
  | C.EA_Special (sc, x) -> special_text (var_text x) sc
  | C.EA_Assume b -> "[" ^ exp_text b ^ "]"
  | C.EA_AssumeNot b -> "![" ^ exp_text b ^ "]"
  | C.EA_Body p -> "body(" ^ p ^ ")"
  | C.EA_Ret (None, _) -> "return"
  | C.EA_Ret (Some e, _) -> "return " ^ exp_text e
  | C.EA_Check (_, e) -> "check(" ^ exp_text e ^ ")"

let action_writes = function
  | C.EA_Assign (x, _) | C.EA_Special (_, x) -> Some (C.var_label x)
  | _ -> None

let call_text callee (C.CallEdge (_, _, args)) =
  callee ^ "(" ^ String.concat ", " (List.map exp_text args) ^ ")"

let intra_edges g =
  List.map (fun (u, (a, v)) -> (u, a, v)) (C.cfg_intra_edges g)

let call_edges g =
  List.map
    (fun (u, (ca, (entry, after))) -> (u, ca, entry, after))
    (C.cfg_call_edges g)

(* The procedure a CFG node belongs to. Intra edges and a call's step to its own
   continuation never leave a procedure, so everything connected to a procedure's
   entry or result through them is that procedure's. Code after a return is not
   reachable from the entry, but every node reaches its procedure's result
   (prog_node_reaches), so walking back from the results names it too. *)
let owners g =
  let table = Hashtbl.create 64 in
  let successors = Hashtbl.create 64 in
  let predecessors = Hashtbl.create 64 in
  let step u v =
    Hashtbl.add successors u v;
    Hashtbl.add predecessors v u
  in
  List.iter (fun (u, _, v) -> step u v) (intra_edges g);
  List.iter (fun (u, _, _, after) -> step u after) (call_edges g);
  let rec visit edges owner node =
    if not (Hashtbl.mem table node) then begin
      Hashtbl.replace table node owner;
      List.iter (visit edges owner) (Hashtbl.find_all edges node)
    end
  in
  let nodes = C.cfg_points g in
  List.iter
    (function
      | C.FunctionEntry p as entry -> visit successors p entry | _ -> ())
    nodes;
  List.iter
    (function
      | C.FunctionResult p as result ->
          Hashtbl.replace table result p;
          List.iter (visit predecessors p)
            (Hashtbl.find_all predecessors result)
      | _ -> ())
    nodes;
  fun node -> Option.value ~default:"" (Hashtbl.find_opt table node)

(* The labels of the variables an expression mentions, once each, in order of first
   occurrence. *)
let exp_vars e = List.map C.var_label (Typed_printer.texp_vars e)

(* What each active analysis holds at a check's point, across every live context: the
   variables the check reads, or a whole value, one per context-distinct rendering, so
   a context-free run shows its single value and a contextual one shows each
   context's own. One entry per analysis, in activation order. *)
let state_slice result point cnd =
  let live =
    List.filter_map
      (fun st ->
        if C.state_point st <> point then None
        else
          match C.state_value st with
          | C.Lifted view -> Some (sections_of view)
          | C.Bot -> None)
      (C.res_states result)
  in
  let labels =
    match live with [] -> [] | sections :: _ -> List.map fst sections
  in
  let joined values = String.concat " | " (List.sort_uniq compare values) in
  List.filter_map
    (fun label ->
      let parts = List.filter_map (List.assoc_opt label) live in
      let text =
        match parts with
        | Whole _ :: _ ->
            joined
              (List.filter_map (function Whole v -> Some v | _ -> None) parts)
        | _ ->
            String.concat ", "
              (List.filter_map
                 (fun x ->
                   match
                     List.filter_map
                       (function
                         | Store b -> List.assoc_opt x b | Whole _ -> None)
                       parts
                   with
                   | [] -> None
                   | values -> Some (display x ^ "=" ^ joined values))
                 (exp_vars cnd))
      in
      if text = "" then None else Some (label ^ ": " ^ text))
    labels
