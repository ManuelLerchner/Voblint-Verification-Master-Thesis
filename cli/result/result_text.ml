(* Reading a run result: the readings every renderer shares.

   Voblint_CLI.Generated hands back data -- CFG nodes, edge actions, verdicts,
   context indices, and values already rendered by their own domain. Naming a
   point, spelling a verdict, labelling a context and wording an edge action are
   decisions made once here, so the text report, the graph, the regression
   snapshot, the HTML report and the browser all read the same result the same
   way. Nothing here can change what the analysis concluded. *)

module C = Voblint_CLI.Generated

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

(* A division or remainder whose divisor the verdict says is, or may be, zero. *)
let division_message verdict operation =
  let kind = match operation with C.Mod _ -> "remainder" | _ -> "division" in
  let text = Vimp_printer.string_of_exp operation in
  match verdict with
  | C.Check_Refuted ->
      kind ^ " by zero whenever this operation is evaluated: " ^ text
  | _ -> "possible " ^ kind ^ " by zero: " ^ text

let diagnostic_message d =
  division_message (C.diagnostic_verdict d)
    (C.arithmetic_operation (C.diagnostic_obligation d))

let context_label = function
  | C.Context_Unit -> "unit"
  | C.Context_Entry [] | C.Context_Call_String [] -> "root context"
  | C.Context_Entry values -> String.concat ", " values
  | C.Context_Call_String points ->
      "call-string=" ^ String.concat " " (List.map point_name points)

(* One row per global unknown: its name, then the bindings of the state it holds. A
   seed is named by its procedure and, when a run has several contexts, by the
   context it was entered at. *)
let global_rows result =
  let contexts = Array.of_list (C.res_contexts result) in
  List.map
    (fun g ->
      let key =
        match C.global_key g with
        | C.Global_Shared -> "Global"
        | C.Global_Seed (f, None) -> "enter " ^ f
        | C.Global_Seed (f, Some i) -> (
            match contexts.(int_of_nat i) with
            | C.Context_Unit -> "enter " ^ f
            | ctx -> "enter " ^ f ^ " @ " ^ context_label ctx)
      in
      let lines =
        match C.global_state g with
        | C.Bot -> [ "unreachable" ]
        | C.Lifted bindings -> List.map (fun (x, v) -> x ^ "=" ^ v) bindings
      in
      (key, lines))
    (C.res_globals result)

let special_text dst = function
  | C.Nondet_Int -> dst ^ " := __voblint_nondet_int()"
  | C.Min (a, b) ->
      Printf.sprintf "%s := min(%s, %s)" dst
        (Vimp_printer.string_of_exp a)
        (Vimp_printer.string_of_exp b)
  | C.Max (a, b) ->
      Printf.sprintf "%s := max(%s, %s)" dst
        (Vimp_printer.string_of_exp a)
        (Vimp_printer.string_of_exp b)

let action_text = function
  | C.EA_Nop -> "nop"
  | C.EA_Assign (x, e) -> x ^ " := " ^ Vimp_printer.string_of_exp e
  | C.EA_Special (sc, x) -> special_text x sc
  | C.EA_Assume b -> "[" ^ Vimp_printer.string_of_exp b ^ "]"
  | C.EA_AssumeNot b -> "![" ^ Vimp_printer.string_of_exp b ^ "]"
  | C.EA_Body p -> "body(" ^ p ^ ")"
  | C.EA_Ret (None, _) -> "return"
  | C.EA_Ret (Some e, _) -> "return " ^ Vimp_printer.string_of_exp e
  | C.EA_Check (_, e) -> "check(" ^ Vimp_printer.string_of_exp e ^ ")"

let action_writes = function
  | C.EA_Assign (x, _) | C.EA_Special (_, x) -> Some x
  | _ -> None

let call_text callee (C.CallEdge (_, _, args)) =
  callee ^ "("
  ^ String.concat ", " (List.map Vimp_printer.string_of_exp args)
  ^ ")"

let intra_edges g = List.map (fun (u, (a, v)) -> (u, a, v)) (C.cfg_intra_list g)

let call_edges g =
  List.map
    (fun (u, (ca, (entry, after))) -> (u, ca, entry, after))
    (C.cfg_calls_list g)

(* The procedure a CFG node belongs to. Intra edges and a call's step to its own
   continuation never leave a procedure, so everything reachable from a procedure's
   entry through them is that procedure's; a result node is named by its procedure
   directly. *)
let owners g =
  let table = Hashtbl.create 64 in
  let successors = Hashtbl.create 64 in
  List.iter (fun (u, _, v) -> Hashtbl.add successors u v) (intra_edges g);
  List.iter
    (fun (u, _, _, after) -> Hashtbl.add successors u after)
    (call_edges g);
  let rec visit owner node =
    if not (Hashtbl.mem table node) then begin
      Hashtbl.replace table node owner;
      List.iter (visit owner) (Hashtbl.find_all successors node)
    end
  in
  List.iter
    (function
      | C.FunctionEntry p as entry -> visit p entry
      | C.FunctionResult p as result -> Hashtbl.replace table result p
      | C.Statement _ -> ())
    (C.cfg_node_list g);
  fun node -> Option.value ~default:"" (Hashtbl.find_opt table node)

(* The variables an expression mentions, once each, in order of first occurrence. *)
let exp_vars e =
  let rec go acc = function
    | C.N _ -> acc
    | C.V x -> if List.mem x acc then acc else acc @ [ x ]
    | C.Not a -> go acc a
    | C.Plus (a, b)
    | C.Minus (a, b)
    | C.Times (a, b)
    | C.Div (a, b)
    | C.Mod (a, b)
    | C.Less (a, b)
    | C.LessEq (a, b)
    | C.Greater (a, b)
    | C.GreaterEq (a, b)
    | C.Eq (a, b)
    | C.NotEq (a, b)
    | C.And (a, b)
    | C.Or (a, b) ->
        go (go acc a) b
  in
  go [] e

(* What the variables a check reads hold at its point, across every live context:
   one value per context-distinct rendering, so a context-free run shows its single
   value and a contextual one shows each context's own. *)
let state_slice result point cnd =
  let live =
    List.filter_map
      (fun st ->
        if C.state_point st <> point then None
        else match C.state_value st with C.Lifted b -> Some b | C.Bot -> None)
      (C.res_states result)
  in
  String.concat ", "
    (List.filter_map
       (fun x ->
         match
           List.sort_uniq compare (List.filter_map (List.assoc_opt x) live)
         with
         | [] -> None
         | values -> Some (x ^ "=" ^ String.concat " | " values))
       (exp_vars cnd))
