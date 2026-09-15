(* The contextual CFG of one run, built from the run result.

   A node is a (point, context) pair the solver covered. Within one context, intra
   edges follow the CFG. A call enters every callee context the result routes it to,
   and the callee's exit resumes the caller at the call's continuation in the
   caller's own context. The route is the result's, never re-derived: which context
   a call enters is a decision of the verified analysis, and this file only draws it.

   Node states show the owning procedure's formals and locals. A declared global is
   shared by every context, so it is not repeated per node; the return slot is the
   compiler's own intermediate, not a program variable, so it is not shown either --
   a combine edge names the call whose result it assigns instead. *)

module C = Voblint_CLI.Generated
module A = Result_text

type node_kind = Program_entry | Program_exit | Proc_entry | Proc_exit | Point

(* A semantic finding at a node. A node with none is drawn by its structure alone. *)
type node_status = Proved | Refuted | Unknown | Unreachable

type node = {
  id : string;
  label : string;
  kind : node_kind;
  status : node_status option;
  bindings : (string * string) list;
  (* Declared globals at this point. The local state carries them like any other
     variable, so they are per point and per context; the drawn graph leaves them
     out only to keep its tooltips short. *)
  globals : (string * string) list;
  (* The return slot, which only an exit state gives a meaningful value. *)
  ret : string option;
  findings : string list;
  point : C.cfg_node;
  owner : string;
  context : int;
  (* The context's number within its owner, as in the node's identifier. *)
  local_context : int;
}

type edge_kind = Intra | Enter | Combine | Call_to_return

(* [writes] names the variable a step assigns, which the browser's value hints and
   state diffs key on; the DOT and snapshot renderings ignore it. *)
type edge = {
  src : string;
  dst : string;
  kind : edge_kind;
  text : string;
  writes : string option;
}

type cluster = {
  cluster_id : string;
  cluster_label : string;
  members : string list;
}

type t = { clusters : cluster list; nodes : node list; edges : edge list }

let ret_var = "#ret"
let main_name = "main"

(* The names a procedure's node state shows, in display order. *)
let scope prog g owner_of =
  let globals = C.declared_global_vars prog in
  let formals_of owner =
    if owner = main_name then []
    else
      match C.prog_table prog owner with
      | Some (C.Proc_decl_ext (formals, _, ())) -> formals
      | None -> []
  in
  let assigned owner =
    List.concat_map
      (fun (u, a, _) ->
        if owner_of u <> owner then []
        else
          match a with
          | C.EA_Assign (x, _) | C.EA_Special (_, x) -> [ x ]
          | _ -> [])
      (A.intra_edges g)
    @ List.concat_map
        (fun (u, C.CallEdge (dst, _, _), _, _) ->
          if owner_of u <> owner then [] else Option.to_list dst)
        (A.call_edges g)
  in
  fun owner ->
    let formals = formals_of owner in
    let locals =
      List.sort_uniq compare
        (List.filter
           (fun x ->
             (not (List.mem x formals))
             && x <> ret_var
             && not (List.mem x globals))
           (assigned owner))
    in
    formals @ locals

let kind_of g = function
  | C.FunctionEntry _ as p when p = C.cfg_entry g -> Program_entry
  | C.FunctionEntry _ -> Proc_entry
  | C.FunctionResult p when p = main_name -> Program_exit
  | C.FunctionResult _ -> Proc_exit
  | C.Statement _ -> Point

let status_of state =
  match C.state_value state with
  | C.Bot -> Some Unreachable
  | C.Lifted _ ->
      (* A safe division is not a finding worth drawing, so only a division that
         is or may be by zero colours a node. *)
      let verdicts =
        List.map snd (C.state_checks state)
        @ List.filter
            (fun v -> v <> C.Lifted C.Check_Proved)
            (List.map snd (C.state_diagnostics state))
      in
      if List.mem (C.Lifted C.Check_Refuted) verdicts then Some Refuted
      else if List.mem (C.Lifted C.Check_Unknown) verdicts then Some Unknown
      else if List.mem (C.Lifted C.Check_Proved) verdicts then Some Proved
      else None

(* A node's variable bindings, one per name the owner's scope shows, in scope order. *)
let bindings_of names state =
  match C.state_value state with
  | C.Bot -> []
  | C.Lifted bindings ->
      List.filter_map
        (fun x -> Option.map (fun v -> (x, v)) (List.assoc_opt x bindings))
        names

(* What the analysis concluded at a node, short enough to label it with. *)
let findings_of state =
  let dead =
    match C.state_value state with
    | C.Bot -> [ "unreachable" ]
    | C.Lifted _ -> []
  in
  dead
  @ List.map
      (fun (cnd, verdict) ->
        let text = "check " ^ Vimp_printer.string_of_exp cnd in
        match verdict with C.Bot -> text ^ " [dead]" | C.Lifted _ -> text)
      (C.state_checks state)
  @ List.filter_map
      (fun (obligation, verdict) ->
        match verdict with
        | C.Lifted ((C.Check_Refuted | C.Check_Unknown) as v) ->
            Some (A.division_message v (C.arithmetic_operation obligation))
        | _ -> None)
      (C.state_diagnostics state)

(* Everything known at a node: its state, then its findings. *)
let lines n = List.map (fun (x, v) -> x ^ "=" ^ v) n.bindings @ n.findings

let build prog (result : (string, unit) C.run_result_ext) : t =
  let g = C.res_cfg result in
  let owner_of = A.owners g in
  let names_of = scope prog g owner_of in
  let globals = C.declared_global_vars prog in
  let contexts = Array.of_list (C.res_contexts result) in
  let states = C.res_states result in
  let covered = Hashtbl.create 64 in
  List.iter
    (fun st ->
      Hashtbl.replace covered
        (C.state_point st, A.int_of_nat (C.state_context st))
        ())
    states;
  let is_covered p c = Hashtbl.mem covered (p, c) in
  (* A context's number within its owner, in the order the result lists states, so
     an identifier does not move when another procedure gains or loses a context. *)
  let local_index = Hashtbl.create 16 in
  let counts = Hashtbl.create 16 in
  List.iter
    (fun st ->
      let owner = owner_of (C.state_point st)
      and c = A.int_of_nat (C.state_context st) in
      if not (Hashtbl.mem local_index (owner, c)) then begin
        let n = Option.value ~default:0 (Hashtbl.find_opt counts owner) in
        Hashtbl.replace local_index (owner, c) n;
        Hashtbl.replace counts owner (n + 1)
      end)
    states;
  let id_of p c =
    let owner = owner_of p in
    Printf.sprintf "%s_%s_ctx%d" owner (A.point_name p)
      (Hashtbl.find local_index (owner, c))
  in
  let targets = Hashtbl.create 16 in
  List.iter
    (fun r ->
      Hashtbl.replace targets
        (C.route_point r, A.int_of_nat (C.route_context r))
        (List.map A.int_of_nat (C.route_targets r)))
    (C.res_routes result);
  (* A live call site that enters no callee context would otherwise show nothing of
     the call it makes; name it on the node. *)
  let unentered_calls p c =
    match
      C.state_value
        (List.find
           (fun st ->
             C.state_point st = p && A.int_of_nat (C.state_context st) = c)
           states)
    with
    | C.Bot -> []
    | C.Lifted _ ->
        List.filter_map
          (fun (u, ca, entry, _) ->
            let callee = match entry with C.FunctionEntry f -> f | _ -> "" in
            if
              u = p
              && Option.value ~default:[] (Hashtbl.find_opt targets (u, c)) = []
            then Some ("call " ^ A.call_text callee ca ^ " [not entered]")
            else None)
          (A.call_edges g)
  in
  let nodes =
    List.map
      (fun st ->
        let p = C.state_point st and c = A.int_of_nat (C.state_context st) in
        {
          id = id_of p c;
          label = A.point_name p;
          kind = kind_of g p;
          status = status_of st;
          bindings = bindings_of (names_of (owner_of p)) st;
          globals = bindings_of globals st;
          ret = List.assoc_opt ret_var (bindings_of [ ret_var ] st);
          findings = findings_of st @ unentered_calls p c;
          point = p;
          owner = owner_of p;
          context = c;
          local_context = Hashtbl.find local_index (owner_of p, c);
        })
      states
  in
  let clusters =
    let order = ref [] in
    let members = Hashtbl.create 16 in
    List.iter
      (fun n ->
        let key = (n.owner, n.context) in
        if not (Hashtbl.mem members key) then order := key :: !order;
        Hashtbl.add members key n.id)
      nodes;
    List.mapi
      (fun i ((owner, c) as key) ->
        {
          cluster_id = Printf.sprintf "cluster_ctx_%d" i;
          cluster_label = owner ^ " / " ^ A.context_label contexts.(c);
          members = List.rev (Hashtbl.find_all members key);
        })
      (List.rev !order)
  in
  let intra =
    List.concat_map
      (fun (u, a, v) ->
        List.filter_map
          (fun st ->
            let c = A.int_of_nat (C.state_context st) in
            if C.state_point st = u && is_covered v c then
              Some
                {
                  src = id_of u c;
                  dst = id_of v c;
                  kind = Intra;
                  text = A.action_text a;
                  writes =
                    (match a with
                    | C.EA_Ret (Some _, _) -> Some ret_var
                    | _ -> A.action_writes a);
                }
            else None)
          states)
      (A.intra_edges g)
  in
  let calls =
    List.concat_map
      (fun (u, ca, entry, after) ->
        List.concat_map
          (fun st ->
            let c = A.int_of_nat (C.state_context st) in
            if C.state_point st <> u then []
            else
              let callee =
                match entry with C.FunctionEntry p -> p | _ -> ""
              in
              let routed =
                Option.value ~default:[] (Hashtbl.find_opt targets (u, c))
              in
              let result_node = C.FunctionResult callee in
              let enters =
                List.concat_map
                  (fun t ->
                    (if is_covered entry t then
                       [
                         {
                           src = id_of u c;
                           dst = id_of entry t;
                           kind = Enter;
                           text = A.call_text callee ca;
                           writes = None;
                         };
                       ]
                     else [])
                    @
                    if is_covered result_node t && is_covered after c then
                      let (C.CallEdge (dst, _, _)) = ca in
                      [
                        {
                          src = id_of result_node t;
                          dst = id_of after c;
                          kind = Combine;
                          text =
                            Option.fold ~none:""
                              ~some:(fun x ->
                                x ^ " := " ^ A.call_text callee ca)
                              dst;
                          writes = None;
                        };
                      ]
                    else [])
                  routed
              in
              enters
              @
              if is_covered after c then
                let (C.CallEdge (dst, _, _)) = ca in
                [
                  {
                    src = id_of u c;
                    dst = id_of after c;
                    kind = Call_to_return;
                    text = callee;
                    writes = dst;
                  };
                ]
              else [])
          states)
      (A.call_edges g)
  in
  { clusters; nodes; edges = intra @ calls }
