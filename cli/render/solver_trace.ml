(* Rendering a solver trace (--trace).

   The exported solver reports its steps through Solver_trace_hook: solver
   events (Voblint_Solver.Solver_Trace), route events and, before the solve,
   the run's readers (Voblint_CLI.Trace_Run). This module reads them back,
   names unknowns, renders values with each domain's own printer, and writes
   the trace as compact text, Goblint-style verbose text, or JSON Lines. It
   reads a finished run only: nothing here changes a result. *)

module C = Voblint_CLI.Generated
module H = Solver_trace_hook
module A = Result_text

type format = Text | Jsonl

(* ------------------------------------------------------------- read back *)

(* The solver is generic in its unknowns and values, so the hook keeps each
   event as an [Obj.t]. A local unknown is a (node, context) pair in every
   run; the context, the global unknowns and the values have a type the
   context mode and the analyses fix. Those stay [Obj.t] here and reach a
   printer the same run installed, so a value only ever meets a reader of its
   own type. This is the one place that casts. *)
type x = C.cfg_node * Obj.t
type solver_event = (x, Obj.t, Obj.t) C.solver_event
type route_event = (x, Obj.t, Obj.t) C.route_event
type printers = (Obj.t, Obj.t, Obj.t, Obj.t) C.trace_printers
type event = Solver of solver_event | Route of route_event

(* The run's readers, and the events of its one solve: route events outside
   the solve are the result being read back, not solver steps. *)
let read_back raw =
  let printers = ref None in
  let solving = ref false in
  let events =
    List.filter_map
      (fun (channel, o) ->
        match channel with
        | "run" ->
            printers := Some (Obj.obj o : printers);
            None
        | "solver" -> (
            let e : solver_event = Obj.obj o in
            match e with
            | C.Ev_Start _ ->
                solving := true;
                Some (Solver e)
            | C.Ev_Stop ->
                solving := false;
                None
            | _ -> Some (Solver e))
        | "route" when !solving -> Some (Route (Obj.obj o : route_event))
        | _ -> None)
      raw
  in
  (!printers, events)

(* ---------------------------------------------------------------- naming *)

let node_name = A.point_name
let value_text v = Value_symbols.decode (C.string_of_abstract_value v)

let context_label (ctx : C.abstract_value C.analysis_context) =
  match ctx with
  | C.Context_Unit -> "unit"
  | C.Context_Entry [] | C.Context_Call_String [] -> "root"
  | C.Context_Entry vs ->
      "[" ^ String.concat ", " (List.map value_text vs) ^ "]"
  | C.Context_Call_String ps ->
      "[" ^ String.concat " " (List.map A.point_name ps) ^ "]"

type view = (C.analysis_domain * C.abstract_value C.field_state) list C.lifted

let view_text (v : view) =
  match v with
  | C.Bot -> "⊥"
  | C.Lifted sections ->
      String.concat "; "
        (List.map
           (fun (a, field) ->
             A.analysis_label a ^ ": "
             ^
             match field with
             | C.Field_Store [] -> "{}"
             | C.Field_Store bs ->
                 String.concat ", "
                   (List.map (fun (x, v) -> x ^ "=" ^ value_text v) bs)
             | C.Field_Whole v -> value_text v)
           sections)

let proc_of = function
  | C.FunctionEntry p | C.FunctionResult p -> p
  | n -> node_name n

type global = Analysis_global | Seed of C.cfg_node * Obj.t

(* Everything that reads a run's unknowns and values, from its printers. *)
type names = {
  context : Obj.t -> C.abstract_value C.analysis_context;
  global : Obj.t -> global;
  local_value : Obj.t -> string;
  global_value : Obj.t -> Obj.t -> string;
  entry_value : Obj.t -> string;
}

let names_of (C.Trace_Printers (ctx, seed_of, local, shared, entry) : printers)
    =
  let read f o = try view_text (f o) with _ -> "?" in
  let global g =
    match seed_of g with None -> Analysis_global | Some (n, c) -> Seed (n, c)
  in
  {
    context = ctx;
    global;
    local_value = read local;
    global_value =
      (fun g d ->
        match global g with
        | Analysis_global -> read shared d
        | Seed _ -> read local d);
    entry_value = read entry;
  }

let local_text nm ((n, c) : x) =
  Printf.sprintf "(%s, %s)" (node_name n) (context_label (nm.context c))

let global_text nm g =
  match nm.global g with
  | Analysis_global -> "Global"
  | Seed (n, c) ->
      Printf.sprintf "Seed(%s, %s)" (proc_of n) (context_label (nm.context c))

let unknown_text nm = function
  | C.Inl x -> local_text nm x
  | C.Inr g -> global_text nm g

(* ------------------------------------------- the per-caller event stream *)

(* The steps the compact form and JSON Lines report, as they are read off the
   solver events. Both forms keep the vocabulary they had before the solver
   reported further steps. *)
type step =
  | Solve of x  (** a local unknown whose right-hand side is evaluated *)
  | Query_local of x * x  (** current unknown, queried local unknown *)
  | Value_local of x * x * Obj.t
      (** current, queried, the value the query returned *)
  | Query_global of x * Obj.t * Obj.t  (** current, global unknown, value *)
  | Side of x * Obj.t * Obj.t  (** current, global unknown, published value *)
  | Update_global of Obj.t * Obj.t * Obj.t  (** global unknown, old, new *)
  | Update_local of x * Obj.t * Obj.t  (** local unknown, old, new *)
  | Answer of x * Obj.t  (** current unknown, value of its right-hand side *)
  | Route_step of x * Obj.t * Obj.t
      (** calling local unknown, entry value, routed context *)

let step_of = function
  | Route (C.Ev_Route (u, d, c)) -> Some (Route_step (u, d, c))
  | Solver e -> (
      match e with
      | C.Ev_Iterate (x, _, false, _) -> Some (Solve x)
      | C.Ev_Query (y, x, _, _) -> Some (Query_local (y, x))
      | C.Ev_Answer (y, x, d) -> Some (Value_local (y, x, d))
      | C.Ev_Answer_Global (x, g, d) -> Some (Query_global (x, g, d))
      | C.Ev_Side (x, g, d) -> Some (Side (x, g, d))
      | C.Ev_Update_Global (_, g, _, o, n) -> Some (Update_global (g, o, n))
      | C.Ev_Update (x, _, _, o, n) -> Some (Update_local (x, o, n))
      | C.Ev_Rhs (x, d) -> Some (Answer (x, d))
      | _ -> None)

(* ------------------------------------------------------------ one record *)

type record = {
  kind : string;  (** machine name *)
  json : (string * string) list;  (** structured JSON fields, already encoded *)
}

let json_string s = Render_json.json_string s

let json_context nm c =
  match nm.context c with
  | C.Context_Unit -> {|{"kind":"unit"}|}
  | C.Context_Entry vs ->
      Printf.sprintf {|{"kind":"entry_state","values":[%s]}|}
        (String.concat "," (List.map (fun v -> json_string (value_text v)) vs))
  | C.Context_Call_String ps ->
      Printf.sprintf {|{"kind":"call_string","sites":[%s]}|}
        (String.concat ","
           (List.map (fun p -> json_string (A.point_name p)) ps))

let json_local nm ((n, c) : x) =
  Printf.sprintf {|{"kind":"local","node":%s,"context":%s}|}
    (json_string (node_name n))
    (json_context nm c)

let json_global nm g =
  match nm.global g with
  | Analysis_global -> {|{"kind":"analysis_global"}|}
  | Seed (n, c) ->
      Printf.sprintf {|{"kind":"activation_seed","procedure":%s,"context":%s}|}
        (json_string (proc_of n))
        (json_context nm c)

let record_of nm seen = function
  | Solve x ->
      let again = Hashtbl.mem seen x in
      Hashtbl.replace seen x ();
      {
        kind = (if again then "resolve" else "solve");
        json = [ ("unknown", json_local nm x) ];
      }
  | Query_local (x, y) ->
      {
        kind = "query_local";
        json = [ ("current", json_local nm x); ("target", json_local nm y) ];
      }
  | Value_local (x, y, d) ->
      {
        kind = "value_local";
        json =
          [
            ("current", json_local nm x);
            ("target", json_local nm y);
            ("value", json_string (nm.local_value d));
          ];
      }
  | Query_global (x, y, d) ->
      {
        kind = "query_global";
        json =
          [
            ("current", json_local nm x);
            ("target", json_global nm y);
            ("value", json_string (nm.global_value y d));
          ];
      }
  | Side (x, y, d) ->
      {
        kind = "side";
        json =
          [
            ("current", json_local nm x);
            ("target", json_global nm y);
            ("value", json_string (nm.global_value y d));
          ];
      }
  | Update_global (y, o, n) ->
      {
        kind = "update_global";
        json =
          [
            ("unknown", json_global nm y);
            ("old", json_string (nm.global_value y o));
            ("new", json_string (nm.global_value y n));
          ];
      }
  | Update_local (x, o, n) ->
      {
        kind = "update_local";
        json =
          [
            ("unknown", json_local nm x);
            ("old", json_string (nm.local_value o));
            ("new", json_string (nm.local_value n));
          ];
      }
  | Answer (x, d) ->
      {
        kind = "answer";
        json =
          [
            ("current", json_local nm x);
            ("value", json_string (nm.local_value d));
          ];
      }
  | Route_step (u, d, c) ->
      {
        kind = "route";
        json =
          [
            ("call", json_local nm u);
            ("entry", json_string (nm.entry_value d));
            ("context", json_context nm c);
          ];
      }

(* ---------------------------------------------------------- compact text *)

(* The per-caller story: which context a call is routed to, the query of the
   callee's result, what the callee's entry reads from its seed, the flushed
   publication and whether it changed the seed, restarts, and what the caller
   returns. Local propagation between plain nodes is left out. *)
let compact nm steps =
  let callers = Hashtbl.create 8 in
  let lines = ref [] in
  let add s = lines := s :: !lines in
  let is_result ((n, _) : x) =
    match n with C.FunctionResult _ -> true | _ -> false
  in
  let is_seed y = match nm.global y with Seed _ -> true | _ -> false in
  (* The caller whose result query saw a publication change the seed it
     depends on; the solver evaluates it again from its call. *)
  let restart = ref None and asking = ref None in
  let announce_restart () =
    Option.iter (fun x -> add ("RESTART  " ^ local_text nm x)) !restart;
    restart := None
  in
  let rec go = function
    | [] -> ()
    | e :: rest ->
        (match e with
        | Route_step (u, d, c) ->
            announce_restart ();
            add
              (Printf.sprintf "ROUTE    call at %s: entry %s -> context %s"
                 (local_text nm u) (nm.entry_value d)
                 (context_label (nm.context c)))
        | Query_local (x, y) when is_result y ->
            announce_restart ();
            Hashtbl.replace callers x ();
            asking := Some x;
            add
              (Printf.sprintf "QUERY    %s asks %s" (local_text nm x)
                 (local_text nm y))
        | Value_local (_, y, d) when is_result y ->
            add
              (Printf.sprintf "         %s returns %s" (local_text nm y)
                 (nm.local_value d))
        | Query_global (x, y, d) when is_seed y ->
            add
              (Printf.sprintf "         %s reads %s = %s" (local_text nm x)
                 (global_text nm y) (nm.global_value y d))
        | Side (_, y, d) ->
            (* The solver's Side step decides update_global before it
               evaluates the rest of the right-hand side, so a change is the
               very next step. *)
            let changed =
              match rest with
              | Update_global (y', _, _) :: _ when y' = y -> true
              | _ -> false
            in
            if changed then restart := !asking;
            add
              (Printf.sprintf "FLUSH    %s += %s%s" (global_text nm y)
                 (nm.global_value y d)
                 (if changed then "  (changed: readers restart)"
                  else "  (no change)"))
        | Answer (x, d) when Hashtbl.mem callers x ->
            add
              (Printf.sprintf "RETURN   %s = %s" (local_text nm x)
                 (nm.local_value d))
        | _ -> ());
        go rest
  in
  go steps;
  List.rev !lines

(* ---------------------------------------------------------- verbose text *)

(* One line per solver event, in the form Goblint's tracing library writes:
   the indentation, "%%% ", the subsystem, ": ", the message. Subsystems and
   messages are those of Goblint's td_simplified.ml where the step is the same
   (td3.ml's "sol" for the value report); "rhs" and "route" are Voblint's own.
   Goblint indents only between tracei and traceu; a query here is traced as
   if its entry were a tracei and its answer a traceu, so the indentation is
   the solver's query depth. As in Goblint, a subsystem that is not selected
   prints nothing and changes no indentation. *)

type indent = Keep | In | Out

let goblint_line nm = function
  | Route (C.Ev_Route (u, d, c)) ->
      Some
        ( "route",
          Printf.sprintf "call at %s: entry %s -> context %s" (local_text nm u)
            (nm.entry_value d)
            (context_label (nm.context c)),
          Keep )
  | Solver e -> (
      let x = local_text nm in
      match e with
      | C.Ev_Start r -> Some ("multivar", "solving for " ^ x r, Keep)
      | C.Ev_Stop -> None
      | C.Ev_Query (_, q, stable, called) ->
          Some
            ( "solver_query",
              Printf.sprintf "entering query for %s; stable %b; called %b" (x q)
                stable called,
              In )
      | C.Ev_Query_Wpoint (q, already) ->
          if already then None
          else Some ("wpoint", "query adding wpoint " ^ x q, Keep)
      | C.Ev_Iterate_From_Query _ ->
          Some ("iter", "iterate called from query", Keep)
      | C.Ev_Add_Infl (y, r) ->
          Some
            ( "infl",
              Printf.sprintf "add_infl %s %s" (unknown_text nm y) (x r),
              Keep )
      | C.Ev_Answer (_, q, d) ->
          Some
            ( "answer",
              Printf.sprintf "exiting query for %s\nanswer: %s" (x q)
                (nm.local_value d),
              Out )
      | C.Ev_Query_Global (_, g) ->
          Some ("solver_query", "entering query for " ^ global_text nm g, In)
      | C.Ev_Answer_Global (_, g, d) ->
          Some
            ( "answer",
              Printf.sprintf "exiting query for %s\nanswer: %s"
                (global_text nm g) (nm.global_value g d),
              Out )
      | C.Ev_Iterate (i, called, stable, wpoint) ->
          Some
            ( "iter",
              Printf.sprintf
                "begin iterate %s, called: %b, stable: %b, wpoint: %b" (x i)
                called stable wpoint,
              Keep )
      | C.Ev_Eq i -> Some ("eq", "eq " ^ x i, Keep)
      | C.Ev_Rhs (i, d) ->
          Some ("rhs", Printf.sprintf "%s = %s" (x i) (nm.local_value d), Keep)
      | C.Ev_Still_Unstable i ->
          Some ("iter", "iterate still unstable " ^ x i, Keep)
      | C.Ev_Widen (i, wp) ->
          if wp then Some ("wpoint", "widen " ^ x i, Keep) else None
      | C.Ev_Sol (i, wp, old, eqd, now) ->
          Some
            ( "sol",
              Printf.sprintf
                "Var: %s (wp: %b)\nOld value: %s\nEqd: %s\nNew value: %s" (x i)
                wp (nm.local_value old) (nm.local_value eqd)
                (nm.local_value now),
              Keep )
      | C.Ev_Wpoint_Remove (i, wp) ->
          if wp then Some ("wpoint", "iterate removing wpoint " ^ x i, Keep)
          else None
      | C.Ev_Update (i, wpx, old_bot, old, now) ->
          if old_bot then None
          else
            Some
              ( "update",
                Printf.sprintf "%s (wpx: %b): %s -> %s" (x i) wpx
                  (nm.local_value old) (nm.local_value now),
                Keep )
      | C.Ev_Iterate_Changed i -> Some ("iter", "iterate changed " ^ x i, Keep)
      | C.Ev_Side (i, g, d) ->
          Some
            ( "side",
              Printf.sprintf "side to %s from %s; value: %s" (global_text nm g)
                (x i) (nm.global_value g d),
              Keep )
      | C.Ev_Update_Global (i, g, old_bot, _, now) ->
          if old_bot then None
          else
            Some
              ( "update",
                Printf.sprintf "side to %s from %s new: %s" (global_text nm g)
                  (x i) (nm.global_value g now),
                Keep )
      | C.Ev_Destabilize y ->
          Some ("destab", "destabilize " ^ unknown_text nm y, Keep)
      | C.Ev_Stable_Remove i -> Some ("destab", "stable remove " ^ x i, Keep))

(* Every subsystem the verbose form can print, for --trace-sys. *)
let subsystems =
  [
    "multivar";
    "solver_query";
    "wpoint";
    "iter";
    "infl";
    "answer";
    "eq";
    "sol";
    "update";
    "side";
    "destab";
    "rhs";
    "route";
  ]

let verbose ~pr ~selected nm events =
  let level = ref 0 in
  List.iter
    (fun e ->
      match goblint_line nm e with
      | Some (sys, msg, indent) when selected sys -> (
          pr "%s%%%%%% %s: %s\n" (String.make !level ' ') sys msg;
          match indent with
          | In -> level := !level + 2
          | Out -> level := max 0 (!level - 2)
          | Keep -> ())
      | _ -> ())
    events

(* ------------------------------------------------------------------ emit *)

let checks result =
  List.map
    (fun c ->
      ( node_name (C.check_point c),
        Vimp_printer.string_of_exp (C.check_exp c),
        A.contextual_verdict_name (C.check_verdict c) ))
    (C.res_checks result)

let counts steps =
  let locals = Hashtbl.create 64 and globals = Hashtbl.create 16 in
  List.iter
    (function
      | Solve x -> Hashtbl.replace locals x ()
      | Query_global (_, y, _) | Side (_, y, _) -> Hashtbl.replace globals y ()
      | _ -> ())
    steps;
  (Hashtbl.length locals, Hashtbl.length globals)

(* The name the header gives a context mode, as voblint's --context spells it. *)
let context_name = function
  | C.Ctx_None -> "none"
  | C.Ctx_EntryState -> "entry-state"
  | C.Ctx_CallString k -> "call-string:" ^ string_of_int (A.int_of_nat k)

(* [out] receives the trace piece by piece: a channel for the CLI, a buffer
   for the browser, which returns the text with the result. [systems] limits
   the verbose form to those subsystems; empty selects all. *)
let emit ~out ~format ~verbose:is_verbose ?(systems = []) ~analyses ~context
    ~globals ~program result =
  let printers, events = read_back (H.recorded ()) in
  let pr fmt = Printf.ksprintf out fmt in
  match printers with
  | None -> pr "Voblint trace: the run recorded no solve\n"
  | Some printers -> (
      let nm = names_of printers in
      let steps = List.filter_map step_of events in
      let locals, globals_n = counts steps in
      match format with
      | Jsonl ->
          pr
            {|{"event":"run","schema":1,"analysis":[%s],"context_policy":%s,"update_rule":%s,"program":%s}|}
            (String.concat "," (List.map json_string analyses))
            (json_string context) (json_string globals) (json_string program);
          pr "\n";
          let seen = Hashtbl.create 64 in
          ignore
            (List.fold_left
               (fun step e ->
                 let r = record_of nm seen e in
                 pr "{\"step\":%d,\"event\":%s%s}\n" step (json_string r.kind)
                   (String.concat ""
                      (List.map
                         (fun (k, v) -> "," ^ json_string k ^ ":" ^ v)
                         r.json));
                 step + 1)
               1 steps);
          List.iter
            (fun (point, cond, verdict) ->
              pr {|{"event":"check","point":%s,"condition":%s,"verdict":%s}|}
                (json_string point) (json_string cond) (json_string verdict);
              pr "\n")
            (checks result);
          pr {|{"event":"end","local_unknowns":%d,"global_unknowns":%d}|} locals
            globals_n;
          pr "\n"
      | Text ->
          pr "Voblint trace\n";
          pr "  analysis: %s\n" (String.concat "," analyses);
          pr "  context:  %s\n" context;
          pr "  globals:  %s\n" globals;
          pr "  program:  %s\n\n" program;
          if is_verbose then
            verbose ~pr
              ~selected:(fun s -> systems = [] || List.mem s systems)
              nm events
          else List.iter (fun l -> pr "%s\n" l) (compact nm steps);
          pr "\n";
          List.iter
            (fun (point, cond, verdict) ->
              pr "CHECK    %s at %s: %s\n" cond point verdict)
            (checks result);
          pr "\nTrace complete: %d local and %d global unknowns solved\n" locals
            globals_n)
