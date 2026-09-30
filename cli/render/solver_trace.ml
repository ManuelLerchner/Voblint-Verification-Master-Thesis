(* Rendering a solver trace (--trace).

   Solver_trace_hook recorded the solver's steps as raw values during the solve;
   the generated code installed the readers that turn them back into result
   states and contexts. This module names unknowns, renders values with each
   domain's own printer, and writes the trace as compact text, verbose text, or
   JSON Lines. It reads a finished run only: nothing here changes a result. *)

module C = Voblint_CLI.Generated
module H = Solver_trace_hook
module A = Result_text

type format = Text | Jsonl

(* ---------------------------------------------------------------- naming *)

let node_name = A.point_name
let value_text v = Value_symbols.decode (C.trace_string_of_abstract_value v)

let context_of (o : Obj.t) : C.abstract_value C.analysis_context =
  Obj.obj (!H.context o)

let context_label o =
  match context_of o with
  | C.Context_Unit -> "unit"
  | C.Context_Entry [] | C.Context_Call_String [] -> "root"
  | C.Context_Entry vs ->
      "[" ^ String.concat ", " (List.map value_text vs) ^ "]"
  | C.Context_Call_String ps ->
      "[" ^ String.concat " " (List.map A.point_name ps) ^ "]"

(* A local unknown is a (node, context) pair. A global unknown is the
   analysis's global or the activation seed of a callee entry in a context,
   read through the decoder the generated code installed for the run's
   global-unknown type. *)
let local_parts (o : Obj.t) : C.cfg_node * Obj.t = Obj.obj o

type global = Analysis_global | Seed of C.cfg_node * Obj.t

let global_of (o : Obj.t) =
  match !H.global o with
  | None -> Analysis_global
  | Some (n, c) -> Seed (Obj.obj n, c)

let local_text o =
  let n, c = local_parts o in
  Printf.sprintf "(%s, %s)" (node_name n) (context_label c)

let proc_of = function
  | C.FunctionEntry p | C.FunctionResult p -> p
  | n -> node_name n

let global_text o =
  match global_of o with
  | Analysis_global -> "Global"
  | Seed (n, c) -> Printf.sprintf "Seed(%s, %s)" (proc_of n) (context_label c)

(* ---------------------------------------------------------------- values *)

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

let read reader o = try view_text (Obj.obj (!H.view (reader o))) with _ -> "?"
let local_value = read (fun o -> !H.state_local o)
let entry_value = read (fun o -> !H.local_part o)

let global_value y d =
  match global_of y with
  | Analysis_global -> read (fun o -> !H.state_global o) d
  | Seed _ -> local_value d

(* ------------------------------------------------------------ one record *)

type record = {
  kind : string;  (** machine name *)
  label : string;  (** text label *)
  subject : string;  (** first line, after the label *)
  details : (string * string) list;  (** indented lines / JSON fields *)
  json : (string * string) list;  (** structured JSON fields, already encoded *)
}

let json_string s = Render_json.json_string s

let json_context o =
  match context_of o with
  | C.Context_Unit -> {|{"kind":"unit"}|}
  | C.Context_Entry vs ->
      Printf.sprintf {|{"kind":"entry_state","values":[%s]}|}
        (String.concat "," (List.map (fun v -> json_string (value_text v)) vs))
  | C.Context_Call_String ps ->
      Printf.sprintf {|{"kind":"call_string","sites":[%s]}|}
        (String.concat ","
           (List.map (fun p -> json_string (A.point_name p)) ps))

let json_local o =
  let n, c = local_parts o in
  Printf.sprintf {|{"kind":"local","node":%s,"context":%s}|}
    (json_string (node_name n))
    (json_context c)

let json_global o =
  match global_of o with
  | Analysis_global -> {|{"kind":"analysis_global"}|}
  | Seed (n, c) ->
      Printf.sprintf {|{"kind":"activation_seed","procedure":%s,"context":%s}|}
        (json_string (proc_of n))
        (json_context c)

let seen = Hashtbl.create 64

let record_of (e : H.event) =
  match e with
  | H.Solve x ->
      let again = Hashtbl.mem seen x in
      Hashtbl.replace seen x ();
      {
        kind = (if again then "resolve" else "solve");
        label = (if again then "RESOLVE" else "SOLVE");
        subject = local_text x;
        details = [];
        json = [ ("unknown", json_local x) ];
      }
  | H.Query_local (x, y) ->
      {
        kind = "query_local";
        label = "QUERY-L";
        subject = local_text x ^ " -> " ^ local_text y;
        details = [];
        json = [ ("current", json_local x); ("target", json_local y) ];
      }
  | H.Value_local (x, y, d) ->
      let v = local_value d in
      {
        kind = "value_local";
        label = "VALUE-L";
        subject = local_text y ^ " to " ^ local_text x;
        details = [ ("value", v) ];
        json =
          [
            ("current", json_local x);
            ("target", json_local y);
            ("value", json_string v);
          ];
      }
  | H.Query_global (x, y, d) ->
      let v = global_value y d in
      {
        kind = "query_global";
        label = "QUERY-G";
        subject = local_text x ^ " -> " ^ global_text y;
        details = [ ("value", v) ];
        json =
          [
            ("current", json_local x);
            ("target", json_global y);
            ("value", json_string v);
          ];
      }
  | H.Side (x, y, d) ->
      let v = global_value y d in
      {
        kind = "side";
        label = "SIDE";
        subject = local_text x ^ " -> " ^ global_text y;
        details = [ ("value", v) ];
        json =
          [
            ("current", json_local x);
            ("target", json_global y);
            ("value", json_string v);
          ];
      }
  | H.Update_global (y, o, n) ->
      let o = global_value y o and n = global_value y n in
      {
        kind = "update_global";
        label = "UPDATE-G";
        subject = global_text y ^ " (readers destabilized)";
        details = [ ("old", o); ("new", n) ];
        json =
          [
            ("unknown", json_global y);
            ("old", json_string o);
            ("new", json_string n);
          ];
      }
  | H.Update_local (x, o, n) ->
      let o = local_value o and n = local_value n in
      {
        kind = "update_local";
        label = "UPDATE-L";
        subject = local_text x ^ " (readers destabilized)";
        details = [ ("old", o); ("new", n) ];
        json =
          [
            ("unknown", json_local x);
            ("old", json_string o);
            ("new", json_string n);
          ];
      }
  | H.Answer (x, d) ->
      let v = local_value d in
      {
        kind = "answer";
        label = "ANSWER";
        subject = local_text x;
        details = [ ("value", v) ];
        json = [ ("current", json_local x); ("value", json_string v) ];
      }
  | H.Route (u, d, c) ->
      let v = entry_value d in
      {
        kind = "route";
        label = "ROUTE";
        subject = "call at " ^ local_text u ^ " -> context " ^ context_label c;
        details = [ ("entry", v) ];
        json =
          [
            ("call", json_local u);
            ("entry", json_string v);
            ("context", json_context c);
          ];
      }

(* ---------------------------------------------------------- compact text *)

(* The per-caller story: which context a call is routed to, the query of the
   callee's result, what the callee's entry reads from its seed, the flushed
   publication and whether it changed the seed, restarts, and what the caller
   returns. Local propagation between plain nodes is left out. *)
let compact events =
  let callers = Hashtbl.create 8 in
  let lines = ref [] in
  let add s = lines := s :: !lines in
  let is_result y =
    match fst (local_parts y) with C.FunctionResult _ -> true | _ -> false
  in
  let is_seed y = match global_of y with Seed _ -> true | _ -> false in
  (* The caller whose result query saw a publication change the seed it
     depends on; the solver evaluates it again from its call. *)
  let restart = ref None and asking = ref None in
  let announce_restart () =
    Option.iter (fun x -> add ("RESTART  " ^ local_text x)) !restart;
    restart := None
  in
  let rec go = function
    | [] -> ()
    | e :: rest ->
        (match e with
        | H.Route (u, d, c) ->
            announce_restart ();
            add
              (Printf.sprintf "ROUTE    call at %s: entry %s -> context %s"
                 (local_text u) (entry_value d) (context_label c))
        | H.Query_local (x, y) when is_result y ->
            announce_restart ();
            Hashtbl.replace callers x ();
            asking := Some x;
            add
              (Printf.sprintf "QUERY    %s asks %s" (local_text x)
                 (local_text y))
        | H.Value_local (x, y, d) when is_result y ->
            add
              (Printf.sprintf "         %s returns %s" (local_text y)
                 (local_value d));
            ignore x
        | H.Query_global (x, y, d) when is_seed y ->
            add
              (Printf.sprintf "         %s reads %s = %s" (local_text x)
                 (global_text y) (global_value y d))
        | H.Side (_, y, d) ->
            (* The solver's Side step (TD_side_upd_rule's eval) decides
               update_global before it evaluates the rest of the right-hand
               side, so a change is recorded as the very next event. *)
            let changed =
              match rest with
              | H.Update_global (y', _, _) :: _ when y' = y -> true
              | _ -> false
            in
            if changed then restart := !asking;
            add
              (Printf.sprintf "FLUSH    %s += %s%s" (global_text y)
                 (global_value y d)
                 (if changed then "  (changed: readers restart)"
                  else "  (no change)"))
        | H.Answer (x, d) when Hashtbl.mem callers x ->
            add
              (Printf.sprintf "RETURN   %s = %s" (local_text x) (local_value d))
        | _ -> ());
        go rest
  in
  go events;
  List.rev !lines

(* ------------------------------------------------------------------ emit *)

let checks result =
  List.map
    (fun c ->
      ( node_name (C.check_point c),
        Vimp_printer.string_of_exp (C.check_exp c),
        A.contextual_verdict_name (C.check_verdict c) ))
    (C.res_checks result)

let counts events =
  let locals = Hashtbl.create 64 and globals = Hashtbl.create 16 in
  List.iter
    (function
      | H.Solve x -> Hashtbl.replace locals x ()
      | H.Query_global (_, y, _) | H.Side (_, y, _) ->
          Hashtbl.replace globals y ()
      | _ -> ())
    events;
  (Hashtbl.length locals, Hashtbl.length globals)

let emit ~out ~format ~verbose ~analyses ~context ~globals ~program result =
  let events = H.recorded () in
  Hashtbl.reset seen;
  let locals, globals_n = counts events in
  let pr fmt = Printf.fprintf out fmt in
  match format with
  | Jsonl ->
      pr
        {|{"event":"run","schema":1,"analysis":[%s],"context_policy":%s,"update_rule":%s,"program":%s}|}
        (String.concat "," (List.map json_string analyses))
        (json_string context) (json_string globals) (json_string program);
      pr "\n";
      ignore
        (List.fold_left
           (fun step e ->
             let r = record_of e in
             pr "{\"step\":%d,\"event\":%s%s}\n" step (json_string r.kind)
               (String.concat ""
                  (List.map
                     (fun (k, v) -> "," ^ json_string k ^ ":" ^ v)
                     r.json));
             step + 1)
           1 events);
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
      if verbose then
        ignore
          (List.fold_left
             (fun step e ->
               let r = record_of e in
               pr "[%03d] %-9s %s\n" step r.label r.subject;
               List.iter (fun (k, v) -> pr "      %s = %s\n" k v) r.details;
               step + 1)
             1 events)
      else List.iter (fun l -> pr "%s\n" l) (compact events);
      pr "\n";
      List.iter
        (fun (point, cond, verdict) ->
          pr "CHECK    %s at %s: %s\n" cond point verdict)
        (checks result);
      pr "\nTrace complete: %d local and %d global unknowns solved\n" locals
        globals_n
