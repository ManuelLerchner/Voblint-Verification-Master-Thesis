(* Browser adapter for the generated analyzer.

   Parsing, graph and JSON rendering, and browser integration are
   intentionally outside the Isabelle export. The actual analysis call uses
   the same generated [run_voblint] entry point as the native CLI.

   A successful call returns the report rows and, when the selected generated
   view publishes one, the graph from that same [AnalysisResult]. The browser
   never performs a second solve merely to obtain a drawing.

   JavaScript API:

     Voblint_run(
       analysis,
       globals,
       context,
       context_depth,
       int_refinement,
       source,
       trace
     )

   Examples:

     Voblint_run("interval", "warrow", "none", 0, "fixpoint", source, "off")

     Voblint_run(
       "int",
       "join",
       "call-string",
       1,
       "once",
       source,
       "verbose"
     )

   [context_depth] is ignored unless [context = "call-string"].

   [int_refinement] is how the components of int refine each other: "never",
   "once" or "fixpoint". It is ignored unless [analysis] names int.

   [trace] is the solver trace's form, as voblint's own flags name it:
   "compact" (--trace), "verbose" (--trace --verbose) or "jsonl"
   (--trace --format jsonl). Each adds a "trace" field to a successful result
   holding the text Solver_trace writes in that form. With "off" the answer
   carries no such field and the solver records nothing.

   [globals] names how the solver merges side-effected globals: "join",
   "per-origin", "warrow", "warrow-per-origin", or "bounded-narrowing" with an
   optional ":N" narrowing bound (default 5, as the CLI's --narrow-bound).
*)

open Js_of_ocaml
module C = Voblint

(* -------------------------------------------------------------------------- *)
(* Timing                                                                     *)
(* -------------------------------------------------------------------------- *)

let now_ms () : float =
  let value : Js.number_t =
    Js.Unsafe.meth_call (Js.Unsafe.get Js.Unsafe.global "performance") "now" [||]
  in
  Js.to_float value

(* -------------------------------------------------------------------------- *)
(* Configuration                                                              *)
(* -------------------------------------------------------------------------- *)

(* The page names a bounded-narrowing rule with its bound, as
   "bounded-narrowing:N"; without one the rule takes the CLI's default. *)
let split_globals s =
  match String.split_on_char ':' s with
  | [ "bounded-narrowing"; n ] -> (
      match int_of_string_opt n with
      | Some n -> Ok ("bounded-narrowing", Some n)
      | None -> Error ("Unknown globals rule: " ^ s))
  | _ -> Ok (s, None)

(* The depth arrives as a JavaScript number. Only one that fits a Wasm OCaml
   int would arrive as an int; reading it as a number first turns a fraction
   or a huge value into an error message instead of a trap. *)
let depth_of mode (depth : Js.number_t) =
  let depth = Js.to_float depth in
  if mode <> "call-string" then Ok None
  else if Float.is_integer depth && depth >= 0. && depth <= float_of_int max_int
  then Ok (Some (int_of_float depth))
  else Error "Call-string depth must be a non-negative integer"

(* The page always sends a refinement; it is a request for int only when int
   is selected. A comma list is kept exactly as given, and no names at all is
   the empty list: run_voblint alone decides whether it is a valid
   activation. The checks are the CLI's, in [Analysis_request.resolve]. *)
let resolve ~analyses ~refinement ~globals ~context ~depth =
  let names = if analyses = "" then [] else String.split_on_char ',' analyses in
  let ( let* ) = Result.bind in
  let* globals_rule, narrow_bound = split_globals globals in
  let* depth = depth_of context depth in
  let request : Analysis_request.request =
    {
      analyses = Some names;
      refinement = (if List.mem "int" names then Some refinement else None);
      globals = globals_rule;
      narrow_bound;
      context;
      depth;
      program_globals = "local";
    }
  in
  match Analysis_request.resolve request with
  | Ok { domains; rule; mode; placement = _ } ->
      Ok (Option.value domains ~default:[], rule, mode)
  | Error (Analysis_request.Unknown_refinement name) ->
      Error ("Unknown int refinement: " ^ name)
  | Error (Analysis_request.Unknown_analysis name) ->
      Error ("Unknown analysis domain: " ^ name)
  | Error (Analysis_request.Unknown_program_globals name) ->
      Error ("Unknown program globals placement: " ^ name)
  | Error
      ( Analysis_request.Unknown_globals _
      | Analysis_request.Negative_narrow_bound
      | Analysis_request.Narrow_bound_without_rule ) ->
      Error ("Unknown globals rule: " ^ globals)
  | Error
      ( Analysis_request.Unknown_context_name _ | Analysis_request.Context _
      | Analysis_request.Refinement_without_int ) ->
      Error ("Unknown context mode: " ^ context)

(* -------------------------------------------------------------------------- *)
(* Browser entry point                                                        *)
(* -------------------------------------------------------------------------- *)

(* None is tracing off; otherwise the format and whether text is verbose.
   "all" is the verbose text plus JSON Lines of the same recording, for a page
   that shows the one and replays the other without solving again. *)
let trace_of_string = function
  | "off" -> Ok None
  | "compact" -> Ok (Some (Solver_trace.Text, false))
  | "verbose" | "all" -> Ok (Some (Solver_trace.Text, true))
  | "jsonl" -> Ok (Some (Solver_trace.Jsonl, false))
  | mode -> Error ("Unknown trace mode: " ^ mode)

let trace_text ?recorded (format, verbose) ~source ~domains ~globals ~context
    result =
  let buffer = Buffer.create 4096 in
  Solver_trace.emit ~out:(Buffer.add_string buffer) ~format ~verbose ~source
    ?recorded
    ~analyses:(List.map Result_text.analysis_label domains)
    ~context:(Solver_trace.context_name context)
    ~globals ~program:"browser.vimp" result;
  Buffer.contents buffer

(* The verbose trace of a run that may never finish, handed to the page while
   it solves: the page cancels such a run by terminating this worker, and only
   what reached it survives. Chunks go to the worker's [Voblint_trace_chunk],
   about every [live_interval_ms]. The finished run's answer carries the whole
   trace again, so a chunk is only ever a preview. *)
let live_interval_ms = 100.

(* What a run records at most: a run that never finishes stops growing here.
   Lines grow with the states they print, so the text has a limit of its own:
   a page holding much more turns slow to receive, keep and show it. *)
let live_event_limit = 50_000
let live_byte_limit = 8 * 1024 * 1024

(* Calls the worker's [name] with [text], if the worker defines it. *)
let post name text =
  let sink = Js.Unsafe.get Js.Unsafe.global name in
  if Js.typeof sink = Js.string "function" then
    ignore (Js.Unsafe.fun_call sink [| Js.Unsafe.inject (Js.string text) |])

let post_chunk = post "Voblint_trace_chunk"

let stream_live ~source ~domains ~globals ~context =
  let buffer = Buffer.create 4096 in
  let last = ref (now_ms ()) and since = ref 0 and posted = ref 0 in
  let render =
    Solver_trace.live_verbose ~out:(Buffer.add_string buffer) ~source
      ~analyses:(List.map Result_text.analysis_label domains)
      ~context:(Solver_trace.context_name context)
      ~globals ~program:"browser.vimp" ()
  in
  let flush () =
    if Buffer.length buffer > 0 then begin
      posted := !posted + Buffer.length buffer;
      post_chunk (Buffer.contents buffer);
      Buffer.clear buffer
    end;
    last := now_ms ()
  in
  flush ();
  Solver_trace_hook.limit := live_event_limit;
  Solver_trace_hook.listener :=
    fun channel o ->
      render channel o;
      incr since;
      let kept = !Solver_trace_hook.kept in
      if
        kept >= live_event_limit
        || !posted + Buffer.length buffer >= live_byte_limit
      then begin
        (* Keeps nothing more, so the listener is not called again. *)
        Solver_trace_hook.limit := kept;
        Buffer.add_string buffer
          (Printf.sprintf
             "\nTrace stopped after %d events; the run goes on unrecorded.\n"
             kept);
        flush ()
      end
      else if !since >= 256 then begin
        (* Reading the clock on every event would cost more than the event. *)
        since := 0;
        if now_ms () -. !last >= live_interval_ms then flush ()
      end

let stop_live () =
  Solver_trace_hook.limit := max_int;
  Solver_trace_hook.listener := fun _ _ -> ()

let run analysis_js globals_js context_js context_depth refinement_js source_js
    trace_js =
  let analysis_name = Js.to_string analysis_js in

  let refinement_name = Js.to_string refinement_js in

  let globals_name = Js.to_string globals_js in

  let context_name = Js.to_string context_js in

  let source = Js.to_string source_js in

  let trace = trace_of_string (Js.to_string trace_js) in
  let with_jsonl = Js.to_string trace_js = "all" in

  (* Set on every call: the worker keeps this module alive between runs. *)
  Solver_trace_hook.enabled :=
    Result.fold ~ok:Option.is_some ~error:(fun _ -> false) trace;
  Solver_trace_hook.reset ();
  stop_live ();

  let answer =
    match
      ( trace,
        resolve ~analyses:analysis_name ~refinement:refinement_name
          ~globals:globals_name ~context:context_name ~depth:context_depth )
    with
    | Error message, _ | _, Error message -> Render_json.error_json message
    | Ok trace, Ok (domains, globals, context) -> (
        try
          let program, stmt_positions, header_positions =
            Vimp_frontend.program "browser.vimp" source
          in
          (* The call as run_voblint receives it, for a page that cancels the run
                 before an answer exists. *)
          post "Voblint_run_input"
            (Render_json.run_voblint_input_json ~domains ~globals ~ctx:context
               program);
          if trace = Some (Solver_trace.Text, true) then
            stream_live ~source:(source, stmt_positions) ~domains
              ~globals:globals_name ~context;
          let analysis_start = now_ms () in
          let answer =
            Fun.protect ~finally:stop_live (fun () ->
                Analysis_request.analyse ~analyses:domains ~globals ~context
                  ~program_globals:C.Program_Globals_Local program)
          in
          let analysis_ms = now_ms () -. analysis_start in
          let raw =
            Render_json.run_voblint_json ~domains ~globals ~ctx:context program
              answer
          in
          match answer with
          | C.Invalid_Activation ->
              Render_json.error_json ~raw
                "Select at least one analysis, each at most once"
          | C.No_Answer ->
              Render_json.error_json ~raw "The solver returned no answer"
          | C.Malformed_Program ->
              let message =
                match Wf_explain.explain program with
                | Some reason -> "Program is not well-formed: " ^ reason
                | None -> "Program is not well-formed"
              in
              Render_json.error_json ~raw message
          | C.Analysed result ->
              let recorded = Solver_trace_hook.recorded () in
              let render form =
                trace_text ~recorded form ~source:(source, stmt_positions)
                  ~domains ~globals:globals_name ~context result
              in
              let trace = Option.map render trace in
              let trace_jsonl =
                if with_jsonl then Some (render (Solver_trace.Jsonl, false))
                else None
              in
              Render_json.result_json ?trace ?trace_jsonl analysis_ms program
                ~stmt_positions ~header_positions ~raw result
        with Vimp_frontend.Parse_error { line; col; msg; _ } ->
          Render_json.parse_error_json ~line ~column:col msg)
  in
  Js.string answer

(*
 * [callback_with_arity] already creates the JavaScript callback.
 * Install it directly on the worker's global scope rather than passing it
 * through [Js.export], which would wrap the function again.
 *)
let () =
  Js.Unsafe.set Js.Unsafe.global (Js.string "Voblint_run")
    (Js.Unsafe.callback_with_arity 7 run)
