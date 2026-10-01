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
module C = Voblint_CLI.Generated

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

(* Each refinement mode is an analysis of its own in the generated carrier. *)
let int_analysis_of_string = function
  | "never" -> Some C.Int_Never_Analysis
  | "once" -> Some C.Int_Once_Analysis
  | "fixpoint" -> Some C.Int_Analysis
  | _ -> None

let domain_of_string int_analysis = function
  | "sign" -> Some C.Sign_Analysis
  | "interval" -> Some C.Interval_Analysis
  | "int" -> Some int_analysis
  | "parity" -> Some C.Parity_Analysis
  | "congruence" -> Some C.Congruence_Analysis
  | "order" -> Some C.Order_Analysis
  | _ -> None

let bounded_narrowing n =
  Some (C.Globals_Bounded_Narrowing (C.nat_of_integer (Z.of_int n)))

let globals_of_string = function
  | "join" -> Some C.Globals_Join
  | "per-origin" -> Some C.Globals_Per_Origin
  | "warrow" -> Some C.Globals_Warrow
  | "warrow-per-origin" -> Some C.Globals_Warrow_Per_Origin
  | "bounded-narrowing" -> bounded_narrowing 5
  | s -> (
      match String.split_on_char ':' s with
      | [ "bounded-narrowing"; n ] -> (
          match int_of_string_opt n with
          | Some n when n >= 0 -> bounded_narrowing n
          | _ -> None)
      | _ -> None)

(* The depth arrives as a JavaScript number. Only one that fits a Wasm OCaml
   int would arrive as an int; reading it as a number first turns a fraction
   or a huge value into an error message instead of a trap. *)
let context_of_string mode (depth : Js.number_t) =
  let depth = Js.to_float depth in
  match mode with
  | "none" -> Ok C.Ctx_None
  | "entry-state" -> Ok C.Ctx_EntryState
  | "call-string"
    when Float.is_integer depth && depth >= 0. && depth <= float_of_int max_int
    ->
      Ok (C.Ctx_CallString (C.nat_of_integer (Z.of_float depth)))
  | "call-string" -> Error "Call-string depth must be a non-negative integer"
  | _ -> Error ("Unknown context mode: " ^ mode)

(* -------------------------------------------------------------------------- *)
(* Browser entry point                                                        *)
(* -------------------------------------------------------------------------- *)

(* A comma list, kept exactly as given, and no names at all as the empty list:
   run_voblint alone decides whether it is a valid activation. *)
let domains_of_string int_analysis names =
  List.fold_right
    (fun name acc ->
      match (domain_of_string int_analysis name, acc) with
      | Some d, Ok ds -> Ok (d :: ds)
      | None, _ -> Error ("Unknown analysis domain: " ^ name)
      | _, (Error _ as e) -> e)
    (if names = "" then [] else String.split_on_char ',' names)
    (Ok [])

(* None is tracing off; otherwise the format and whether text is verbose. *)
let trace_of_string = function
  | "off" -> Ok None
  | "compact" -> Ok (Some (Solver_trace.Text, false))
  | "verbose" -> Ok (Some (Solver_trace.Text, true))
  | "jsonl" -> Ok (Some (Solver_trace.Jsonl, false))
  | mode -> Error ("Unknown trace mode: " ^ mode)

let trace_text (format, verbose) ~source ~domains ~globals ~context result =
  let buffer = Buffer.create 4096 in
  Solver_trace.emit ~out:(Buffer.add_string buffer) ~format ~verbose ~source
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

(* What a run records at most: a run that never finishes stops growing here. *)
let live_event_limit = 50_000

let post_chunk text =
  let sink = Js.Unsafe.get Js.Unsafe.global "Voblint_trace_chunk" in
  if Js.typeof sink = Js.string "function" then
    ignore (Js.Unsafe.fun_call sink [| Js.Unsafe.inject (Js.string text) |])

let stream_live ~source ~domains ~globals ~context =
  let buffer = Buffer.create 4096 in
  let last = ref (now_ms ()) and since = ref 0 in
  let render =
    Solver_trace.live_verbose ~out:(Buffer.add_string buffer) ~source
      ~analyses:(List.map Result_text.analysis_label domains)
      ~context:(Solver_trace.context_name context)
      ~globals ~program:"browser.vimp" ()
  in
  let flush () =
    if Buffer.length buffer > 0 then begin
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
      if !Solver_trace_hook.kept >= live_event_limit then begin
        Buffer.add_string buffer
          (Printf.sprintf
             "\nTrace stopped after %d events; the run goes on unrecorded.\n"
             live_event_limit);
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

  (* Set on every call: the worker keeps this module alive between runs. *)
  Solver_trace_hook.enabled :=
    Result.fold ~ok:Option.is_some ~error:(fun _ -> false) trace;
  Solver_trace_hook.reset ();
  stop_live ();

  let answer =
    match
      ( trace,
        int_analysis_of_string refinement_name,
        globals_of_string globals_name,
        context_of_string context_name context_depth )
    with
    | Error message, _, _, _ -> Render_json.error_json message
    | _, None, _, _ ->
        Render_json.error_json ("Unknown int refinement: " ^ refinement_name)
    | _, _, None, _ ->
        Render_json.error_json ("Unknown globals rule: " ^ globals_name)
    | _, _, _, Error message -> Render_json.error_json message
    | Ok trace, Some int_analysis, Some globals, Ok context -> (
        match domains_of_string int_analysis analysis_name with
        | Error message -> Render_json.error_json message
        | Ok domains -> (
            try
              let program, stmt_positions, header_positions =
                Vimp_frontend.program "browser.vimp" source
              in
              if trace = Some (Solver_trace.Text, true) then
                stream_live ~source:(source, stmt_positions) ~domains
                  ~globals:globals_name ~context;
              let analysis_start = now_ms () in
              let answer =
                Fun.protect ~finally:stop_live (fun () ->
                    Value_symbols.decode_answer
                      (C.run_voblint domains globals context program))
              in
              let analysis_ms = now_ms () -. analysis_start in
              let raw =
                Render_json.run_voblint_json ~domains ~globals ~ctx:context
                  program answer
              in
              match answer with
              | C.Invalid_Activation ->
                  Render_json.error_json ~raw
                    "Select at least one analysis, each at most once"
              | C.Malformed_Program ->
                  let message =
                    match Wf_explain.explain program with
                    | Some reason -> "Program is not well-formed: " ^ reason
                    | None -> "Program is not well-formed"
                  in
                  Render_json.error_json ~raw message
              | C.Analysed result ->
                  let trace =
                    Option.map
                      (fun form ->
                        trace_text form ~source:(source, stmt_positions)
                          ~domains ~globals:globals_name ~context result)
                      trace
                  in
                  Render_json.result_json ?trace analysis_ms program
                    ~stmt_positions ~header_positions ~raw result
            with Vimp_frontend.Parse_error { line; col; msg; _ } ->
              Render_json.parse_error_json ~line ~column:col msg))
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
