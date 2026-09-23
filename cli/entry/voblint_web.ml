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
       source
     )

   Examples:

     Voblint_run("interval", "warrow", "none", 0, source)

     Voblint_run(
       "interval",
       "join",
       "call-string",
       1,
       source
     )

   [context_depth] is ignored unless [context = "call-string"].

   [globals] names how the solver merges side-effected globals: "join",
   "per-origin", "warrow" or "warrow-per-origin".
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

let domain_of_string = function
  | "sign" -> Some C.Sign_Analysis
  | "interval" -> Some C.Interval_Analysis
  | "int" -> Some C.Int_Analysis
  | "parity" -> Some C.Parity_Analysis
  | "congruence" -> Some C.Congruence_Analysis
  | _ -> None

let globals_of_string = function
  | "join" -> Some C.Globals_Join
  | "per-origin" -> Some C.Globals_Per_Origin
  | "warrow" -> Some C.Globals_Warrow
  | "warrow-per-origin" -> Some C.Globals_Warrow_Per_Origin
  | _ -> None

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

let run analysis_js globals_js context_js context_depth source_js =
  let analysis_name = Js.to_string analysis_js in

  let globals_name = Js.to_string globals_js in

  let context_name = Js.to_string context_js in

  let source = Js.to_string source_js in

  let answer =
    match
      ( domain_of_string analysis_name,
        globals_of_string globals_name,
        context_of_string context_name context_depth )
    with
    | None, _, _ ->
        Render_json.error_json ("Unknown analysis domain: " ^ analysis_name)
    | _, None, _ ->
        Render_json.error_json ("Unknown globals rule: " ^ globals_name)
    | _, _, Error message -> Render_json.error_json message
    | Some analysis, Some globals, Ok context -> (
        try
          let program, stmt_positions, header_positions =
            Vimp_frontend.program "browser.vimp" source
          in
          let analysis_start = now_ms () in
          let answer =
            Value_symbols.decode_answer
              (C.run_voblint analysis globals context program)
          in
          let analysis_ms = now_ms () -. analysis_start in
          let raw =
            Render_json.run_voblint_json ~kind:analysis ~globals ~ctx:context
              program answer
          in
          match answer with
          | C.Malformed_Program ->
              let message =
                match Wf_explain.explain program with
                | Some reason -> "Program is not well-formed: " ^ reason
                | None -> "Program is not well-formed"
              in
              Render_json.error_json ~raw message
          | C.Analysed result ->
              Render_json.result_json analysis_ms program ~stmt_positions
                ~header_positions ~raw result
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
    (Js.Unsafe.callback_with_arity 5 run)
