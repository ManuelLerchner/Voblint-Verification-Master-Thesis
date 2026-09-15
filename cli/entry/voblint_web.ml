(* Browser adapter for the generated analyzer.

   Parsing, DOT rendering, JSON rendering and browser integration are
   intentionally outside the Isabelle export. The actual analysis call uses
   the same generated [run_voblint] entry point as the native CLI.

   A successful call returns the report rows and, when the selected generated
   view publishes one, the graph from that same [AnalysisResult]. The browser
   never performs a second solve merely to obtain a drawing.

   JavaScript API:

     Voblint_run(
       analysis,
       solver,
       context,
       context_depth,
       source
     )

   Examples:

     Voblint_run("interval", "default", "none", 0, source)

     Voblint_run(
       "interval",
       "default",
       "call-string",
       1,
       source
     )

   [context_depth] is ignored unless [context = "call-string"].

   "default" means that no explicit solver choice is supplied to
   [run_voblint], so the generated dispatcher chooses the production
   configuration.
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

type browser_solver = Default_Solver | Explicit_Solver of C.solver_choice

let solver_of_string = function
  | "default" -> Some Default_Solver
  | "join" -> Some (Explicit_Solver C.Solver_Join)
  | "per-origin" -> Some (Explicit_Solver C.Solver_PerOrigin)
  | "warrow" -> Some (Explicit_Solver C.Solver_Warrow)
  | "warrow-per-origin" -> Some (Explicit_Solver C.Solver_WarrowPerOrigin)
  | _ -> None

let solver_argument = function
  | Default_Solver -> None
  | Explicit_Solver solver -> Some solver

let context_of_string mode depth =
  match mode with
  | "none" -> Ok C.Ctx_None
  | "entry-state" -> Ok C.Ctx_EntryState
  | "call-string" when depth >= 1 ->
      Ok (C.Ctx_CallString (C.nat_of_integer (Z.of_int depth)))
  | "call-string" -> Error "Call-string depth must be at least 1"
  | _ -> Error ("Unknown context mode: " ^ mode)

(* -------------------------------------------------------------------------- *)
(* Analysis result rendering                                                  *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Browser entry point                                                        *)
(* -------------------------------------------------------------------------- *)

let run analysis_js solver_js context_js context_depth source_js =
  let analysis_name = Js.to_string analysis_js in

  let solver_name = Js.to_string solver_js in

  let context_name = Js.to_string context_js in

  let source = Js.to_string source_js in

  let answer =
    match domain_of_string analysis_name, solver_of_string solver_name,
          context_of_string context_name context_depth with
    | None, _, _ -> Render_json.error_json ("Unknown analysis domain: " ^ analysis_name)
    | _, None, _ -> Render_json.error_json ("Unknown solver: " ^ solver_name)
    | _, _, Error message -> Render_json.error_json message
    | Some analysis, Some browser_solver, Ok context -> (
        try
          let program, check_positions, stmt_positions, header_positions =
            Vimp_frontend.program "browser.vimp" source
          in
          let analysis_start = now_ms () in
          let answer =
            C.run_voblint analysis (solver_argument browser_solver) context program
          in
          let analysis_ms = now_ms () -. analysis_start in
          let raw =
            Render_json.run_voblint_json ~kind:analysis ~solver:(solver_argument browser_solver)
              ~ctx:context program answer
          in
          match answer with
          | C.Malformed_Program -> Render_json.error_json ~raw "Program is not well-formed"
          | C.Unsupported_Configuration ->
              Render_json.error_json ~raw
                "This domain, solver, and context combination is not supported"
          | C.Analysed result ->
              Render_json.result_json analysis_ms program ~check_positions ~stmt_positions
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
