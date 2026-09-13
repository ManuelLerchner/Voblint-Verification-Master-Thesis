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
(* JSON                                                                       *)
(* -------------------------------------------------------------------------- *)

let json_escape value =
  let buffer = Buffer.create (String.length value + 16) in

  String.iter
    (function
      | '"' ->
          Buffer.add_string buffer "\\\""

      | '\\' ->
          Buffer.add_string buffer "\\\\"

      | '\n' ->
          Buffer.add_string buffer "\\n"

      | '\r' ->
          Buffer.add_string buffer "\\r"

      | '\t' ->
          Buffer.add_string buffer "\\t"

      | c ->
          Buffer.add_char buffer c)
    value;

  Buffer.contents buffer


let json_string value =
  "\"" ^ json_escape value ^ "\""


let error_json message =
  Js.string
    (Printf.sprintf
       "{\"status\":\"error\",\"message\":%s}"
       (json_string message))


(* -------------------------------------------------------------------------- *)
(* Configuration                                                              *)
(* -------------------------------------------------------------------------- *)

let domain_of_string = function
  | "sign" ->
      Some C.Sign_Analysis

  | "interval" ->
      Some C.Interval_Analysis

  | "int" ->
      Some C.Int_Analysis

  | "parity" ->
      Some C.Parity_Analysis

  | "congruence" ->
      Some C.Congruence_Analysis

  | _ ->
      None


type browser_solver =
  | Default_Solver
  | Explicit_Solver of C.solver_choice


let solver_of_string = function
  | "default" ->
      Some Default_Solver

  | "join" ->
      Some (Explicit_Solver C.Solver_Join)

  | "per-origin" ->
      Some (Explicit_Solver C.Solver_PerOrigin)

  | "warrow" ->
      Some (Explicit_Solver C.Solver_Warrow)

  | "warrow-per-origin" ->
      Some (Explicit_Solver C.Solver_WarrowPerOrigin)

  | _ ->
      None


let solver_argument = function
  | Default_Solver ->
      None

  | Explicit_Solver solver ->
      Some solver


let context_of_string mode depth =
  match mode with
  | "none" ->
      Ok C.Ctx_None

  | "entry-state" ->
      Ok C.Ctx_EntryState

  | "call-string" when depth >= 1 ->
      Ok
        (C.Ctx_CallString
           (C.nat_of_integer (Z.of_int depth)))

  | "call-string" ->
      Error "Call-string depth must be at least 1"

  | _ ->
      Error ("Unknown context mode: " ^ mode)


(* The browser wants checks and a drawing from one result.

   Context-insensitive runs can use the checked-state view for both default
   and explicitly selected solvers.

   Context-sensitive production/default runs use the per-context view so the
   graph does not join away the very contexts the user requested.

   Explicit-solver contextual routes currently publish the report but not a
   graph-capable contextual state view. Preserve those valid report runs
   instead of rejecting them or silently performing a second analysis. *)
let browser_view browser_solver context =
  match browser_solver, context with
  | _, C.Ctx_None ->
      C.View_Checked_States

  | Default_Solver, C.Ctx_EntryState
  | Default_Solver, C.Ctx_CallString _ ->
      C.View_Contexts

  | Explicit_Solver _, C.Ctx_EntryState
  | Explicit_Solver _, C.Ctx_CallString _ ->
      C.View_Report


(* -------------------------------------------------------------------------- *)
(* Analysis result rendering                                                  *)
(* -------------------------------------------------------------------------- *)

let verdict = function
  | C.Bot ->
      "DEAD"

  | C.Lifted C.Check_Proved ->
      "PROVED"

  | C.Lifted C.Check_Refuted ->
      "REFUTED"

  | C.Lifted C.Check_Unknown ->
      "UNKNOWN"


let node = function
  | C.Statement n ->
      "pp" ^ Z.to_string (C.integer_of_nat n)

  | C.FunctionEntry name ->
      "entry_" ^ name

  | C.FunctionResult name ->
      "result_" ^ name


let check_json row =
  Printf.sprintf
    "{\"point\":%s,\"condition\":%s,\"verdict\":%s,\"state\":%s}"
    (json_string (node (C.row_point row)))
    (json_string (C.row_condition row))
    (json_string (verdict (C.row_verdict row)))
    (json_string (C.row_state row))


let diagnostic_severity diagnostic =
  match C.diagnostic_verdict diagnostic with
  | C.Check_Refuted ->
      "error"

  | C.Check_Proved
  | C.Check_Unknown ->
      "warning"


let diagnostic_json diagnostic =
  Printf.sprintf
    "{\"severity\":%s,\"message\":%s}"
    (json_string (diagnostic_severity diagnostic))
    (json_string (C.diagnostic_message diagnostic))


let graph_json output =
  match C.out_graph output with
  | None ->
      "null"

  | Some graph ->
      json_string (Dot_render.render graph)


let output_json output =
  let checks =
    C.out_checks output
    |> List.map check_json
    |> String.concat ","
  in

  let diagnostics =
    C.out_diagnostics output
    |> List.map diagnostic_json
    |> String.concat ","
  in

  Printf.sprintf
    "{\"status\":\"ok\",\
     \"checks\":[%s],\
     \"diagnostics\":[%s],\
     \"graph\":%s}"
    checks
    diagnostics
    (graph_json output)


(* -------------------------------------------------------------------------- *)
(* Browser entry point                                                        *)
(* -------------------------------------------------------------------------- *)

let run analysis_js solver_js context_js context_depth source_js =
  let analysis_name =
    Js.to_string analysis_js
  in

  let solver_name =
    Js.to_string solver_js
  in

  let context_name =
    Js.to_string context_js
  in

  let source =
    Js.to_string source_js
  in

  match domain_of_string analysis_name with
  | None ->
      error_json
        ("Unknown analysis domain: " ^ analysis_name)

  | Some analysis ->
      begin
        match solver_of_string solver_name with
        | None ->
            error_json
              ("Unknown solver: " ^ solver_name)

        | Some browser_solver ->
            begin
              match context_of_string context_name context_depth with
              | Error message ->
                  error_json message

              | Ok context ->
                  try
                    let program, _, _ =
                      Vimp_frontend.program
                        "browser.vimp"
                        source
                    in

                    match
                      C.run_voblint
                        analysis
                        (solver_argument browser_solver)
                        context
                        (browser_view browser_solver context)
                        program
                    with
                    | C.Malformed_Program ->
                        error_json
                          "Program is not well-formed"

                    | C.Unsupported_Configuration ->
                        error_json
                          "This domain, solver, and context combination is not supported"

                    | C.Analysed output ->
                        Js.string (output_json output)

                  with
                  | Vimp_frontend.Parse_error
                      { line; col; msg; _ } ->
                      Js.string
                        (Printf.sprintf
                           "{\"status\":\"error\",\
                            \"message\":%s,\
                            \"line\":%d,\
                            \"column\":%d}"
                           (json_string msg)
                           line
                           col)
            end
      end


(*
 * [callback_with_arity] already creates the JavaScript callback.
 * Install it directly on globalThis/window rather than passing it through
 * [Js.export], which would wrap the function again.
 *)
let () =
  Js.Unsafe.set
    Js.Unsafe.global
    (Js.string "Voblint_run")
    (Js.Unsafe.callback_with_arity 5 run)
