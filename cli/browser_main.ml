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
    Js.Unsafe.meth_call
      (Js.Unsafe.get Js.Unsafe.global "performance")
      "now"
      [||]
  in
  Js.to_float value

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


(* Every successful browser run asks for the canonical contextual graph.

   Context-insensitive analysis is not a separate rendering discipline: its
   result table has exactly one unit context. Entry-state and call-string runs
   keep every covered context separate. The solver chooses the solved table; it
   does not choose how that table is visualized. *)
let browser_view _browser_solver _context =
  C.View_Contexts


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


let output_json analysis_ms output =
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
     \"timing\":{\"analysis_ms\":%.3f},\
     \"checks\":[%s],\
     \"diagnostics\":[%s],\
     \"graph\":%s}"
    analysis_ms
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

                    let analysis_start =
                      now_ms ()
                    in
                    let answer =
                      C.run_voblint
                        analysis
                        (solver_argument browser_solver)
                        context
                        (browser_view browser_solver context)
                        program
                    in
                    let analysis_ms =
                      now_ms () -. analysis_start
                    in

                    match answer with
                    | C.Malformed_Program ->
                        error_json
                          "Program is not well-formed"

                    | C.Unsupported_Configuration ->
                        error_json
                          "This domain, solver, and context combination is not supported"

                    | C.Analysed output ->
                        Js.string
                          (output_json analysis_ms output)

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
 * Install it directly on the worker's global scope rather than passing it
 * through [Js.export], which would wrap the function again.
 *)
let () =
  Js.Unsafe.set
    Js.Unsafe.global
    (Js.string "Voblint_run")
    (Js.Unsafe.callback_with_arity 5 run)
