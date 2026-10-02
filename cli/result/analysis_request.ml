(* The configuration vocabulary the native CLI and the browser entry share: the
   names an analysis, a refinement mode, a globals rule and a context policy go
   by, in both directions, the validation of a whole request, and the one call
   that analyses a program and renders the report. Each entry keeps its own
   error messages; the names and the checks are decided here once. *)

module C = Voblint

let refinement_of_name = function
  | "never" -> Some C.Refine_Never
  | "once" -> Some C.Refine_Once
  | "fixpoint" -> Some C.Refine_Fixpoint
  | _ -> None

let default_refinement = C.Refine_Fixpoint

(* Each refinement mode is an analysis of its own in the generated carrier; all
   of them are int to the user. *)
let analysis_of_name ~refinement = function
  | "sign" -> Some C.Sign_Analysis
  | "interval" -> Some C.Interval_Analysis
  | "int" -> Some (C.Int_Analysis refinement)
  | "parity" -> Some C.Parity_Analysis
  | "congruence" -> Some C.Congruence_Analysis
  | "order" -> Some C.Order_Analysis
  | _ -> None

let name_of_analysis = function
  | C.Sign_Analysis -> "sign"
  | C.Interval_Analysis -> "interval"
  | C.Int_Analysis _ -> "int"
  | C.Parity_Analysis -> "parity"
  | C.Congruence_Analysis -> "congruence"
  | C.Order_Analysis -> "order"

(* The default of Goblint's solvers.td3.narrow-globs.narrow-gas option. The
   vendored rule counts differently: 0 still allows the one narrowing step of
   each switch. *)
let default_narrow_bound = 5

let bounded_narrowing n =
  C.Globals_Bounded_Narrowing (C.nat_of_integer (Z.of_int n))

(* "bounded-narrowing" takes its bound from the caller. *)
let globals_of_name ~narrow_bound = function
  | "join" -> Some C.Globals_Join
  | "per-origin" -> Some C.Globals_Per_Origin
  | "warrow" -> Some C.Globals_Warrow
  | "warrow-per-origin" -> Some C.Globals_Warrow_Per_Origin
  | "bounded-narrowing" -> Some (bounded_narrowing narrow_bound)
  | _ -> None

type context_error =
  | Unknown_context
  | Missing_depth
  | Negative_depth
  | Unexpected_depth

(* A call string needs its depth; no other policy takes one. *)
let context_of_name name depth =
  match (name, depth) with
  | "none", None -> Ok C.Ctx_None
  | "entry-state", None -> Ok C.Ctx_EntryState
  | "call-string", Some k when k < 0 -> Error Negative_depth
  | "call-string", Some k ->
      Ok (C.Ctx_CallString (C.nat_of_integer (Z.of_int k)))
  | "call-string", None -> Error Missing_depth
  | ("none" | "entry-state"), Some _ -> Error Unexpected_depth
  | _ -> Error Unknown_context

(* Where a program's globals live: in each point's own state, or on the shared
   channel every point reads. *)
let program_globals_of_name = function
  | "local" -> Some C.Program_Globals_Local
  | "shared" -> Some C.Program_Globals_Shared
  | _ -> None

let config ~analyses ~globals ~context ~program_globals =
  C.Analysis_Config (analyses, globals, context, program_globals)

(* A request as either entry receives it: names, not constructors. The native
   CLI reads it off its flags, the browser off the page's selections. *)
type request = {
  analyses : string list option;
  refinement : string option;
  globals : string;
  narrow_bound : int option;
  context : string;
  depth : int option;
  program_globals : string;
}

type request_error =
  | Unknown_refinement of string
  | Unknown_context_name of string
  | Unknown_globals of string
  | Unknown_analysis of string
  | Unknown_program_globals of string
  | Refinement_without_int
  | Negative_narrow_bound
  | Narrow_bound_without_rule
  | Context of context_error

type resolved = {
  domains : C.analysis_domain list option;
  rule : C.globals_rule;
  mode : C.context_mode;
  placement : C.program_globals;
}

(* Every check a request needs before a program is read, in the order the CLI
   reports them. Each entry words the errors itself. *)
let resolve (r : request) : (resolved, request_error) result =
  let ( let* ) = Result.bind in
  let* refinement =
    match r.refinement with
    | None -> Ok default_refinement
    | Some name -> (
        match refinement_of_name name with
        | Some mode -> Ok mode
        | None -> Error (Unknown_refinement name))
  in
  let* () =
    match context_of_name r.context None with
    | Error Unknown_context -> Error (Unknown_context_name r.context)
    | _ -> Ok ()
  in
  let* rule =
    match globals_of_name ~narrow_bound:default_narrow_bound r.globals with
    | Some rule -> Ok rule
    | None -> Error (Unknown_globals r.globals)
  in
  let* domains =
    match r.analyses with
    | None -> Ok None
    | Some names ->
        List.fold_right
          (fun name acc ->
            let* ds = acc in
            match analysis_of_name ~refinement name with
            | Some d -> Ok (d :: ds)
            | None -> Error (Unknown_analysis name))
          names (Ok [])
        |> Result.map Option.some
  in
  let* () =
    match (r.refinement, r.analyses) with
    | Some _, names when not (List.mem "int" (Option.value names ~default:[]))
      ->
        Error Refinement_without_int
    | _ -> Ok ()
  in
  let* rule =
    match (r.globals, r.narrow_bound) with
    | "bounded-narrowing", Some n when n < 0 -> Error Negative_narrow_bound
    | "bounded-narrowing", n ->
        Ok (bounded_narrowing (Option.value n ~default:default_narrow_bound))
    | _, Some _ -> Error Narrow_bound_without_rule
    | _, None -> Ok rule
  in
  let* mode =
    Result.map_error (fun e -> Context e) (context_of_name r.context r.depth)
  in
  let* placement =
    match program_globals_of_name r.program_globals with
    | Some placement -> Ok placement
    | None -> Error (Unknown_program_globals r.program_globals)
  in
  Ok { domains; rule; mode; placement }

(* The analysis and its rendering, in sequence: the report run_voblint returns is
   semantic, and the adapters read its rendering. *)
let analyse ~analyses ~globals ~context ~program_globals program =
  Value_symbols.render_answer
    (C.run_voblint
       (config ~analyses ~globals ~context ~program_globals)
       program)
