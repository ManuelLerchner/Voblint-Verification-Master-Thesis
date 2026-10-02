(* The configuration vocabulary the native CLI and the browser entry share: the
   names an analysis, a refinement mode, a globals rule and a context policy go
   by, in both directions, and the one call that analyses a program and renders
   the report. Each entry keeps its own error messages; the names are decided
   here once. *)

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

let config ~analyses ~globals ~context =
  C.Analysis_Config (analyses, globals, context)

(* The analysis and its rendering, in sequence: the report run_voblint returns is
   semantic, and the adapters read its rendering. *)
let analyse ~analyses ~globals ~context program =
  Value_symbols.render_answer
    (C.run_voblint (config ~analyses ~globals ~context) program)
