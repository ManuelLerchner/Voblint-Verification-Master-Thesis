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
  | "sign" -> Some C.Typed_Sign
  | "interval" -> Some C.Typed_Interval
  | "int" -> Some (C.Typed_Int refinement)
  | "parity" -> Some C.Typed_Parity
  | "congruence" -> Some C.Typed_Congruence
  | "order" -> Some C.Typed_Order
  | _ -> None

let name_of_analysis = function
  | C.Typed_Sign -> "sign"
  | C.Typed_Interval -> "interval"
  | C.Typed_Int _ -> "int"
  | C.Typed_Parity -> "parity"
  | C.Typed_Congruence -> "congruence"
  | C.Typed_Order -> "order"

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

(* A call string needs its depth; no other policy takes one. No context at all is a
   call string of length zero. *)
let context_of_name name depth =
  match (name, depth) with
  | "none", None -> Ok (C.Typed_Call_String (C.nat_of_integer Z.zero))
  | "entry-state", None -> Ok C.Typed_Entry_State
  | "call-string", Some k when k < 0 -> Error Negative_depth
  | "call-string", Some k ->
      Ok (C.Typed_Call_String (C.nat_of_integer (Z.of_int k)))
  | "call-string", None -> Error Missing_depth
  | ("none" | "entry-state"), Some _ -> Error Unexpected_depth
  | _ -> Error Unknown_context

(* Where a program's globals live: in each point's own state, or on the shared
   channel every point reads. *)
let program_globals_of_name = function
  | "flow-sensitive" -> Some C.Program_Globals_Flow_Sensitive
  | "flow-insensitive" -> Some C.Program_Globals_Flow_Insensitive
  | _ -> None

(* The options the domains read, under the paths of Goblint's configuration tree
   (src/config/options.schema.json). [--set PATH VALUE] reaches every row, a
   row's flag is an alias for its path, and the help text is generated from the
   rows. A further option is a further row and the field of voblint_conf it
   fills in [sem_of_settings]. *)
type option_spec = {
  path : string;
  flag : string option;
  values : string list;
  default : string;
  help : string;
}

let option_specs =
  [
    {
      path = "sem.int.signed_overflow";
      flag = Some "--signed-overflow";
      values = [ "assume_top"; "assume_wraparound" ];
      default = "assume_top";
      help =
        "How the integer domains treat a possible signed overflow: the kind's \
         top (Goblint's default) or wraparound, as the concrete semantics \
         computes it. Unsigned kinds wrap under both.";
    };
  ]

let option_of_path path = List.find_opt (fun o -> o.path = path) option_specs

let option_of_flag flag =
  List.find_opt (fun o -> o.flag = Some flag) option_specs

(* A request's value for a row: its last setting, or the row's default. *)
let setting settings spec =
  List.fold_left
    (fun v (p, x) -> if p = spec.path then x else v)
    spec.default settings

let signed_overflow_of_name = function
  | "assume_wraparound" -> C.Assume_Wraparound
  | _ -> C.Assume_Top

let sem_of_settings settings =
  let get path =
    match option_of_path path with
    | Some spec -> setting settings spec
    | None -> invalid_arg ("Analysis_request.sem_of_settings: " ^ path)
  in
  C.Sem_conf_ext (signed_overflow_of_name (get "sem.int.signed_overflow"), ())

(* A request as either entry receives it: names, not constructors. The native
   CLI reads it off its flags, the browser off the page's selections.
   [settings] are the PATH VALUE pairs of [option_specs], in the order given. *)
type request = {
  analyses : string list option;
  refinement : string option;
  globals : string;
  narrow_bound : int option;
  context : string;
  depth : int option;
  program_globals : string;
  settings : (string * string) list;
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
  | Unknown_option of string
  | Invalid_option_value of option_spec * string

type resolved = {
  domains : C.typed_domain list option;
  rule : C.globals_rule;
  mode : C.typed_context;
  placement : C.program_globals;
  sem : unit C.sem_conf_ext;
}

(* Every check a request needs before a program is read, in the order the CLI
   reports them. Each entry words the errors itself. *)
let resolve (r : request) : (resolved, request_error) result =
  let ( let* ) = Result.bind in
  let* () =
    List.fold_left
      (fun acc (path, value) ->
        let* () = acc in
        match option_of_path path with
        | None -> Error (Unknown_option path)
        | Some spec when not (List.mem value spec.values) ->
            Error (Invalid_option_value (spec, value))
        | Some _ -> Ok ())
      (Ok ()) r.settings
  in
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
  Ok { domains; rule; mode; placement; sem = sem_of_settings r.settings }

(* The configuration run_voblint receives, one value for every option. *)
let conf ~domains ~rule ~context ~placement ~sem =
  C.Voblint_conf_ext (domains, context, rule, placement, sem, ())

(* The message of the one abort in the generated analyzer: a chain of nested
   queries deeper than query_depth (MCP_Spec.ask_rec). Logically such a query
   answers top; the executable stops instead, so its run has no certified
   report. A query cycle is not this abort: it answers top and the run goes on. *)
let query_depth_exhausted = "query recursion exceeded query_depth"

(* The analysis and its rendering, in sequence: the report run_voblint returns is
   semantic, and the adapters read its rendering. A run cut short by query depth
   answers No_Answer, as one the solver did not finish does; no other failure is
   caught. *)
let analyse ~conf ~decls program =
  let answer =
    try C.run_voblint conf decls program
    with Failure msg when msg = query_depth_exhausted -> C.No_Answer
  in
  Value_symbols.render_answer answer

(* The options' help, generated from [option_specs], in the layout of the
   other flags: name at column 2, text wrapped at column 29. *)
let options_usage () =
  let indent = String.make 29 ' ' in
  let wrap text =
    let words = String.split_on_char ' ' text in
    let lines, last =
      List.fold_left
        (fun (lines, cur) w ->
          if cur = "" then (lines, w)
          else if String.length cur + 1 + String.length w > 50 then
            (cur :: lines, w)
          else (lines, cur ^ " " ^ w))
        ([], "") words
    in
    List.rev (last :: lines)
  in
  String.concat ""
    (List.map
       (fun o ->
         let names =
           (match o.flag with
             | Some f ->
                 [ Printf.sprintf "  %s %s" f (String.concat "|" o.values) ]
             | None -> [])
           @ [
               Printf.sprintf "  --set %s %s" o.path
                 (String.concat "|" o.values);
             ]
         in
         String.concat "\n" names ^ "\n"
         ^ String.concat ""
             (List.map
                (fun l -> indent ^ l ^ "\n")
                (wrap (o.help ^ " Default: " ^ o.default ^ "."))))
       option_specs)
