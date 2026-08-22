(* voblint: a thin CLI over the Isabelle-generated, proved-sound analyzer.

   source text (unverified adapter)
       -> Vimp_lexer/Vimp_parser (this directory, generated from
          grammar/vimp.yaml by scripts/gen_vimp_menhir.py -- ocamllex +
          Menhir, NOT verified) via Vimp_frontend (hand-written glue)
       -> imp_prog
       -> Voblint_CLI.Analysis_Config.mk_analysis_config (one config value)
       -> Voblint_CLI.Analyse_Dispatch.analyse_config/analyse_config_ctx/
          analyse_config_with_state (Isabelle-generated; each consults
          Analysis_Config.resolve_analysis_config, the single domain/solver/
          context legality-and-defaults table, then dispatches to the
          matching typed report function)
       -> proved analysis results, subject to the Isabelle theorem
          assumptions (solver termination and check reachability -- see
          Example_Analysis_Dispatch.thy's soundness corollaries)

   Trust boundary: soundness applies to the imp_prog the parser produces, not
   to the claim that this imp_prog faithfully represents the text file the
   user wrote. The parser is unverified, the same way Goblint's own C
   frontend is unverified -- parsing was never in the soundness scope of
   either project. A parser bug can change *which* program gets analyzed; it
   cannot invalidate the analyzer's soundness theorem for the AST actually
   produced. See docs/CLI_DESIGN.md. *)

let usage =
  "voblint --analysis sign|interval|int|parity [--context none|entry-state|call-string] \
   [--context-depth K] [--context-graph collapsed|expanded] [--dot] \
   [--timeout SECONDS] FILE.vimp\n\
   voblint --parse-only FILE.vimp\n\n\
   Options:\n\
  \  --analysis sign|interval|int|parity[,...]\n\
  \                             Abstract domain to run (required, unless\n\
  \                             --parse-only). int is the refining composite\n\
  \                             Sign x Interval x Parity x Congruence domain,\n\
  \                             fixed at its most precise refinement mode\n\
  \                             (Refine_Fixpoint) and the warrowing solver.\n\
  \                             parity is the four-element Bot/Even/Odd/Top\n\
  \                             lattice; it decides equalities only by\n\
  \                             refuting them across differing parities, and\n\
  \                             is context-insensitive.\n\
  \                             A comma list (e.g. int,interval) puts every\n\
  \                             named domain side by side in one --html\n\
  \                             report, one <analysis> block per node, so\n\
  \                             their precision can be compared in place.\n\
  \                             Requires --html and --context none; every\n\
  \                             other output path uses the first domain only.\n\
  \  --context none|entry-state|call-string\n\
  \                             Context sensitivity (default: none, today's\n\
  \                             flow-insensitive, call-site-insensitive\n\
  \                             behaviour). entry-state re-analyzes each\n\
  \                             callee per distinct entered-argument context,\n\
  \                             including under --dot/--dot-full/\n\
  \                             --graph-snapshot (a node covered by several\n\
  \                             contexts renders their joined state under\n\
  \                             --context-graph, which now defaults to drawing\n\
  \                             them separately);\n\
  \                             supported by sign, interval and int.\n\
  \                             call-string re-analyzes each callee per\n\
  \                             distinct bounded call history (requires\n\
  \                             --context-depth K, K >= 1), supported by\n\
  \                             sign, interval and int, including under\n\
  \                             --dot/--dot-full/--graph-snapshot. parity is\n\
  \                             context-insensitive for now. Any other\n\
  \                             --analysis/--context combination is a clear\n\
  \                             configuration error, not a silent fallback to\n\
  \                             --context none.\n\
  \  --context-depth K          Call-string bound (only valid with --context\n\
  \                             call-string; must be at least 1 -- a call\n\
  \                             string needs to keep at least one call site\n\
  \                             to separate anything, so a bound of 0 has no\n\
  \                             positive use as a public value and is\n\
  \                             rejected rather than silently treated as\n\
  \                             --context none).\n\
  \  --context-graph collapsed|expanded\n\
  \                             How --dot/--dot-full/--graph-snapshot/--html\n\
  \                             render --context entry-state. expanded draws\n\
  \                             one node per (point, context) pair, annotated\n\
  \                             through the same solved AnalysisResult with no\n\
  \                             join, so a point dead in one activation and\n\
  \                             live in another renders as two distinct nodes\n\
  \                             rather than one live-looking join. collapsed\n\
  \                             draws one node per program point with its\n\
  \                             contexts joined.\n\
  \                             The default is expanded wherever the\n\
  \                             configuration supports it: a context-sensitive\n\
  \                             run is asked for because the contexts matter.\n\
  \                             The expanded renderer is typed in the context\n\
  \                             type itself and only --analysis interval has\n\
  \                             that configuration today, so the other domains\n\
  \                             default to collapsed -- but an explicit\n\
  \                             --context-graph expanded there is still a\n\
  \                             configuration error, not a silent fallback, and\n\
  \                             so is expanded with --context none or with\n\
  \                             --context call-string (whose renderer is always\n\
  \                             per-context and has no collapsed mode).\n\
  \  --solver join|per-origin|warrow|warrow-per-origin\n\
  \                             Pick the vendored solver's update-rule\n\
  \                             discipline directly, bypassing the domain's\n\
  \                             production default (experimental; issue\n\
  \                             #131). warrow is supported by interval and\n\
  \                             int; sign has no widen instance, and parity\n\
  \                             has one but no solved table behind it yet.\n\
  \                             Supported by the plain text report and by\n\
  \                             --html, which reads the state table the chosen\n\
  \                             discipline solved. Not by --dot/--dot-full/\n\
  \                             --graph-snapshot, which annotate from a report\n\
  \                             carrying no per-node state; and not by --html\n\
  \                             together with --context, whose per-solver\n\
  \                             routes publish verdicts without a state table.\n\
  \  --dot                      Emit a GraphViz .dot rendering of the solved CFG,\n\
  \                             annotated at check nodes only, instead of the\n\
  \                             textual check report.\n\
  \  --dot-full                 Like --dot, but every node is annotated with its\n\
  \                             own computed abstract state, not just check nodes.\n\
  \  --html                     Write a browsable HTML result directory (default:\n\
  \                             result/, as Goblint's own --html does)\n\
  \                             (abstract states live in per-node documents, so\n\
  \                             the CFG stays readable where --dot-full does\n\
  \                             not). Needs `dot` on PATH for the graph pane,\n\
  \                             and the vendor/g2html submodule for the\n\
  \                             frontend. Serve it and open index.xml:\n\
  \                               python3 -m http.server --directory result 8080\n\
  \  --html-out DIR             Write that directory to DIR instead. Implies\n\
  \                             --html.\n\
  \  --graph-snapshot           Emit a deterministic, DOT-free textual snapshot\n\
  \                             of the solved CFG (clusters/nodes/edges), for\n\
  \                             embedding as a regression fixture's expected\n\
  \                             output instead of a --dot rendering.\n\
  \  --parse-only               Parse and exit (0 on success, 2 with a\n\
  \                             file:line:col message on a parse error); runs\n\
  \                             no analysis, no --analysis needed. For syntax\n\
  \                             checking and parser conformance testing.\n\
  \                             A syntactically valid but ill-formed program\n\
  \                             (e.g. a wrong-arity special call) still exits\n\
  \                             4 with no message here -- well-formedness is\n\
  \                             checked only on the full run below, after\n\
  \                             --parse-only's own early exit.\n\
  \  --timeout SECONDS          Wall-clock budget for the analysis subprocess\n\
  \                             (default 10). The analyzer is proved sound but\n\
  \                             not proved total (see CLI_DESIGN.md's Interval\n\
  \                             containment note), so it runs in a killable\n\
  \                             child process rather than in-process.\n\
  \  --help                     Show this message.\n\n\
   Trust boundary: results are sound for the program this file's unverified\n\
  \  parser actually built, not a guarantee that the parser read your source\n\
  \  correctly. The analyzer core (parsing excluded) is generated from a\n\
  \  machine-checked Isabelle/HOL proof."

let un_char c = Char.chr (Z.to_int (Voblint_CLI.Core.integer_of_char c))
let un_string cs = String.concat "" (List.map (fun c -> String.make 1 (un_char c)) cs)

let node_label = function
  | Voblint_CLI.Core.Statement n -> "pp" ^ Z.to_string (Voblint_CLI.Core.integer_of_nat n)
  | Voblint_CLI.Core.FunctionEntry s -> "entry_" ^ s
  | Voblint_CLI.Core.FunctionResult s -> "result_" ^ s

let verdict_label = function
  | Voblint_CLI.Core.Check_Proved -> "PROVED"
  | Voblint_CLI.Core.Check_Refuted -> "REFUTED"
  | Voblint_CLI.Core.Check_Unknown -> "UNKNOWN"

(* analyse_with_state's report carries an exact, proved unreachable flag per
   entry (resolved_st_q_lifted_is_bot_for, Exec_St.thy) instead of leaving
   this CLI to reconstruct reachability by probing a variable list against
   the already-converted state -- see docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md,
   section 9. Unreachable entries are suppressed entirely, matching Goblint's
   "__goblint_check(0); // NOWARN (unreachable)" convention (no output at
   that location), rather than shown with a vacuous PROVED verdict. *)
let render_text_report (report :
      (Voblint_CLI.Core.cfg_node
       * (Voblint_CLI.Core.exp
          * (Voblint_CLI.Core.check_result
             * (bool * (string -> Voblint_CLI.Analyse_Dispatch.abstract_value)))))
      list)
    (check_positions : (int * int) list) =
  let buf = Buffer.create 256 in
  (* report and check_positions are both in check-declaration order, one
     entry per __voblint_check the parser saw -- see Vimp_frontend.program's
     doc comment. A length mismatch would mean that invariant broke, so let
     it raise rather than silently misalign. *)
  List.iter2
    (fun (node, (cond, (verdict, (unreachable, f)))) (line, col) ->
       if not unreachable then begin
         let vars = Voblint_CLI.State_Report_GraphViz.exp_vnames_list cond in
         let state =
           vars
           |> List.map (fun x ->
             x ^ "=" ^ un_string (Voblint_CLI.State_Report_GraphViz.string_of_abstract_value (f x)))
           |> String.concat ", "
         in
         Buffer.add_string buf
           (Printf.sprintf "%d:%-2d %-10s %-20s %-8s %s\n" line col (node_label node)
              (un_string (Voblint_CLI.Core.string_of_exp (Voblint_CLI.Core.nat_of_integer Z.zero) cond))
              (verdict_label verdict) state)
       end)
    report check_positions;
  Buffer.contents buf

let report_row buf (line, col) node cond verdict =
  Buffer.add_string buf
    (Printf.sprintf "%d:%-2d %-10s %-20s %-8s\n" line col (node_label node)
       (un_string (Voblint_CLI.Core.string_of_exp (Voblint_CLI.Core.nat_of_integer Z.zero) cond))
       (verdict_label verdict))

(* analyse_with_solver's check_report_entry list carries no per-variable state
   projection (unlike analyse_with_state's report) and no deadness channel, so
   there is no dead-code filter or per-variable state column here -- only the
   check verdict itself. *)
let render_flat_report
    (report :
      (Voblint_CLI.Core.cfg_node * (Voblint_CLI.Core.exp * Voblint_CLI.Core.check_result)) list)
    (check_positions : (int * int) list) =
  let buf = Buffer.create 256 in
  List.iter2
    (fun (node, (cond, verdict)) (line, col) -> report_row buf (line, col) node cond verdict)
    report check_positions;
  Buffer.contents buf

(* analyse_ctx's report distinguishes Dead -- every context covering the check
   is unreachable -- from a decided verdict (Abstract_Checks.thy's
   contextual_verdict). Dead rows are suppressed entirely, matching what
   render_text_report already does with analyse_with_state's unreachable flag
   and Goblint's "__goblint_check(0); // NOWARN (unreachable)" convention,
   rather than printing a verdict for code no execution reaches.

   The filter happens inside the iter2 callback, never by pre-filtering either
   list: report and check_positions must stay the same length and the same
   order, one entry per __voblint_check the parser saw. *)
let render_ctx_report
    (report :
      (Voblint_CLI.Core.cfg_node
       * (Voblint_CLI.Core.exp * Voblint_CLI.Core.contextual_verdict))
      list)
    (check_positions : (int * int) list) =
  let buf = Buffer.create 256 in
  List.iter2
    (fun (node, (cond, verdict)) (line, col) ->
       match verdict with
       | Voblint_CLI.Core.Dead -> ()
       | Voblint_CLI.Core.Decided v -> report_row buf (line, col) node cond v)
    report check_positions;
  Buffer.contents buf

(* Names the analysis in the report's own <analysis name="..."> element, so a
   node document says which domain produced the state it shows. *)
let analysis_label = function
  | Voblint_CLI.Analysis_Config.Sign_Analysis -> "sign"
  | Voblint_CLI.Analysis_Config.Interval_Analysis -> "interval"
  | Voblint_CLI.Analysis_Config.Int_Analysis -> "int"
  | Voblint_CLI.Analysis_Config.Parity_Analysis -> "parity"

let rec mkdir_p dir =
  if dir <> "" && dir <> "/" && dir <> "." && not (Sys.file_exists dir) then begin
    mkdir_p (Filename.dirname dir);
    try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let rec rm_rf path =
  match Sys.is_directory path with
  | true ->
    Array.iter (fun n -> rm_rf (Filename.concat path n)) (Sys.readdir path);
    (try Unix.rmdir path with Unix.Unix_error _ -> ())
  | false -> (try Sys.remove path with Sys_error _ -> ())
  | exception Sys_error _ -> ()

(* A second run into the same directory must not leave the previous program's
   node documents behind: they are reachable from the frontend and describe a
   different CFG. Only the subtrees this emitter owns are cleared, and only once
   index.xml identifies the directory as a previous report -- so pointing
   --html-out at a directory holding anything else is refused rather than
   quietly emptied. *)
let owned_entries = [ "nodes"; "files"; "dot"; "cfgs"; "index.xml" ]

let prepare_report_dir dir =
  if not (Sys.file_exists dir) then mkdir_p dir
  else if not (Sys.is_directory dir) then begin
    Printf.eprintf "voblint: %s exists and is not a directory\n" dir;
    exit 5
  end
  else if Array.length (Sys.readdir dir) > 0 then begin
    if not (Sys.file_exists (Filename.concat dir "index.xml")) then begin
      Printf.eprintf
        "voblint: refusing to write a report into non-empty %s (no index.xml, so \
         this is not a previous report directory)\n"
        dir;
      exit 5
    end;
    List.iter (fun n -> rm_rf (Filename.concat dir n)) owned_entries
  end

let write_report_file root (f : Html_report.file) =
  let path = Filename.concat root f.Html_report.path in
  mkdir_p (Filename.dirname path);
  let oc = open_out path in
  output_string oc f.Html_report.content;
  close_out oc

let copy_file src dst =
  let ic = open_in_bin src in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
       let n = in_channel_length ic in
       let data = really_input_string ic n in
       let oc = open_out_bin dst in
       output_string oc data;
       close_out oc)

(* The frontend is g2html's resources/, copied in verbatim. Its location is
   resolved relative to the binary so a built tree works in place; an explicit
   VOBLINT_FRONTEND overrides that for an installed layout. *)
let frontend_dir () =
  match Sys.getenv_opt "VOBLINT_FRONTEND" with
  | Some d -> Some d
  | None ->
    let candidate =
      Filename.concat
        (Filename.dirname (Filename.dirname Sys.executable_name))
        (Filename.concat "vendor" (Filename.concat "g2html" "resources"))
    in
    if Sys.file_exists candidate && Sys.is_directory candidate then Some candidate else None

type outcome =
  | Ok_text of string
  | Ok_dot of string
  | Ok_graph of string
  | Ok_report of string
  | Unsupported_combo of string

(* The analyzer is proved sound but not proved total (Interval especially,
   see docs/CLI_DESIGN.md's containment note) -- a killable subprocess bounds
   a hang or crash the same way it would for an unsuspecting CLI user, rather
   than taking this process down or hanging indefinitely in-process. *)
let run_contained ~timeout (f : unit -> outcome) : (outcome, string) result =
  let tmp = Filename.temp_file "voblint" ".out" in
  Fun.protect
    ~finally:(fun () -> try Sys.remove tmp with Sys_error _ -> ())
    (fun () ->
       match Unix.fork () with
       | 0 ->
         (* Child: never returns to the caller. *)
         let exit_code =
           try
             let oc = open_out tmp in
             (match f () with
              | Ok_text s -> output_string oc "T\n"; output_string oc s
              | Ok_dot s -> output_string oc "D\n"; output_string oc s
              | Ok_graph s -> output_string oc "G\n"; output_string oc s
              | Ok_report s -> output_string oc "R\n"; output_string oc s
              | Unsupported_combo s -> output_string oc "U\n"; output_string oc s);
             close_out oc;
             0
           with e ->
             let oc = open_out tmp in
             output_string oc ("E\n" ^ Printexc.to_string e);
             close_out oc;
             1
         in
         exit exit_code
       | pid ->
         let deadline = Unix.gettimeofday () +. timeout in
         let rec wait_loop () =
           match Unix.waitpid [ Unix.WNOHANG ] pid with
           | 0, _ ->
             if Unix.gettimeofday () > deadline then begin
               (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
               ignore (Unix.waitpid [] pid);
               Error (Printf.sprintf "analysis did not finish within %.0fs (killed)" timeout)
             end else begin
               ignore (Unix.select [] [] [] 0.05);
               wait_loop ()
             end
           | _, Unix.WEXITED 0 ->
             let ic = open_in tmp in
             let n = in_channel_length ic in
             let contents = really_input_string ic n in
             close_in ic;
             (match String.index_opt contents '\n' with
              | Some i ->
                let tag = String.sub contents 0 i in
                let body = String.sub contents (i + 1) (String.length contents - i - 1) in
                (match tag with
                 | "T" -> Ok (Ok_text body)
                 | "D" -> Ok (Ok_dot body)
                 | "G" -> Ok (Ok_graph body)
                 | "R" -> Ok (Ok_report body)
                 | "U" -> Ok (Unsupported_combo body)
                 | _ -> Error body)
              | None -> Error "analysis subprocess produced no output")
           | _, Unix.WEXITED code -> Error (Printf.sprintf "analysis subprocess exited with code %d" code)
           | _, (Unix.WSIGNALED s | Unix.WSTOPPED s) ->
             Error (Printf.sprintf "analysis subprocess terminated by signal %d" s)
         in
         wait_loop ())

(* Unset means "whatever the configuration supports": a context-sensitive run
   is asked for because the contexts matter, so drawing them is the useful
   default, and joining them away is the thing to opt into. An explicit choice
   is still honoured -- and still rejected where it cannot be served. *)
type context_graph_mode = Collapsed | Expanded

(* --context/--context-depth are two independent flags that can arrive in
   either order, but Ctx_CallString needs the depth at construction time --
   so parsing collects an intermediate tag + optional depth, and the final
   immutable Analysis_Config.context_mode value is assembled once, after
   parse_args returns, from both together. *)
type context_kind = CK_None | CK_EntryState | CK_CallString

let () =
  let analysis = ref None in
  (* Every domain named by --analysis, in order. Only --html reads past the
     head; see the comma-list note in parse_args. *)
  let analyses = ref [] in
  let context_kind = ref CK_None in
  let context_depth = ref None in
  let context_graph = ref None in
  let solver = ref None in
  let dot = ref false in
  let dot_full = ref false in
  let graph_snapshot = ref false in
  let html = ref false in
  (* Goblint's --html writes a fixed "result" directory; --html-out is the
     override. Taking no argument is what keeps `--html FILE.vimp` from reading
     the program as the output directory. *)
  let html_dir = ref "result" in
  let parse_only = ref false in
  let timeout = ref 10.0 in
  let file = ref None in
  let rec parse_args = function
    | [] -> ()
    | "--help" :: _ -> print_endline usage; exit 0
    | "--analysis" :: v :: rest ->
      (* A comma list asks one report to carry several domains side by side.
         The head stays the analysis every other output path means by
         "--analysis", so a single name behaves exactly as before. *)
      let kind_of name =
        match name with
        | "sign" -> Voblint_CLI.Analysis_Config.Sign_Analysis
        | "interval" -> Voblint_CLI.Analysis_Config.Interval_Analysis
        | "int" -> Voblint_CLI.Analysis_Config.Int_Analysis
        | "parity" -> Voblint_CLI.Analysis_Config.Parity_Analysis
        | _ -> prerr_endline ("unknown --analysis value: " ^ name); exit 1
      in
      let names = String.split_on_char ',' v |> List.filter (fun n -> n <> "") in
      if names = [] then begin
        prerr_endline "voblint: --analysis expects at least one domain";
        exit 1
      end;
      analyses := List.map kind_of names;
      analysis := Some (List.hd (List.map kind_of names));
      parse_args rest
    | "--context" :: v :: rest ->
      (match v with
       | "none" -> context_kind := CK_None
       | "entry-state" -> context_kind := CK_EntryState
       | "call-string" -> context_kind := CK_CallString
       | _ -> prerr_endline ("unknown --context value: " ^ v); exit 1);
      parse_args rest
    | "--context-depth" :: v :: rest ->
      (try context_depth := Some (int_of_string v)
       with _ -> prerr_endline ("--context-depth expects an integer: " ^ v); exit 1);
      parse_args rest
    | "--context-graph" :: v :: rest ->
      (match v with
       | "collapsed" -> context_graph := Some Collapsed
       | "expanded" -> context_graph := Some Expanded
       | _ -> prerr_endline ("unknown --context-graph value: " ^ v); exit 1);
      parse_args rest
    | "--solver" :: v :: rest ->
      (match v with
       | "join" -> solver := Some Voblint_CLI.Analysis_Config.Solver_Join
       | "per-origin" -> solver := Some Voblint_CLI.Analysis_Config.Solver_PerOrigin
       | "warrow" -> solver := Some Voblint_CLI.Analysis_Config.Solver_Warrow
       | "warrow-per-origin" ->
         solver := Some Voblint_CLI.Analysis_Config.Solver_WarrowPerOrigin
       | _ -> prerr_endline ("unknown --solver value: " ^ v); exit 1);
      parse_args rest
    | "--dot" :: rest -> dot := true; parse_args rest
    | "--dot-full" :: rest -> dot_full := true; parse_args rest
    | "--graph-snapshot" :: rest -> graph_snapshot := true; parse_args rest
    | "--html" :: rest -> html := true; parse_args rest
    | "--html-out" :: v :: rest -> html := true; html_dir := v; parse_args rest
    | [ "--html-out" ] -> prerr_endline "voblint: --html-out expects a directory"; exit 1
    | "--parse-only" :: rest -> parse_only := true; parse_args rest
    | "--timeout" :: v :: rest ->
      (try timeout := float_of_string v with _ -> prerr_endline "--timeout expects a number"; exit 1);
      parse_args rest
    | f :: rest when String.length f > 0 && f.[0] <> '-' -> file := Some f; parse_args rest
    | arg :: _ -> prerr_endline ("unrecognized argument: " ^ arg); exit 1
  in
  parse_args (List.tl (Array.to_list Sys.argv));
  (* --context-depth is only meaningful paired with --context call-string --
     a shape mismatch between the two flags as typed by the user, not a
     domain/solver/context legality question, so it is rejected here rather
     than folded into Ctx_CallString's own construction or deferred to
     Analysis_Config.resolve_analysis_config (which has no notion of
     --context-depth at all, the same way it has no notion of
     --context-graph). Once matched, the depth itself is handed to
     Ctx_CallString unchecked (a negative --context-depth clamps to nat's
     own zero via nat_of_integer, and k=0 is then rejected the ordinary way,
     by valid_analysis_config below -- no second k >= 1 check here). *)
  let context =
    match !context_kind, !context_depth with
    | CK_None, None -> Voblint_CLI.Analysis_Config.Ctx_None
    | CK_EntryState, None -> Voblint_CLI.Analysis_Config.Ctx_EntryState
    | CK_CallString, Some k ->
      Voblint_CLI.Analysis_Config.Ctx_CallString (Voblint_CLI.Core.nat_of_integer (Z.of_int k))
    | CK_CallString, None ->
      prerr_endline "voblint: --context call-string requires --context-depth K"; exit 1
    | (CK_None | CK_EntryState), Some _ ->
      prerr_endline "voblint: --context-depth is only valid with --context call-string"; exit 1
  in
  let context = ref context in
  let path =
    match !file with
    | Some p -> p
    | None -> prerr_endline "missing FILE.vimp"; prerr_endline usage; exit 1
  in
  let src =
    try
      let ic = open_in_bin path in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      s
    with Sys_error msg -> prerr_endline ("voblint: cannot read " ^ path ^ ": " ^ msg); exit 1
  in
  let prog, check_positions =
    try Vimp_frontend.program path src
    with Vimp_frontend.Parse_error { file; line; col; msg } ->
      Printf.eprintf "%s:%d:%d: parse error: %s\n" file line col msg;
      exit 2
  in
  if !parse_only then exit 0;
  if not (Voblint_CLI.Core.wf_program_compile_input_exec prog) then begin
    Printf.eprintf "%s: program is not well-formed\n" path;
    exit 4
  end;
  let kind =
    match !analysis with
    | Some k -> k
    | None -> prerr_endline "missing --analysis sign|interval"; prerr_endline usage; exit 1
  in
  (* One analysis_config value, one legality gate (Analysis_Config.thy's
     valid_analysis_config/resolve_analysis_config): every domain/solver/
     context combination the CLI accepts or rejects is decided there, not by
     a second, hand-maintained OCaml compatibility table. Every domain now has
     both an entry-state and a call-string branch; Interval accepts an explicit
     --solver alongside either context, since the routed equation system
     underneath either one is solved under all three disciplines exactly like
     the flat one, while Sign/Int are proved at Solver_Join only. *)
  let cfg = Voblint_CLI.Analysis_Config.mk_analysis_config kind !solver !context in
  if not (Voblint_CLI.Analysis_Config.valid_analysis_config cfg) then begin
    prerr_endline "voblint: unsupported --analysis/--context/--solver combination";
    exit 1
  end;
  (* The call-string depth as a nat, for the contextual renderers below.
     cs_ctx_dot_auto/cs_ctx_graph_snapshot_auto take k directly rather than
     re-deriving it from cfg's Ctx_CallString payload: the config value is a
     legality question (already settled by valid_analysis_config above), the
     renderer argument is a routing-policy one, and keeping them separate
     avoids a second unwrapping of the same datatype at the call site. *)
  let cs_depth () =
    match !context_depth with
    | Some k -> Voblint_CLI.Core.nat_of_integer (Z.of_int k)
    | None -> Voblint_CLI.Core.nat_of_integer Z.zero
  in
  (* expanded is meaningless without a context to expand -- reject rather than
     silently rendering the collapsed graph a bare --context-graph expanded
     might otherwise appear to have requested. *)
  if !context_graph = Some Expanded && !context = Voblint_CLI.Analysis_Config.Ctx_None then begin
    prerr_endline "voblint: --context-graph expanded requires --context entry-state";
    exit 1
  end;
  (* The expanded entry-state graph draws one node per (point, context) pair, so
     its renderer is typed in the context type itself -- ivl list -- unlike the
     collapsed renderings, which join contexts away and share one abstract_value
     projection across every domain. Only Interval has that expanded
     configuration today. Reject the other domains explicitly rather than fall
     through to Interval's renderer and emit a graph labelled with a different
     analysis's states, which is exactly the silent wrong output this check
     exists to prevent. *)
  if !context_graph = Some Expanded
     && !context = Voblint_CLI.Analysis_Config.Ctx_EntryState
     && kind <> Voblint_CLI.Analysis_Config.Interval_Analysis then begin
    prerr_endline
      "voblint: --context-graph expanded is only supported by --analysis interval";
    exit 1
  end;
  (* --context-graph has no effect on a call-string graph: that renderer is
     always per-context (it has no collapsed mode), so accepting the flag here
     would silently ignore it. *)
  if !context_graph = Some Expanded && !context_kind = CK_CallString then begin
    prerr_endline
      "voblint: --context-graph is not supported with --context call-string";
    exit 1
  end;
  (* --solver's flat check_report_entry list has no per-node state map to
     render, and entry_state_{full_state,report}_{dot,graph_snapshot}_auto
     are Interval-only regardless of --solver -- this compatibility is about
     report *shape* versus presentation, not analysis semantics, so it stays
     a CLI-level check rather than moving into analysis_config's scope. *)
  (* --html can show an explicitly chosen solver: every solver route already
     solves a state table, and solver_checked_export_auto reads the one the
     requested discipline produced. The stdout renderings still cannot -- they
     annotate from a report that carries no per-node state. *)
  if !solver <> None && (!dot || !dot_full || !graph_snapshot) then begin
    prerr_endline
      "voblint: --solver supports the plain text report and --html, not \
       --dot/--dot-full/--graph-snapshot";
    exit 1
  end;
  if !solver <> None && !html && !context <> Voblint_CLI.Analysis_Config.Ctx_None then begin
    prerr_endline
      "voblint: --solver with --html requires --context none";
    exit 1
  end;
  (* --html writes a directory; the other renderings write one document to
     stdout. Asking for both is a contradiction about where output goes, not a
     combination to silently resolve. *)
  if !html && (!dot || !dot_full || !graph_snapshot) then begin
    prerr_endline "voblint: --html cannot be combined with --dot/--dot-full/--graph-snapshot";
    exit 1
  end;
  (* The expanded renderer is typed in the context type itself, and only
     Interval has that configuration, so "draw the contexts" resolves to
     collapsed for the others rather than failing a run nobody misconfigured.
     An explicit --context-graph expanded is still rejected there, a few checks
     above: defaulting to what the configuration supports is not the same as
     ignoring what the user asked for. *)
  let expanded_supported =
    !context = Voblint_CLI.Analysis_Config.Ctx_EntryState
    && kind = Voblint_CLI.Analysis_Config.Interval_Analysis
  in
  let context_graph =
    match !context_graph with
    | Some mode -> mode
    | None -> if expanded_supported then Expanded else Collapsed
  in
  let context_graph = ref context_graph in
  (* Several domains in one report means several solves feeding one set of node
     documents, merged by node identifier. Identifiers are built from the CFG
     and the context, so they only agree across domains when the context is the
     same for all of them -- which is why a list is confined to the
     context-insensitive path rather than silently merging mismatched nodes. *)
  if List.length !analyses > 1 then begin
    if not !html then begin
      prerr_endline
        "voblint: --analysis with several domains is only supported by --html";
      exit 1
    end;
    if !context <> Voblint_CLI.Analysis_Config.Ctx_None then begin
      prerr_endline
        "voblint: --analysis with several domains requires --context none";
      exit 1
    end
  end;
  (* Prepared here, not inside the contained child: a refusal to write into the
     given directory is an argument error the user should see as one, not as a
     subprocess exit code relayed through the analysis timeout wrapper. *)
  if !html then prepare_report_dir !html_dir;
  match
    run_contained ~timeout:!timeout (fun () ->
      if !html then
        let dir = !html_dir in
        let graph_for k =
          match !solver with
          | Some sc ->
            (match Voblint_CLI.State_Report_GraphViz.solver_checked_export_auto k sc prog with
             | Some g -> g
             | None ->
               (* valid_analysis_config already rejected the combinations with
                  no table behind them, so this is unreachable rather than a
                  fallback worth inventing a rendering for. *)
               failwith "unsupported --analysis/--solver combination")
          | None ->
          if !context_kind = CK_CallString then
            Voblint_CLI.State_Report_GraphViz.cs_ctx_export_auto k (cs_depth ()) prog
          else if !context_graph = Expanded then
            Voblint_CLI.State_Report_GraphViz.entry_state_ctx_export_auto prog
          else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
            Voblint_CLI.State_Report_GraphViz.entry_state_full_state_checked_export_auto k prog
          else Voblint_CLI.State_Report_GraphViz.full_state_checked_export_auto k prog
        in
        let graphs = List.map (fun k -> (analysis_label k, graph_for k)) !analyses in
        (* The source view's inline annotations need a verdict *and* a
           position, and only the parser knows positions -- it notes each
           __voblint_check token as it consumes one, in the same order this
           report lists them. Unreachable checks are dropped, matching what
           the text report does with those rows. *)
        let checks =
          match Voblint_CLI.Analyse_Dispatch.analyse_config_with_state cfg prog with
          | None -> []
          | Some report ->
            List.filter_map
              (fun ((_, (cond, (verdict, (unreachable, _)))), (line, column)) ->
                 if unreachable then None
                 else
                   Some
                     { Html_report.line;
                       column;
                       verdict = verdict_label verdict;
                       cond =
                         un_string
                           (Voblint_CLI.Core.string_of_exp
                              (Voblint_CLI.Core.nat_of_integer Z.zero) cond) })
              (List.combine report check_positions)
        in
        let files, nodes, dead =
          Html_report.emit ~graphs ~source_file:(Filename.basename path) ~source_text:src
            ~fn:"main" ~checks
        in
        List.iter (fun (f : Html_report.file) -> write_report_file dir f) files;
        Ok_report
          (Printf.sprintf "%d node(s), %d unreachable\n" nodes dead)
      else if !graph_snapshot && !dot_full then
        Ok_graph
          (if !context_kind = CK_CallString then
             Voblint_CLI.State_Report_GraphViz.cs_ctx_graph_snapshot_auto kind (cs_depth ()) prog
           else if !context_graph = Expanded then
             Voblint_CLI.State_Report_GraphViz.entry_state_ctx_graph_snapshot_auto prog
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Voblint_CLI.State_Report_GraphViz.entry_state_full_state_graph_snapshot_auto kind prog
           else Voblint_CLI.State_Report_GraphViz.full_state_graph_snapshot_auto kind prog)
      else if !graph_snapshot then
        Ok_graph
          (if !context_kind = CK_CallString then
             Voblint_CLI.State_Report_GraphViz.cs_ctx_graph_snapshot_auto kind (cs_depth ()) prog
           else if !context_graph = Expanded then
             Voblint_CLI.State_Report_GraphViz.entry_state_ctx_graph_snapshot_auto prog
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Voblint_CLI.State_Report_GraphViz.entry_state_report_graph_snapshot_auto kind prog
           else Voblint_CLI.State_Report_GraphViz.state_report_graph_snapshot_auto kind prog)
      else if !dot_full then
        Ok_dot
          (if !context_kind = CK_CallString then
             Dot_render.render
               (Voblint_CLI.State_Report_GraphViz.cs_ctx_export_auto kind (cs_depth ()) prog)
           else if !context_graph = Expanded then
             Dot_render.render
               (Voblint_CLI.State_Report_GraphViz.entry_state_ctx_export_auto prog)
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Dot_render.render
               (Voblint_CLI.State_Report_GraphViz.entry_state_full_state_export_auto kind prog)
           else Dot_render.render (Voblint_CLI.State_Report_GraphViz.full_state_export_auto kind prog))
      else if !dot then
        Ok_dot
          (if !context_kind = CK_CallString then
             Dot_render.render
               (Voblint_CLI.State_Report_GraphViz.cs_ctx_export_auto kind (cs_depth ()) prog)
           else if !context_graph = Expanded then
             Dot_render.render
               (Voblint_CLI.State_Report_GraphViz.entry_state_ctx_export_auto prog)
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Dot_render.render
               (Voblint_CLI.State_Report_GraphViz.entry_state_report_export_auto kind prog)
           else Dot_render.render (Voblint_CLI.State_Report_GraphViz.state_report_export_auto kind prog))
      else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
        (match Voblint_CLI.Analyse_Dispatch.analyse_config_ctx cfg prog with
         | Some report -> Ok_text (render_ctx_report report check_positions)
         | None -> Unsupported_combo "unsupported --analysis/--context combination")
      else if !solver <> None then
        (match Voblint_CLI.Analyse_Dispatch.analyse_config cfg prog with
         | Some report -> Ok_text (render_flat_report report check_positions)
         | None -> Unsupported_combo "unsupported --analysis/--solver combination")
      else
        (match Voblint_CLI.Analyse_Dispatch.analyse_config_with_state cfg prog with
         | Some report -> Ok_text (render_text_report report check_positions)
         | None -> Unsupported_combo "unsupported --analysis combination"))
  with
  | Ok (Ok_text s) -> print_string s
  | Ok (Ok_dot s) -> print_string s
  | Ok (Ok_graph s) -> print_string s
  | Ok (Ok_report s) ->
    (* Post-processing runs here, not in the contained child: the analysis is
       what needs a timeout, and a killed child should not take the asset copy
       and the graphviz call down with it. *)
    let dir = !html_dir in
    (match frontend_dir () with
     | None ->
       prerr_endline
         "voblint: frontend assets not found -- run: git submodule update --init vendor/g2html";
       exit 5
     | Some assets ->
       Array.iter
         (fun name ->
            let src = Filename.concat assets name in
            if not (Sys.is_directory src) then copy_file src (Filename.concat dir name))
         (Sys.readdir assets));
    let seg = Html_report.xmlify (Filename.basename path) in
    let dot_file = Filename.concat dir (Filename.concat "dot" (Filename.concat seg "main.dot")) in
    let svg_dir = Filename.concat dir (Filename.concat "cfgs" seg) in
    mkdir_p svg_dir;
    let svg_file = Filename.concat svg_dir "main.svg" in
    let cmd = Filename.quote_command "dot" [ "-Tsvg"; dot_file; "-o"; svg_file ] in
    (* Without a working graphviz the report still carries every node document;
       only the graph pane is empty. Say so and carry on rather than fail. *)
    (match Unix.system (cmd ^ " 2>/dev/null") with
     | Unix.WEXITED 0 -> ()
     | _ ->
       prerr_endline
         "voblint: `dot -Tsvg` failed or is missing -- wrote dot/ but no cfgs/*.svg, \
          so the CFG pane will be empty");
    print_string s;
    (* The entry point is index.xml, not an .html file, and it renders only when
       served: browsers refuse to apply its stylesheet over file://. Saying so
       here is cheaper than the reader concluding nothing was written. *)
    Printf.printf
      "wrote %s/\n\
       The entry point is %s/index.xml -- an .html file to open directly does not\n\
       exist, and file:// will not render it. Serve the directory first:\n\
      \  python3 -m http.server --directory %s 8080\n\
       then open http://localhost:8080/index.xml (or use `pixi run report`,\n\
       which serves and opens it for you).\n"
      dir dir dir
  | Ok (Unsupported_combo msg) -> prerr_endline ("voblint: " ^ msg); exit 1
  | Error msg -> Printf.eprintf "voblint: %s\n" msg; exit 3
