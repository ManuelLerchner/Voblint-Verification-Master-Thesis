(* voblint: a thin CLI over the Isabelle-generated, proved-sound analyzer.

   source text (unverified adapter)
       -> Vimp_lexer/Vimp_parser (this directory, generated from
          grammar/vimp.yaml by scripts/gen_vimp_menhir.py -- ocamllex +
          Menhir, NOT verified) via Vimp_frontend (hand-written glue)
       -> imp_prog
       -> Voblint_CLI.Analysis_Config.mk_analysis_config (one config value)
       -> Voblint_CLI.Analyse.analyse_config/analyse_config_ctx/
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
  "voblint --analysis sign|interval|int [--context none|entry-state|call-string] \
   [--context-depth K] [--context-graph collapsed|expanded] [--dot] \
   [--timeout SECONDS] FILE.vimp\n\
   voblint --parse-only FILE.vimp\n\n\
   Options:\n\
  \  --analysis sign|interval|int\n\
  \                             Abstract domain to run (required, unless\n\
  \                             --parse-only). int is the refining composite\n\
  \                             Sign x Interval x Parity x Congruence domain,\n\
  \                             fixed at its most precise refinement mode\n\
  \                             (Refine_Fixpoint) and the warrowing solver; it\n\
  \                             has no --context or --solver support yet.\n\
  \  --context none|entry-state|call-string\n\
  \                             Context sensitivity (default: none, today's\n\
  \                             flow-insensitive, call-site-insensitive\n\
  \                             behaviour). entry-state re-analyzes each\n\
  \                             callee per distinct entered-argument context,\n\
  \                             including under --dot/--dot-full/\n\
  \                             --graph-snapshot (a node covered by several\n\
  \                             contexts renders their joined state under\n\
  \                             --context-graph collapsed, the default); only\n\
  \                             --analysis interval supports it. call-string\n\
  \                             re-analyzes each callee per distinct bounded\n\
  \                             call history (requires --context-depth K,\n\
  \                             K >= 1); --analysis interval only, plain text\n\
  \                             report only for now (no --dot/--dot-full/\n\
  \                             --graph-snapshot support yet). Any other\n\
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
  \                             How --dot/--dot-full/--graph-snapshot render\n\
  \                             --context entry-state (default: collapsed, one\n\
  \                             node per program point with its contexts\n\
  \                             joined). expanded instead draws one node per\n\
  \                             (point, context) pair, annotated through the\n\
  \                             same solved AnalysisResult with no join, so a\n\
  \                             point dead in one activation and live in\n\
  \                             another renders as two distinct nodes rather\n\
  \                             than one live-looking join. Requires --context\n\
  \                             entry-state -- expanded with --context none is\n\
  \                             a clear configuration error, not a silent\n\
  \                             fallback to collapsed.\n\
  \  --solver join|per-origin|warrow\n\
  \                             Pick the vendored solver's update-rule\n\
  \                             discipline directly, bypassing the domain's\n\
  \                             production default (experimental; issue\n\
  \                             #131). warrow only type-checks against\n\
  \                             interval (sign has no widen instance).\n\
  \                             Plain text report only -- incompatible with\n\
  \                             --context/--dot/--dot-full/--graph-snapshot.\n\
  \  --dot                      Emit a GraphViz .dot rendering of the solved CFG,\n\
  \                             annotated at check nodes only, instead of the\n\
  \                             textual check report.\n\
  \  --dot-full                 Like --dot, but every node is annotated with its\n\
  \                             own computed abstract state, not just check nodes.\n\
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
             * (bool * (string -> Voblint_CLI.Analyse.abstract_value)))))
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
         let vars = Voblint_CLI.Example_State_Report_GraphViz.exp_vnames_list cond in
         let state =
           vars
           |> List.map (fun x ->
             x ^ "=" ^ un_string (Voblint_CLI.Example_State_Report_GraphViz.string_of_abstract_value (f x)))
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

type outcome = Ok_text of string | Ok_dot of string | Ok_graph of string | Unsupported_combo of string

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
                 | "U" -> Ok (Unsupported_combo body)
                 | _ -> Error body)
              | None -> Error "analysis subprocess produced no output")
           | _, Unix.WEXITED code -> Error (Printf.sprintf "analysis subprocess exited with code %d" code)
           | _, (Unix.WSIGNALED s | Unix.WSTOPPED s) ->
             Error (Printf.sprintf "analysis subprocess terminated by signal %d" s)
         in
         wait_loop ())

type context_graph_mode = Collapsed | Expanded

(* --context/--context-depth are two independent flags that can arrive in
   either order, but Ctx_CallString needs the depth at construction time --
   so parsing collects an intermediate tag + optional depth, and the final
   immutable Analysis_Config.context_mode value is assembled once, after
   parse_args returns, from both together. *)
type context_kind = CK_None | CK_EntryState | CK_CallString

let () =
  let analysis = ref None in
  let context_kind = ref CK_None in
  let context_depth = ref None in
  let context_graph = ref Collapsed in
  let solver = ref None in
  let dot = ref false in
  let dot_full = ref false in
  let graph_snapshot = ref false in
  let parse_only = ref false in
  let timeout = ref 10.0 in
  let file = ref None in
  let rec parse_args = function
    | [] -> ()
    | "--help" :: _ -> print_endline usage; exit 0
    | "--analysis" :: v :: rest ->
      (match v with
       | "sign" -> analysis := Some Voblint_CLI.Analysis_Config.Sign_Analysis
       | "interval" -> analysis := Some Voblint_CLI.Analysis_Config.Interval_Analysis
       | "int" -> analysis := Some Voblint_CLI.Analysis_Config.Int_Analysis
       | _ -> prerr_endline ("unknown --analysis value: " ^ v); exit 1);
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
       | "collapsed" -> context_graph := Collapsed
       | "expanded" -> context_graph := Expanded
       | _ -> prerr_endline ("unknown --context-graph value: " ^ v); exit 1);
      parse_args rest
    | "--solver" :: v :: rest ->
      (match v with
       | "join" -> solver := Some Voblint_CLI.Analysis_Config.Solver_Join
       | "per-origin" -> solver := Some Voblint_CLI.Analysis_Config.Solver_PerOrigin
       | "warrow" -> solver := Some Voblint_CLI.Analysis_Config.Solver_Warrow
       | _ -> prerr_endline ("unknown --solver value: " ^ v); exit 1);
      parse_args rest
    | "--dot" :: rest -> dot := true; parse_args rest
    | "--dot-full" :: rest -> dot_full := true; parse_args rest
    | "--graph-snapshot" :: rest -> graph_snapshot := true; parse_args rest
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
     a second, hand-maintained OCaml compatibility table. This subsumes what
     used to be two separate checks here -- Sign/Int have no entry-state
     branch, and an explicit --solver is unconditionally incompatible with
     any --context other than none, even --solver warrow under
     --context entry-state, which happens to name the same solver
     entry-state analysis already uses internally. *)
  let cfg = Voblint_CLI.Analysis_Config.mk_analysis_config kind !solver !context in
  if not (Voblint_CLI.Analysis_Config.valid_analysis_config cfg) then begin
    prerr_endline "voblint: unsupported --analysis/--context/--solver combination";
    exit 1
  end;
  (* --dot/--dot-full/--graph-snapshot for --context call-string would
     otherwise silently fall through to the entry-state-specific renderers
     below (the only ones a non-Ctx_None context currently routes to),
     rendering EntryState's own result table regardless of what --context
     actually selected. GraphViz support for call-string is real future
     work, not something to approximate by reusing an unrelated renderer;
     reject explicitly rather than emit a plausible-looking wrong graph. *)
  if !context_kind = CK_CallString && (!dot || !dot_full || !graph_snapshot) then begin
    prerr_endline
      "voblint: --context call-string does not support --dot/--dot-full/--graph-snapshot yet";
    exit 1
  end;
  (* expanded is meaningless without a context to expand -- reject rather than
     silently rendering the collapsed graph a bare --context-graph expanded
     might otherwise appear to have requested. *)
  if !context_graph = Expanded && !context = Voblint_CLI.Analysis_Config.Ctx_None then begin
    prerr_endline "voblint: --context-graph expanded requires --context entry-state";
    exit 1
  end;
  (* --solver's flat check_report_entry list has no per-node state map to
     render, and entry_state_{full_state,report}_{dot,graph_snapshot}_auto
     are Interval-only regardless of --solver -- this compatibility is about
     report *shape* versus presentation, not analysis semantics, so it stays
     a CLI-level check rather than moving into analysis_config's scope. *)
  if !solver <> None && (!dot || !dot_full || !graph_snapshot) then begin
    prerr_endline "voblint: --solver only supports the plain text report";
    exit 1
  end;
  match
    run_contained ~timeout:!timeout (fun () ->
      if !graph_snapshot && !dot_full then
        Ok_graph
          (if !context_graph = Expanded then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_ctx_graph_snapshot_auto prog
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_full_state_graph_snapshot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.full_state_graph_snapshot_auto kind prog)
      else if !graph_snapshot then
        Ok_graph
          (if !context_graph = Expanded then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_ctx_graph_snapshot_auto prog
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_report_graph_snapshot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.state_report_graph_snapshot_auto kind prog)
      else if !dot_full then
        Ok_dot
          (if !context_graph = Expanded then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_ctx_dot_auto prog
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_full_state_dot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.full_state_dot_auto kind prog)
      else if !dot then
        Ok_dot
          (if !context_graph = Expanded then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_ctx_dot_auto prog
           else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_report_dot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.state_report_dot_auto kind prog)
      else if !context <> Voblint_CLI.Analysis_Config.Ctx_None then
        (match Voblint_CLI.Analyse.analyse_config_ctx cfg prog with
         | Some report -> Ok_text (render_ctx_report report check_positions)
         | None -> Unsupported_combo "unsupported --analysis/--context combination")
      else if !solver <> None then
        (match Voblint_CLI.Analyse.analyse_config cfg prog with
         | Some report -> Ok_text (render_flat_report report check_positions)
         | None -> Unsupported_combo "unsupported --analysis/--solver combination")
      else
        (match Voblint_CLI.Analyse.analyse_config_with_state cfg prog with
         | Some report -> Ok_text (render_text_report report check_positions)
         | None -> Unsupported_combo "unsupported --analysis combination"))
  with
  | Ok (Ok_text s) -> print_string s
  | Ok (Ok_dot s) -> print_string s
  | Ok (Ok_graph s) -> print_string s
  | Ok (Unsupported_combo msg) -> prerr_endline ("voblint: " ^ msg); exit 1
  | Error msg -> Printf.eprintf "voblint: %s\n" msg; exit 3
