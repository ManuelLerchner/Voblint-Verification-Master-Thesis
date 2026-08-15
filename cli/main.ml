(* voblint: a thin CLI over the Isabelle-generated, proved-sound analyzer.

   source text (unverified adapter)
       -> Vimp_lexer/Vimp_parser (this directory, generated from
          grammar/vimp.yaml by scripts/gen_vimp_menhir.py -- ocamllex +
          Menhir, NOT verified) via Vimp_frontend (hand-written glue)
       -> imp_prog
       -> Voblint_CLI.Analyse.analyse_with_state (Isabelle-generated)
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
  "voblint --analysis sign|interval [--context none|entry-state] [--dot] \
   [--timeout SECONDS] FILE.vimp\n\
   voblint --parse-only FILE.vimp\n\n\
   Options:\n\
  \  --analysis sign|interval   Abstract domain to run (required, unless\n\
  \                             --parse-only).\n\
  \  --context none|entry-state Context sensitivity (default: none, today's\n\
  \                             flow-insensitive, call-site-insensitive\n\
  \                             behaviour). entry-state re-analyzes each\n\
  \                             callee per distinct entered-argument context,\n\
  \                             including under --dot/--dot-full/\n\
  \                             --graph-snapshot (a node covered by several\n\
  \                             contexts renders their joined state); only\n\
  \                             --analysis interval supports it -- any other\n\
  \                             combination is a clear configuration error,\n\
  \                             not a silent fallback to --context none.\n\
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

(* A pointwise abstract state's concretisation is the conjunction of every
   variable's own concretisation: it is empty iff SOME variable's is, not
   only when one particular fixed variable's is (Sign and Interval are both
   non-relational). Probing every variable in program_vars -- rather than
   one fixed name -- is therefore an exact reachability test for these
   domains, not just a sound-but-incomplete heuristic: see
   is_bottom_abstract_value's doc comment in Example_State_Report_GraphViz.thy.
   Unreachable entries are suppressed entirely, matching Goblint's
   "__goblint_check(0); // NOWARN (unreachable)" convention (no output at
   that location), rather than shown with a vacuous PROVED verdict. *)
let is_unreachable vars_to_probe (f : string -> Voblint_CLI.Analyse.abstract_value) =
  List.exists
    (fun x -> Voblint_CLI.Example_State_Report_GraphViz.is_bottom_abstract_value (f x))
    vars_to_probe

let render_text_report ~vars_to_probe (report :
      (Voblint_CLI.Core.cfg_node
       * (Voblint_CLI.Core.bexp
          * (Voblint_CLI.Core.check_result * (string -> Voblint_CLI.Analyse.abstract_value))))
      list)
    (check_positions : (int * int) list) =
  let buf = Buffer.create 256 in
  (* report and check_positions are both in check-declaration order, one
     entry per __voblint_check the parser saw -- see Vimp_frontend.program's
     doc comment. A length mismatch would mean that invariant broke, so let
     it raise rather than silently misalign. *)
  List.iter2
    (fun (node, (cond, (verdict, f))) (line, col) ->
       if not (is_unreachable vars_to_probe f) then begin
         let vars = Voblint_CLI.Example_State_Report_GraphViz.bexp_vnames_list cond in
         let state =
           vars
           |> List.map (fun x ->
             x ^ "=" ^ un_string (Voblint_CLI.Example_State_Report_GraphViz.string_of_abstract_value (f x)))
           |> String.concat ", "
         in
         Buffer.add_string buf
           (Printf.sprintf "%d:%-2d %-10s %-20s %-8s %s\n" line col (node_label node)
              (un_string (Voblint_CLI.Core.string_of_bexp cond))
              (verdict_label verdict) state)
       end)
    report check_positions;
  Buffer.contents buf

(* analyse_ctx's check_report_entry list carries no per-variable state
   projection (unlike analyse_with_state's report), so there is no
   is_unreachable dead-code filter or per-variable state column here --
   only the check verdict itself. *)
let render_flat_report
    (report :
      (Voblint_CLI.Core.cfg_node * (Voblint_CLI.Core.bexp * Voblint_CLI.Core.check_result)) list)
    (check_positions : (int * int) list) =
  let buf = Buffer.create 256 in
  List.iter2
    (fun (node, (cond, verdict)) (line, col) ->
       Buffer.add_string buf
         (Printf.sprintf "%d:%-2d %-10s %-20s %-8s\n" line col (node_label node)
            (un_string (Voblint_CLI.Core.string_of_bexp cond))
            (verdict_label verdict)))
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

let () =
  let analysis = ref None in
  let context = ref Voblint_CLI.Analyse.Ctx_None in
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
       | "sign" -> analysis := Some Voblint_CLI.Analyse.Sign_Analysis
       | "interval" -> analysis := Some Voblint_CLI.Analyse.Interval_Analysis
       | _ -> prerr_endline ("unknown --analysis value: " ^ v); exit 1);
      parse_args rest
    | "--context" :: v :: rest ->
      (match v with
       | "none" -> context := Voblint_CLI.Analyse.Ctx_None
       | "entry-state" -> context := Voblint_CLI.Analyse.Ctx_EntryState
       | _ -> prerr_endline ("unknown --context value: " ^ v); exit 1);
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
  (* entry_state_{full_state,report}_{dot,graph_snapshot}_auto take no
     analysis_kind: they are Interval-only by construction, the same
     restriction analyse_ctx encodes for the text-report path (Ctx_EntryState
     has no Sign branch). Checked once, up front, for every mode -- not just
     the text path -- so an unsupported combination is a clear, static error
     before the timeout-guarded analysis runs, never a silent Interval
     substitution for a requested Sign report. *)
  if !context <> Voblint_CLI.Analyse.Ctx_None && kind <> Voblint_CLI.Analyse.Interval_Analysis then begin
    prerr_endline "voblint: unsupported --analysis/--context combination";
    exit 1
  end;
  let vars_to_probe = Voblint_CLI.Example_State_Report_GraphViz.program_vars prog in
  match
    run_contained ~timeout:!timeout (fun () ->
      if !graph_snapshot && !dot_full then
        Ok_graph
          (if !context <> Voblint_CLI.Analyse.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_full_state_graph_snapshot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.full_state_graph_snapshot_auto kind prog)
      else if !graph_snapshot then
        Ok_graph
          (if !context <> Voblint_CLI.Analyse.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_report_graph_snapshot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.state_report_graph_snapshot_auto kind prog)
      else if !dot_full then
        Ok_dot
          (if !context <> Voblint_CLI.Analyse.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_full_state_dot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.full_state_dot_auto kind prog)
      else if !dot then
        Ok_dot
          (if !context <> Voblint_CLI.Analyse.Ctx_None then
             Voblint_CLI.Example_State_Report_GraphViz.entry_state_report_dot_auto prog
           else Voblint_CLI.Example_State_Report_GraphViz.state_report_dot_auto kind prog)
      else if !context <> Voblint_CLI.Analyse.Ctx_None then
        (match Voblint_CLI.Analyse.analyse_ctx kind !context prog with
         | Some report -> Ok_text (render_flat_report report check_positions)
         | None -> Unsupported_combo "unsupported --analysis/--context combination")
      else
        Ok_text
          (render_text_report ~vars_to_probe
             (Voblint_CLI.Analyse.analyse_with_state kind prog)
             check_positions))
  with
  | Ok (Ok_text s) -> print_string s
  | Ok (Ok_dot s) -> print_string s
  | Ok (Ok_graph s) -> print_string s
  | Ok (Unsupported_combo msg) -> prerr_endline ("voblint: " ^ msg); exit 1
  | Error msg -> Printf.eprintf "voblint: %s\n" msg; exit 3
