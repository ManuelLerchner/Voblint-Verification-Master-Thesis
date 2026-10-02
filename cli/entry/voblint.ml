(* voblint: a thin CLI over the Isabelle-generated, proved-sound analyzer.

   source text (unverified adapter)
       -> Vimp_lexer/Vimp_parser (this directory, generated from
          manifests/vimp-grammar.yaml by scripts/gen_vimp_menhir.py -- ocamllex +
          Menhir, NOT verified) via Vimp_frontend (hand-written glue)
       -> imp_prog
       -> Voblint_CLI.Generated.run_voblint (Analysis_Config (domains, globals, context))
          (Isabelle-generated). One call checks the program is well-formed and
          runs the analyses the activation list, global update rule and context name;
          every combination is answered. What comes back is data -- states per point and
          context, the routes calls take, the check column, diagnostics -- with
          every abstract value already rendered by its own domain. Every
          rendering below (text report, graph, snapshot, HTML) is built from that
          one result, so none can draw from a different solve than another.
       -> proved analysis results, subject to the Isabelle theorem
          assumptions (solver termination and check reachability -- see
          Analysis_Certified.thy)

   Trust boundary: soundness applies to the imp_prog the parser produces, not
   to the claim that this imp_prog faithfully represents the text file the
   user wrote. The parser is unverified, the same way Goblint's own C
   frontend is unverified -- parsing was never in the soundness scope of
   either project. A parser bug can change *which* program gets analyzed; it
   cannot invalidate the analyzer's soundness theorem for the AST actually
   produced. See docs/CLI_DESIGN.md. *)

let usage =
  "voblint --analysis sign|interval|int|parity|congruence|order [--context \
   none|entry-state|call-string] [--context-depth K] [--globals \
   join|per-origin|warrow|warrow-per-origin|bounded-narrowing] [--narrow-bound \
   N] [--int-refinement never|once|fixpoint] [--dot] [--timeout SECONDS]\n\
  \  [--trace] [--verbose|--compact] [--trace-sys SYS[,...]] [--format \
   text|jsonl]\n\
  \  [--output FILE]\n\
  \  FILE.vimp\n\
   voblint --parse-only FILE.vimp\n\
   voblint --ast FILE.vimp\n\n\
   Options:\n\
  \  --analysis sign|interval|int|parity|congruence|order[,...]\n\
  \                             Abstract domain to run (required, unless\n\
  \                             --parse-only). int is the refining composite\n\
  \                             Sign x Interval x Parity x Congruence domain,\n\
  \                             whose components refine each other as\n\
  \                             --int-refinement selects.\n\
  \                             parity is the four-element Bot/Even/Odd/Top\n\
  \                             lattice; it decides equalities only by\n\
  \                             refuting them across differing parities.\n\
  \                             congruence is the residue-class domain, one\n\
  \                             value constrained to x = r (mod m); m = 0\n\
  \                             pins a single integer and m = 1 constrains\n\
  \                             nothing. It decides no orderings and decides\n\
  \                             equalities only between singletons.\n\
  \                             order is relational: it records which\n\
  \                             variables are ordered by <= and answers\n\
  \                             comparisons between them to the other\n\
  \                             analyses of a comma list.\n\
  \                             A comma list (e.g. interval,parity) runs the\n\
  \                             named domains together in one solve: a state\n\
  \                             shows each domain's part on its own, a\n\
  \                             point any of them proves unreachable is\n\
  \                             unreachable, and a check is decided by the\n\
  \                             meet of their answers. Naming a domain twice\n\
  \                             is rejected.\n\
  \  --context none|entry-state|call-string\n\
  \                             Context sensitivity (default: none, one\n\
  \                             context per callee regardless of call\n\
  \                             site). entry-state re-analyzes each\n\
  \                             callee per distinct entered-argument context,\n\
  \                             including under --dot/--graph-snapshot,\n\
  \                             which always draw the\n\
  \                             covered contexts separately.\n\
  \                             call-string re-analyzes each callee per\n\
  \                             distinct bounded call history (requires\n\
  \                             --context-depth K). Every domain serves\n\
  \                             every context mode at every --globals rule.\n\
  \  --context-depth K          Call-string bound (only valid with --context\n\
  \                             call-string). K = 0 keeps no call site, so\n\
  \                             every callee shares one context.\n\
  \  --globals join|per-origin|warrow|warrow-per-origin|bounded-narrowing\n\
  \                             How the solver merges a value side-effected\n\
  \                             into a global: joined, joined per origin,\n\
  \                             warrowed, warrowed per origin, or widened per\n\
  \                             origin with narrowing bounded by\n\
  \                             --narrow-bound (default: warrow). Locals\n\
  \                             are warrowed at loop heads under every rule.\n\
  \  --narrow-bound N           bounded-narrowing narrows an origin once each\n\
  \                             time it switches from widening to narrowing,\n\
  \                             and keeps narrowing only while it has\n\
  \                             switched fewer than N times (default: 5, the\n\
  \                             default of Goblint's narrow-gas option). Only\n\
  \                             valid with --globals bounded-narrowing.\n\
  \  --int-refinement never|once|fixpoint\n\
  \                             How the components of int teach each other\n\
  \                             after every operation: not at all, one round,\n\
  \                             or rounds until nothing changes (default:\n\
  \                             fixpoint). Only valid with --analysis int.\n\
  \  --dot                      Emit the canonical contextual GraphViz .dot CFG\n\
  \                             instead of the textual check report. Every local\n\
  \                             node carries its own context state and checks.\n\
  \  --html                     Write a browsable HTML result directory \
   (default:\n\
  \                             build/report/)\n\
  \                             (abstract states live in per-node documents, so\n\
  \                             the CFG stays readable where --dot does\n\
  \                             not). Needs `dot` on PATH for the graph pane,\n\
  \                             and the vendor/g2html submodule for the\n\
  \                             frontend. Serve it and open index.xml:\n\
  \                               python3 -m http.server --directory \
   build/report 8080\n\
  \  --html-out DIR             Write that directory to DIR instead. Implies\n\
  \                             --html.\n\
  \  --json                     Print the result as the browser adapter receives\n\
  \                             it (analysis time reported as 0).\n\
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
  \                             0 here: well-formedness is checked only on a\n\
  \                             full run, which rejects it with exit 4.\n\
  \  --ast                      Print the parsed program as JSON (globals,\n\
  \                             main's body, procedure table), the imp_prog\n\
  \                             value the browser page passes to the analyzer,\n\
  \                             and exit. Like --parse-only, runs no analysis.\n\
  \  --timeout SECONDS          Wall-clock budget for the analysis subprocess\n\
  \                             (default 10). The analyzer is proved sound but\n\
  \                             not proved total (see CLI_DESIGN.md's Interval\n\
  \                             containment note), so it runs in a killable\n\
  \                             child process rather than in-process.\n\
  \  --trace                    Also write a trace of the solver's steps to\n\
  \                             stderr (or --output FILE). Standard output is\n\
  \                             unchanged. The trace is written once the\n\
  \                             solve finishes; a killed run leaves none.\n\
  \  --compact                  Trace per call: routing, the result query,\n\
  \                             seed reads, flushed publications, restarts\n\
  \                             and returns (default).\n\
  \  --verbose                  Trace every solver step, one line per step\n\
  \                             in a Goblint-aligned tracing vocabulary\n\
  \                             ('%%% iter: begin iterate ...').\n\
  \  --trace-sys SYS[,...]      Print only these subsystems of the verbose\n\
  \                             trace, as Goblint's --trace SYS selects them:\n\
  \                             multivar, solver_query, wpoint, iter, infl,\n\
  \                             answer, eq, sol, update, side, destab, and\n\
  \                             Voblint's own rhs and route. Repeatable;\n\
  \                             implies --trace --verbose.\n\
  \  --format text|jsonl        Trace as text (default) or JSON Lines.\n\
  \  --output FILE              Write the trace to FILE instead of stderr.\n\
  \                             Each of --compact, --verbose, --trace-sys,\n\
  \                             --format and --output implies --trace.\n\
  \  --help                     Show this message.\n\n\
   Trust boundary: results are sound for the program this file's unverified\n\
  \  parser actually built, not a guarantee that the parser read your source\n\
  \  correctly. The analyzer core (parsing excluded) is generated from a\n\
  \  machine-checked Isabelle/HOL proof."

module C = Voblint_CLI.Generated
module A = Result_text

let print_diagnostics path analysis positions diagnostics =
  List.iter
    (fun diagnostic ->
      let location =
        match Render_text.diagnostic_location positions diagnostic with
        | Some (line, column) -> Printf.sprintf "%d:%d" line column
        | None -> A.point_name (C.diagnostic_point diagnostic)
      in
      Printf.eprintf "%s:%s: %s: %s [%s]\n" path location
        (Render_text.diagnostic_severity diagnostic)
        (Result_text.diagnostic_message diagnostic)
        analysis)
    diagnostics

let rec mkdir_p dir =
  if dir <> "" && dir <> "/" && dir <> "." && not (Sys.file_exists dir) then begin
    mkdir_p (Filename.dirname dir);
    try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let rec rm_rf path =
  match Sys.is_directory path with
  | true -> (
      Array.iter (fun n -> rm_rf (Filename.concat path n)) (Sys.readdir path);
      try Unix.rmdir path with Unix.Unix_error _ -> ())
  | false -> ( try Sys.remove path with Sys_error _ -> ())
  | exception Sys_error _ -> ()

let frontend_dir () =
  match Sys.getenv_opt "VOBLINT_FRONTEND" with
  | Some d -> Some d
  | None ->
      let candidate =
        Filename.concat
          (Filename.dirname (Filename.dirname Sys.executable_name))
          (Filename.concat "vendor" (Filename.concat "g2html" "resources"))
      in
      if Sys.file_exists candidate && Sys.is_directory candidate then
        Some candidate
      else None

(* The entries --html owns, and so is free to replace on every run. *)
let owned_entries = [ "nodes"; "files"; "dot"; "cfgs"; "warn"; "index.xml" ]

let rec has_regular_file path =
  match Sys.is_directory path with
  | true ->
      Array.exists
        (fun n -> has_regular_file (Filename.concat path n))
        (Sys.readdir path)
  | false -> true
  | exception Sys_error _ -> false

(* The only thing refused is a directory holding a regular file this emitter
   does not write: that is someone else's data, and the report would be
   interleaved with it. Empty directories and old voblint output are never a
   reason to refuse. Read-only, and run before the analysis, so an unusable
   --html-out is reported as the argument error it is rather than after a
   solve. *)
let check_report_dir dir =
  if not (Sys.file_exists dir) then ()
  else if not (Sys.is_directory dir) then begin
    Printf.eprintf "voblint: %s exists and is not a directory\n" dir;
    exit 5
  end
  else begin
    let assets =
      match frontend_dir () with
      | Some d -> Array.to_list (Sys.readdir d)
      | None -> []
    in
    let owned n = List.mem n owned_entries || List.mem n assets in
    match
      List.filter
        (fun n -> (not (owned n)) && has_regular_file (Filename.concat dir n))
        (Array.to_list (Sys.readdir dir))
    with
    | [] -> ()
    | n :: _ ->
        Printf.eprintf
          "voblint: refusing to write a report into %s: it holds %s, which is \
           not voblint output\n"
          dir n;
        exit 5
  end

(* Every run rewrites the report entries and the copied frontend assets, so
   stale node documents from a previous program (or the leftovers of a run
   that died halfway) never survive into the next report. Clearing waits until
   the analysis has answered: a program the analyzer rejects leaves the report
   already there intact rather than emptying a directory it never refills. *)
let clear_report_dir dir =
  if not (Sys.file_exists dir) then mkdir_p dir
  else List.iter (fun n -> rm_rf (Filename.concat dir n)) owned_entries

let write_report_file root (f : Report_dir.file) =
  let path = Filename.concat root f.Report_dir.path in
  mkdir_p (Filename.dirname path);
  let oc = open_out path in
  output_string oc f.Report_dir.content;
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
type outcome =
  | Ok_text of string
  | Ok_dot of string
  | Ok_graph of string
  | Ok_report of string
  (* Both rejections are the analyzer's own answer, so they surface from inside
     the contained run rather than from a gate this file keeps. *)
  | Malformed
  | Invalid_activation

(* Raised where an answer other than a successful run arrives, so every
   rendering below can be written against the output it needs. *)
exception Answered of outcome

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
              | Ok_text s ->
                  output_string oc "T\n";
                  output_string oc s
              | Ok_dot s ->
                  output_string oc "D\n";
                  output_string oc s
              | Ok_graph s ->
                  output_string oc "G\n";
                  output_string oc s
              | Ok_report s ->
                  output_string oc "R\n";
                  output_string oc s
              | Malformed -> output_string oc "M\n"
              | Invalid_activation -> output_string oc "I\n");
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
          (* Back off from a short first sleep rather than polling at a flat
             50ms. An analysis that finishes in single-digit milliseconds used
             to wait out one whole 50ms tick, which was most of the CLI's wall
             clock on a small program and hid what the analysis itself cost. *)
          let rec wait_loop nap =
            match Unix.waitpid [ Unix.WNOHANG ] pid with
            | 0, _ ->
                if Unix.gettimeofday () > deadline then begin
                  (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
                  ignore (Unix.waitpid [] pid);
                  Error
                    (Printf.sprintf
                       "analysis did not finish within %.0fs (killed)" timeout)
                end
                else begin
                  ignore (Unix.select [] [] [] nap);
                  wait_loop (Float.min 0.05 (nap *. 2.))
                end
            | _, Unix.WEXITED 0 -> (
                let ic = open_in tmp in
                let n = in_channel_length ic in
                let contents = really_input_string ic n in
                close_in ic;
                match String.index_opt contents '\n' with
                | Some i -> (
                    let tag = String.sub contents 0 i in
                    let body =
                      String.sub contents (i + 1)
                        (String.length contents - i - 1)
                    in
                    match tag with
                    | "T" -> Ok (Ok_text body)
                    | "D" -> Ok (Ok_dot body)
                    | "G" -> Ok (Ok_graph body)
                    | "R" -> Ok (Ok_report body)
                    | "M" -> Ok Malformed
                    | "I" -> Ok Invalid_activation
                    | _ -> Error body)
                | None -> Error "analysis subprocess produced no output")
            | _, Unix.WEXITED code ->
                (* The child records its exception under an "E" tag before
                exiting non-zero; surface it instead of only the code. *)
                let detail =
                  try
                    let ic = open_in tmp in
                    let n = in_channel_length ic in
                    let contents = really_input_string ic n in
                    close_in ic;
                    match String.index_opt contents '\n' with
                    | Some i when String.sub contents 0 i = "E" ->
                        ": "
                        ^ String.sub contents (i + 1)
                            (String.length contents - i - 1)
                    | _ -> ""
                  with Sys_error _ | End_of_file -> ""
                in
                Error
                  (Printf.sprintf "analysis subprocess exited with code %d%s"
                     code detail)
            | _, (Unix.WSIGNALED s | Unix.WSTOPPED s) ->
                Error
                  (Printf.sprintf "analysis subprocess terminated by signal %d"
                     s)
          in
          wait_loop 0.0005)

let () =
  (* Every domain named by --analysis, in order, exactly as given: run_voblint
     alone decides whether the list is a valid activation. *)
  let analysis_names = ref None in
  let int_refinement = ref None in
  (* --context and --context-depth can arrive in either order, but a call
     string needs its depth at construction time, so the policy is assembled
     once every flag is read. *)
  let context_name = ref "none" in
  let context_depth = ref None in
  let globals = ref Voblint_CLI.Generated.Globals_Warrow in
  let narrow_bound = ref None in
  let dot = ref false in
  let graph_snapshot = ref false in
  let json = ref false in
  let html = ref false in
  (* Generated report output stays under build/; --html-out is the override.
     Taking no argument keeps `--html FILE.vimp` from reading the program as
     the output directory. *)
  let html_dir = ref "build/report" in
  let parse_only = ref false in
  let ast = ref false in
  let timeout = ref 10.0 in
  let trace = ref false in
  let trace_verbose = ref false in
  let trace_format = ref Solver_trace.Text in
  let trace_systems = ref [] in
  let trace_output = ref None in
  let globals_name = ref "warrow" in
  let file = ref None in
  let rec parse_args = function
    | [] -> ()
    | "--help" :: _ ->
        print_endline usage;
        exit 0
    | "--analysis" :: v :: rest ->
        analysis_names := Some (String.split_on_char ',' v);
        parse_args rest
    | "--int-refinement" :: v :: rest ->
        (match Analysis_request.refinement_of_name v with
        | Some mode -> int_refinement := Some mode
        | None ->
            prerr_endline ("unknown --int-refinement value: " ^ v);
            exit 1);
        parse_args rest
    | "--context" :: v :: rest ->
        (match Analysis_request.context_of_name v None with
        | Error Analysis_request.Unknown_context ->
            prerr_endline ("unknown --context value: " ^ v);
            exit 1
        | _ -> context_name := v);
        parse_args rest
    | "--context-depth" :: v :: rest ->
        (try context_depth := Some (int_of_string v)
         with _ ->
           prerr_endline ("--context-depth expects an integer: " ^ v);
           exit 1);
        parse_args rest
    | "--globals" :: v :: rest ->
        globals_name := v;
        (* The bound is filled in once every flag is read, so --narrow-bound
           may come before or after --globals. *)
        (match
           Analysis_request.globals_of_name
             ~narrow_bound:Analysis_request.default_narrow_bound v
         with
        | Some rule -> globals := rule
        | None ->
            prerr_endline ("unknown --globals value: " ^ v);
            exit 1);
        parse_args rest
    | "--narrow-bound" :: v :: rest ->
        (try narrow_bound := Some (int_of_string v)
         with _ ->
           prerr_endline ("--narrow-bound expects an integer: " ^ v);
           exit 1);
        parse_args rest
    | "--dot" :: rest ->
        dot := true;
        parse_args rest
    | "--graph-snapshot" :: rest ->
        graph_snapshot := true;
        parse_args rest
    | "--json" :: rest ->
        json := true;
        parse_args rest
    | "--html" :: rest ->
        html := true;
        parse_args rest
    | "--html-out" :: v :: rest ->
        html := true;
        html_dir := v;
        parse_args rest
    | [ "--html-out" ] ->
        prerr_endline "voblint: --html-out expects a directory";
        exit 1
    | "--parse-only" :: rest ->
        parse_only := true;
        parse_args rest
    | "--ast" :: rest ->
        ast := true;
        parse_args rest
    | "--trace" :: rest ->
        trace := true;
        parse_args rest
    | "--verbose" :: rest ->
        trace := true;
        trace_verbose := true;
        parse_args rest
    | "--compact" :: rest ->
        trace := true;
        trace_verbose := false;
        parse_args rest
    | "--trace-sys" :: v :: rest ->
        trace := true;
        trace_verbose := true;
        List.iter
          (fun s ->
            if not (List.mem s Solver_trace.subsystems) then begin
              prerr_endline
                ("unknown --trace-sys subsystem: " ^ s ^ " (known: "
                ^ String.concat ", " Solver_trace.subsystems
                ^ ")");
              exit 1
            end;
            trace_systems := s :: !trace_systems)
          (String.split_on_char ',' v);
        parse_args rest
    | "--format" :: v :: rest ->
        trace := true;
        (match v with
        | "text" -> trace_format := Solver_trace.Text
        | "jsonl" -> trace_format := Solver_trace.Jsonl
        | _ ->
            prerr_endline ("unknown --format value: " ^ v);
            exit 1);
        parse_args rest
    | "--output" :: v :: rest ->
        trace := true;
        trace_output := Some v;
        parse_args rest
    | "--timeout" :: v :: rest ->
        (try timeout := float_of_string v
         with _ ->
           prerr_endline "--timeout expects a number";
           exit 1);
        parse_args rest
    | f :: rest when String.length f > 0 && f.[0] <> '-' ->
        file := Some f;
        parse_args rest
    | arg :: _ ->
        prerr_endline ("unrecognized argument: " ^ arg);
        exit 1
  in
  parse_args (List.tl (Array.to_list Sys.argv));
  (* The refinement mode belongs to int, so it is resolved after every flag is
     read and rejected when no int analysis is named. Each mode is an analysis
     of its own in the generated carrier; all of them are int to the user. *)
  let analyses =
    let refinement =
      Option.value !int_refinement ~default:Analysis_request.default_refinement
    in
    let kind_of name =
      match Analysis_request.analysis_of_name ~refinement name with
      | Some analysis -> analysis
      | None ->
          prerr_endline ("unknown --analysis value: " ^ name);
          exit 1
    in
    Option.map (List.map kind_of) !analysis_names
  in
  (match (!int_refinement, !analysis_names) with
  | Some _, names when not (List.mem "int" (Option.value names ~default:[])) ->
      prerr_endline
        "voblint: --int-refinement is only valid with --analysis int";
      exit 1
  | _ -> ());
  (match (!globals_name, !narrow_bound) with
  | "bounded-narrowing", Some n when n < 0 ->
      prerr_endline "voblint: --narrow-bound must not be negative";
      exit 1
  | "bounded-narrowing", n ->
      globals :=
        Analysis_request.bounded_narrowing
          (Option.value n ~default:Analysis_request.default_narrow_bound)
  | _, Some _ ->
      prerr_endline
        "voblint: --narrow-bound is only valid with --globals bounded-narrowing";
      exit 1
  | _, None -> ());
  (* --context-depth is only meaningful paired with --context call-string, so
     a mismatch between the two flags is rejected here. *)
  let context =
    match Analysis_request.context_of_name !context_name !context_depth with
    | Ok context -> context
    | Error Analysis_request.Negative_depth ->
        prerr_endline "voblint: --context-depth must not be negative";
        exit 1
    | Error Analysis_request.Missing_depth ->
        prerr_endline
          "voblint: --context call-string requires --context-depth K";
        exit 1
    | Error
        (Analysis_request.Unexpected_depth | Analysis_request.Unknown_context)
      ->
        prerr_endline
          "voblint: --context-depth is only valid with --context call-string";
        exit 1
  in
  let path =
    match !file with
    | Some p -> p
    | None ->
        prerr_endline "missing FILE.vimp";
        prerr_endline usage;
        exit 1
  in
  let src =
    try
      let ic = open_in_bin path in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      s
    with Sys_error msg ->
      prerr_endline ("voblint: cannot read " ^ path ^ ": " ^ msg);
      exit 1
  in
  let prog, stmt_positions, header_positions =
    try Vimp_frontend.program path src
    with Vimp_frontend.Parse_error { file; line; col; msg } ->
      Printf.eprintf "%s:%d:%d: parse error: %s\n" file line col msg;
      exit 2
  in
  if !parse_only then exit 0;
  if !ast then begin
    print_endline (Render_json.program_json prog);
    exit 0
  end;
  let domains =
    match analyses with
    | Some ds -> ds
    | None ->
        prerr_endline
          "missing --analysis sign|interval|int|parity|congruence|order";
        prerr_endline usage;
        exit 1
  in
  (* --html writes a directory; the other renderings write one document to
     stdout. Asking for both is a contradiction about where output goes, not a
     combination to silently resolve. *)
  if !json then begin
    let answer =
      Analysis_request.analyse ~analyses:domains ~globals:!globals ~context prog
    in
    let raw =
      Render_json.run_voblint_json ~domains ~globals:!globals ~ctx:context prog
        answer
    in
    (match answer with
    | C.Analysed result ->
        print_endline
          (Render_json.result_json 0. prog ~stmt_positions ~header_positions
             ~raw result)
    | C.Invalid_Activation | C.Malformed_Program | C.No_Answer ->
        print_endline raw);
    exit 0
  end;
  if !html && (!dot || !graph_snapshot) then begin
    prerr_endline
      "voblint: --html cannot be combined with --dot/--graph-snapshot";
    exit 1
  end;
  let label = String.concat "," (List.map A.analysis_label domains) in
  Solver_trace_hook.enabled := !trace;
  (* Written by the contained child after the solve: the recorded events live
     in its memory, and a killed child has nothing complete to show. *)
  let emit_trace result =
    let write out =
      Solver_trace.emit ~out:(output_string out) ~format:!trace_format
        ~verbose:!trace_verbose ~systems:!trace_systems
        ~source:(src, stmt_positions)
        ~analyses:(List.map A.analysis_label domains)
        ~context:(Solver_trace.context_name context)
        ~globals:!globals_name ~program:path result;
      flush out
    in
    match !trace_output with
    | None -> write stderr
    | Some f ->
        let oc = open_out_bin f in
        Fun.protect ~finally:(fun () -> close_out oc) (fun () -> write oc)
  in
  let solve () =
    match
      Analysis_request.analyse ~analyses:domains ~globals:!globals ~context prog
    with
    | C.Invalid_Activation -> raise (Answered Invalid_activation)
    | C.Malformed_Program -> raise (Answered Malformed)
    | C.No_Answer -> failwith "voblint: the solver returned no answer"
    | C.Analysed result ->
        if !trace then emit_trace result;
        if !html || !dot || !graph_snapshot then
          print_diagnostics path label stmt_positions (C.res_diagnostics result);
        result
  in
  (* Checked here, not inside the contained child: a refusal to write into the
     given directory is an argument error the user should see as one, not as a
     subprocess exit code relayed through the analysis timeout wrapper. The
     directory is only emptied later, once the analysis has answered. *)
  if !html then check_report_dir !html_dir;
  match
    run_contained ~timeout:!timeout (fun () ->
        try
          if !html then (
            let dir = !html_dir in
            (* Everything a report browser reads back is one solve: the graph
             it draws, the states in its node documents, the check column
             beside the source and the solved globals all come off the same
             result, under the same view. *)
            let result = solve () in
            let graph = Context_graph.build prog result in
            let globals = A.global_sections result in
            (* The source view's inline annotations need a verdict and a
             position; each check row carries its position as its label.
             Unreachable checks are dropped, matching what the text report's
             DEAD label says without a verdict to show. *)
            let checks =
              List.filter_map
                (fun (check, (line, column)) ->
                  match C.check_verdict check with
                  | C.Bot -> None
                  | C.Lifted v ->
                      Some
                        {
                          Render_xml.line;
                          column;
                          verdict = A.verdict_name v;
                          cond = Vimp_printer.string_of_exp (C.check_exp check);
                          message = None;
                        })
                (Render_text.located_checks (C.res_checks result))
            in
            let diagnostics =
              List.map
                (fun diagnostic ->
                  let line, column =
                    Option.value ~default:(0, 0)
                      (Render_text.diagnostic_location stmt_positions diagnostic)
                  in
                  {
                    Render_xml.line;
                    column;
                    verdict = Render_text.diagnostic_severity diagnostic;
                    cond = "";
                    message =
                      Some
                        (Result_text.diagnostic_message diagnostic
                        ^ " [" ^ label ^ "]");
                  })
                (C.res_diagnostics result)
            in
            let checks = checks @ diagnostics in
            let files, nodes, dead =
              Report_dir.emit ~graph ~source_file:(Filename.basename path)
                ~source_text:src ~fn:"main" ~checks ~positions:stmt_positions
                ~globals
            in
            clear_report_dir dir;
            List.iter
              (fun (f : Report_dir.file) -> write_report_file dir f)
              files;
            Ok_report (Printf.sprintf "%d node(s), %d unreachable\n" nodes dead))
          else if !graph_snapshot then
            Ok_graph
              (Render_snapshot.render (Context_graph.build prog (solve ())))
          else if !dot then
            Ok_dot (Render_dot.render (Context_graph.build prog (solve ())))
          else
            Ok_text
              (Render_text.render_report path label stmt_positions (solve ()))
        with Answered o -> o)
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
            "voblint: frontend assets not found -- run: git submodule update \
             --init vendor/g2html";
          exit 5
      | Some assets ->
          Array.iter
            (fun name ->
              let src = Filename.concat assets name in
              if not (Sys.is_directory src) then
                copy_file src (Filename.concat dir name))
            (Sys.readdir assets));
      let seg = Render_xml.xmlify (Filename.basename path) in
      let dot_file =
        Filename.concat dir
          (Filename.concat "dot" (Filename.concat seg "main.dot"))
      in
      let svg_dir = Filename.concat dir (Filename.concat "cfgs" seg) in
      mkdir_p svg_dir;
      let svg_file = Filename.concat svg_dir "main.svg" in
      let cmd =
        Filename.quote_command "dot" [ "-Tsvg"; dot_file; "-o"; svg_file ]
      in
      (* Without a working graphviz the report still carries every node document;
       only the graph pane is empty. Say so and carry on rather than fail. *)
      (match Unix.system (cmd ^ " 2>/dev/null") with
      | Unix.WEXITED 0 -> ()
      | _ ->
          prerr_endline
            "voblint: `dot -Tsvg` failed or is missing -- wrote dot/ but no \
             cfgs/*.svg, so the CFG pane will be empty");
      print_string s;
      (* The entry point is index.xml, not an .html file, and it renders only when
       served: browsers refuse to apply its stylesheet over file://. Saying so
       here is cheaper than the reader concluding nothing was written. *)
      Printf.printf
        "wrote %s/\n\
         The entry point is %s/index.xml -- an .html file to open directly \
         does not\n\
         exist, and file:// will not render it. Serve the directory first:\n\
        \  python3 -m http.server --directory %s 8080\n\
         then open http://localhost:8080/index.xml (or use `pixi run \
         html-report-serve`,\n\
         which serves and opens it for you).\n\
         Needs a browser that still applies XSLT: Chrome removes it in M155/M158\n\
         (November 2026), and this frontend uses it for the entry point and for\n\
         every pane. See README.md for the migration routes.\n"
        dir dir dir
  | Ok Malformed ->
      Printf.eprintf "%s: program is not well-formed\n" path;
      exit 4
  | Ok Invalid_activation ->
      prerr_endline "voblint: --analysis names a domain more than once";
      exit 1
  | Error msg ->
      Printf.eprintf "voblint: %s\n" msg;
      exit 3
