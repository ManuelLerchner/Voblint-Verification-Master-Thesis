(* voblint: a thin CLI over the Isabelle-generated, proved-sound analyzer.

   source text (unverified adapter)
       -> Vimp_lexer/Vimp_parser (this directory, generated from
          manifests/vimp-grammar.yaml by scripts/gen_vimp_menhir.py -- ocamllex +
          Menhir, NOT verified) via Vimp_frontend (hand-written glue)
       -> imp_prog
       -> Voblint_CLI.Generated.run_voblint domain globals context
          (Isabelle-generated). One call checks the program is well-formed and
          runs the one analysis the domain, global update rule and context name;
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
  "voblint --analysis sign|interval|int|parity|congruence [--context \
   none|entry-state|call-string] [--context-depth K] [--globals \
   join|per-origin|warrow|warrow-per-origin] [--dot] [--timeout SECONDS] \
   FILE.vimp\n\
   voblint --parse-only FILE.vimp\n\n\
   Options:\n\
  \  --analysis sign|interval|int|parity|congruence[,...]\n\
  \                             Abstract domain to run (required, unless\n\
  \                             --parse-only). int is the refining composite\n\
  \                             Sign x Interval x Parity x Congruence domain,\n\
  \                             fixed at its most precise refinement mode\n\
  \                             (Refine_Fixpoint).\n\
  \                             parity is the four-element Bot/Even/Odd/Top\n\
  \                             lattice; it decides equalities only by\n\
  \                             refuting them across differing parities.\n\
  \                             congruence is the residue-class domain, one\n\
  \                             value constrained to x = r (mod m); m = 0\n\
  \                             pins a single integer and m = 1 constrains\n\
  \                             nothing. It decides no orderings and decides\n\
  \                             equalities only between singletons.\n\
  \                             A comma list (e.g. int,interval) puts every\n\
  \                             named domain side by side in one --html\n\
  \                             report, one <analysis> block per node, so\n\
  \                             their precision can be compared in place.\n\
  \                             Requires --html and --context none; every\n\
  \                             other output path uses the first domain only.\n\
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
  \  --globals join|per-origin|warrow|warrow-per-origin\n\
  \                             How the solver merges a value side-effected\n\
  \                             into a global: joined, joined per origin,\n\
  \                             warrowed, or warrowed per origin (default:\n\
  \                             warrow). Locals are warrowed at loop heads\n\
  \                             under every rule.\n\
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

(* Names the analysis in the report's own <analysis name="..."> element, so a
   node document says which domain produced the state it shows. *)
let analysis_label = function
  | Voblint_CLI.Generated.Sign_Analysis -> "sign"
  | Voblint_CLI.Generated.Interval_Analysis -> "interval"
  | Voblint_CLI.Generated.Int_Analysis -> "int"
  | Voblint_CLI.Generated.Parity_Analysis -> "parity"
  | Voblint_CLI.Generated.Congruence_Analysis -> "congruence"

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
  (* The rejection is the analyzer's own answer, so it surfaces from inside
     the contained run rather than from a gate this file keeps. *)
  | Malformed

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
              | Malformed -> output_string oc "M\n");
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
                  Error
                    (Printf.sprintf
                       "analysis did not finish within %.0fs (killed)" timeout)
                end
                else begin
                  ignore (Unix.select [] [] [] 0.05);
                  wait_loop ()
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
          wait_loop ())

(* --context/--context-depth are two independent flags that can arrive in
   either order, but Ctx_CallString needs the depth at construction time --
   so parsing collects an intermediate tag + optional depth, and the final
   immutable context_mode value is assembled once, after parse_args returns,
   from both together. *)
type context_kind = CK_None | CK_EntryState | CK_CallString

let () =
  let analysis = ref None in
  (* Every domain named by --analysis, in order. Only --html reads past the
     head; see the comma-list note in parse_args. *)
  let analyses = ref [] in
  let context_kind = ref CK_None in
  let context_depth = ref None in
  let globals = ref Voblint_CLI.Generated.Globals_Warrow in
  let dot = ref false in
  let graph_snapshot = ref false in
  let html = ref false in
  (* Generated report output stays under build/; --html-out is the override.
     Taking no argument keeps `--html FILE.vimp` from reading the program as
     the output directory. *)
  let html_dir = ref "build/report" in
  let parse_only = ref false in
  let timeout = ref 10.0 in
  let file = ref None in
  let rec parse_args = function
    | [] -> ()
    | "--help" :: _ ->
        print_endline usage;
        exit 0
    | "--analysis" :: v :: rest ->
        (* A comma list asks one report to carry several domains side by side.
         The head stays the analysis every other output path means by
         "--analysis", so a single name behaves exactly as before. *)
        let kind_of name =
          match name with
          | "sign" -> Voblint_CLI.Generated.Sign_Analysis
          | "interval" -> Voblint_CLI.Generated.Interval_Analysis
          | "int" -> Voblint_CLI.Generated.Int_Analysis
          | "parity" -> Voblint_CLI.Generated.Parity_Analysis
          | "congruence" -> Voblint_CLI.Generated.Congruence_Analysis
          | _ ->
              prerr_endline ("unknown --analysis value: " ^ name);
              exit 1
        in
        let names =
          String.split_on_char ',' v |> List.filter (fun n -> n <> "")
        in
        if names = [] then begin
          prerr_endline "voblint: --analysis expects at least one domain";
          exit 1
        end;
        analyses := List.map kind_of names;
        analysis := Some (List.hd !analyses);
        parse_args rest
    | "--context" :: v :: rest ->
        (match v with
        | "none" -> context_kind := CK_None
        | "entry-state" -> context_kind := CK_EntryState
        | "call-string" -> context_kind := CK_CallString
        | _ ->
            prerr_endline ("unknown --context value: " ^ v);
            exit 1);
        parse_args rest
    | "--context-depth" :: v :: rest ->
        (try context_depth := Some (int_of_string v)
         with _ ->
           prerr_endline ("--context-depth expects an integer: " ^ v);
           exit 1);
        parse_args rest
    | "--globals" :: v :: rest ->
        (match v with
        | "join" -> globals := Voblint_CLI.Generated.Globals_Join
        | "per-origin" -> globals := Voblint_CLI.Generated.Globals_Per_Origin
        | "warrow" -> globals := Voblint_CLI.Generated.Globals_Warrow
        | "warrow-per-origin" ->
            globals := Voblint_CLI.Generated.Globals_Warrow_Per_Origin
        | _ ->
            prerr_endline ("unknown --globals value: " ^ v);
            exit 1);
        parse_args rest
    | "--dot" :: rest ->
        dot := true;
        parse_args rest
    | "--graph-snapshot" :: rest ->
        graph_snapshot := true;
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
  (* --context-depth is only meaningful paired with --context call-string, so
     a mismatch between the two flags is rejected here. *)
  let context =
    match (!context_kind, !context_depth) with
    | CK_None, None -> Voblint_CLI.Generated.Ctx_None
    | CK_EntryState, None -> Voblint_CLI.Generated.Ctx_EntryState
    | CK_CallString, Some k when k < 0 ->
        prerr_endline "voblint: --context-depth must not be negative";
        exit 1
    | CK_CallString, Some k ->
        Voblint_CLI.Generated.Ctx_CallString
          (Voblint_CLI.Generated.nat_of_integer (Z.of_int k))
    | CK_CallString, None ->
        prerr_endline
          "voblint: --context call-string requires --context-depth K";
        exit 1
    | (CK_None | CK_EntryState), Some _ ->
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
  let prog, check_positions, stmt_positions, _ =
    try Vimp_frontend.program path src
    with Vimp_frontend.Parse_error { file; line; col; msg } ->
      Printf.eprintf "%s:%d:%d: parse error: %s\n" file line col msg;
      exit 2
  in
  if !parse_only then exit 0;
  let kind =
    match !analysis with
    | Some k -> k
    | None ->
        prerr_endline "missing --analysis sign|interval|int|parity|congruence";
        prerr_endline usage;
        exit 1
  in
  (* --html writes a directory; the other renderings write one document to
     stdout. Asking for both is a contradiction about where output goes, not a
     combination to silently resolve. *)
  if !html && (!dot || !graph_snapshot) then begin
    prerr_endline
      "voblint: --html cannot be combined with --dot/--graph-snapshot";
    exit 1
  end;
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
    if context <> Voblint_CLI.Generated.Ctx_None then begin
      prerr_endline
        "voblint: --analysis with several domains requires --context none";
      exit 1
    end
  end;
  let result_for k =
    match C.run_voblint k !globals context prog with
    | C.Malformed_Program -> raise (Answered Malformed)
    | C.Analysed result ->
        if !html || !dot || !graph_snapshot then
          print_diagnostics path (analysis_label k) stmt_positions
            (C.res_diagnostics result);
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
            (* Everything a report browser reads back is one solve per domain:
             the graph it draws, the states in its node documents, the check
             column beside the source and the solved globals all come off the
             same result, under the same view. *)
            let payload_for k =
              let result = result_for k in
              ( Context_graph.build prog result,
                C.res_checks result,
                A.global_rows result,
                C.res_diagnostics result )
            in
            let payloads =
              List.map (fun k -> (analysis_label k, payload_for k)) !analyses
            in
            let graphs =
              List.map (fun (label, (g, _, _, _)) -> (label, g)) payloads
            in
            let globals =
              List.filter_map
                (fun (label, (_, _, gvs, _)) ->
                  if gvs = [] then None else Some (label, gvs))
                payloads
            in
            (* The source view's inline annotations need a verdict *and* a
             position, and only the parser knows positions -- it notes each
             __voblint_check token as it consumes one, in the same order the
             check column lists them. The head of --analysis is the domain the
             text report would print, so its verdicts are the ones annotated
             here. Unreachable checks are dropped, matching what the text
             report's DEAD label says without a verdict to show. *)
            let checks =
              match payloads with
              | (_, (_, rows, _, _)) :: _ ->
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
                    (Render_text.paired_checks rows check_positions)
              | [] ->
                  (* --analysis names at least one domain or the run never got
                 here, so an empty list would mean a report with no findings
                 beside its graph. *)
                  failwith "no --analysis domain to report"
            in
            let diagnostics =
              List.concat_map
                (fun (label, (_, _, _, diagnostics)) ->
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
                    diagnostics)
                payloads
            in
            let checks = checks @ diagnostics in
            let files, nodes, dead =
              Report_dir.emit ~graphs ~source_file:(Filename.basename path)
                ~source_text:src ~fn:"main" ~checks ~positions:stmt_positions
                ~globals
            in
            clear_report_dir dir;
            List.iter
              (fun (f : Report_dir.file) -> write_report_file dir f)
              files;
            Ok_report (Printf.sprintf "%d node(s), %d unreachable\n" nodes dead))
          else if !graph_snapshot then
            Ok_graph (Render_snapshot.render (Context_graph.build prog (result_for kind)))
          else if !dot then
            Ok_dot (Render_dot.render (Context_graph.build prog (result_for kind)))
          else
            Ok_text
              (Render_text.render_report path (analysis_label kind) stmt_positions
                 (result_for kind) check_positions)
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
  | Error msg ->
      Printf.eprintf "voblint: %s\n" msg;
      exit 3
