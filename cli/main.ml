(* voblint: a thin CLI over the Isabelle-generated, proved-sound analyzer.

   source text (unverified adapter)
       -> Vimp_lexer/Vimp_parser (this directory, generated from
          grammar/vimp.yaml by scripts/gen_vimp_menhir.py -- ocamllex +
          Menhir, NOT verified) via Vimp_frontend (hand-written glue)
       -> imp_prog
       -> Voblint_CLI.Generated.run_voblint domain solver context view
          (Isabelle-generated). One call decides whether that combination of
          domain, solver and context is legal at all, whether the requested
          view can be served, and -- when both hold -- runs the one analysis
          it names. What comes back is a single result carrying the graph, its
          textual snapshot, the check column and the solved globals, so a
          rendering can never draw its graph from one solve and its findings
          from another.
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
  "voblint --analysis sign|interval|int|parity|congruence \
   [--context none|entry-state|call-string] \
   [--context-depth K] [--context-graph collapsed|expanded] [--dot] \
   [--timeout SECONDS] FILE.vimp\n\
   voblint --parse-only FILE.vimp\n\n\
   Options:\n\
  \  --analysis sign|interval|int|parity|congruence[,...]\n\
  \                             Abstract domain to run (required, unless\n\
  \                             --parse-only). int is the refining composite\n\
  \                             Sign x Interval x Parity x Congruence domain,\n\
  \                             fixed at its most precise refinement mode\n\
  \                             (Refine_Fixpoint) and the warrowing solver.\n\
  \                             parity is the four-element Bot/Even/Odd/Top\n\
  \                             lattice; it decides equalities only by\n\
  \                             refuting them across differing parities, and\n\
  \                             is context-insensitive.\n\
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
  \                             Context sensitivity (default: none, today's\n\
  \                             flow-insensitive, call-site-insensitive\n\
  \                             behaviour). entry-state re-analyzes each\n\
  \                             callee per distinct entered-argument context,\n\
  \                             including under --dot/--dot-full/\n\
  \                             --graph-snapshot (a node covered by several\n\
  \                             contexts renders their joined state under\n\
  \                             --context-graph collapsed; the default draws\n\
  \                             them separately).\n\
  \                             call-string re-analyzes each callee per\n\
  \                             distinct bounded call history (requires\n\
  \                             --context-depth K, K >= 1).\n\
  \                             Every domain serves both context modes, at\n\
  \                             the solver discipline its own routed\n\
  \                             soundness covers; an explicit --solver the\n\
  \                             pairing has no proved route for is a clear\n\
  \                             configuration error, not a silent fallback\n\
  \                             to --context none.\n\
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
  \                             An explicit --context-graph expanded with\n\
  \                             --context none, or with --context call-string\n\
  \                             (whose renderer is always per-context and has\n\
  \                             no collapsed mode), is a configuration error\n\
  \                             rather than a silent fallback.\n\
  \  --solver join|per-origin|warrow|warrow-per-origin\n\
  \                             Pick the vendored solver's update-rule\n\
  \                             discipline directly, bypassing the domain's\n\
  \                             production default (experimental; issue\n\
  \                             #131). warrow is supported by interval and\n\
  \                             int; sign, parity and congruence have a widen\n\
  \                             operator but no solved table behind it yet.\n\
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
  \                             No effect under --context call-string or\n\
  \                             --context-graph expanded: those views already\n\
  \                             annotate every node with its per-context state.\n\
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

let node_label = function
  | Voblint_CLI.Generated.Statement n -> "pp" ^ Z.to_string (Voblint_CLI.Generated.integer_of_nat n)
  | Voblint_CLI.Generated.FunctionEntry s -> "entry_" ^ s
  | Voblint_CLI.Generated.FunctionResult s -> "result_" ^ s

let verdict_label = function
  | Voblint_CLI.Generated.Check_Proved -> "PROVED"
  | Voblint_CLI.Generated.Check_Refuted -> "REFUTED"
  | Voblint_CLI.Generated.Check_Unknown -> "UNKNOWN"

(* Pairs each check row with the source position of the __voblint_check that
   produced it. Both lists are in check-declaration order, one entry per check
   the parser saw -- see Vimp_frontend.program's doc comment -- and only the
   parser knows positions, so a length mismatch leaves no correct alignment to
   fall back on. Every later row would be attributed to the wrong source line,
   which is worse than failing. *)
let paired_checks (rows : Voblint_CLI.Generated.check_row list)
    (check_positions : (int * int) list) =
  if List.length rows <> List.length check_positions then
    failwith
      (Printf.sprintf "verdict/position mismatch: %d verdicts for %d checks"
         (List.length rows) (List.length check_positions));
  List.combine rows check_positions

(* A row's verdict is lifted, and Bot is the proved-unreachable case: no
   execution reaches the check, so no verdict was computed for it. Goblint
   suppresses such a location entirely; naming it DEAD keeps "proved
   unreachable" distinguishable from "the compiler dropped this check", which
   a suppressed row cannot express. The state slice is dropped alongside the
   verdict -- bottom binds nothing worth printing. *)
let render_report (rows : Voblint_CLI.Generated.check_row list)
    (check_positions : (int * int) list) =
  let buf = Buffer.create 256 in
  List.iter
    (fun (row, (line, col)) ->
       let label, state =
         match Voblint_CLI.Generated.row_verdict row with
         | Voblint_CLI.Generated.Bot -> "DEAD", ""
         | Voblint_CLI.Generated.Lifted v ->
           verdict_label v, Voblint_CLI.Generated.row_state row
       in
       Buffer.add_string buf
         (Printf.sprintf "%d:%-2d %-10s %-20s %-8s %s\n" line col
            (node_label (Voblint_CLI.Generated.row_point row))
            (Voblint_CLI.Generated.row_condition row)
            label state))
    (paired_checks rows check_positions);
  Buffer.contents buf

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
  | true ->
    Array.iter (fun n -> rm_rf (Filename.concat path n)) (Sys.readdir path);
    (try Unix.rmdir path with Unix.Unix_error _ -> ())
  | false -> (try Sys.remove path with Sys_error _ -> ())
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
    if Sys.file_exists candidate && Sys.is_directory candidate then Some candidate else None

(* The entries --html owns, and so is free to replace on every run. *)
let owned_entries = [ "nodes"; "files"; "dot"; "cfgs"; "warn"; "index.xml" ]

let rec has_regular_file path =
  match Sys.is_directory path with
  | true -> Array.exists (fun n -> has_regular_file (Filename.concat path n)) (Sys.readdir path)
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
        (fun n -> not (owned n) && has_regular_file (Filename.concat dir n))
        (Array.to_list (Sys.readdir dir))
    with
    | [] -> ()
    | n :: _ ->
      Printf.eprintf
        "voblint: refusing to write a report into %s: it holds %s, which is not \
         voblint output\n"
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
type outcome =
  | Ok_text of string
  | Ok_dot of string
  | Ok_graph of string
  | Ok_report of string
  (* Both rejections are the analyzer's own answer, so they surface from
     inside the contained run rather than from a gate this file keeps. *)
  | Malformed
  | Unsupported_config

(* Raised where an answer other than a successful run arrives, so every
   rendering below can be written against the output it needs. *)
exception Answered of outcome

(* A configuration that publishes no drawing leaves the graph and the snapshot
   empty. Nothing downstream can render that, so asking for a rendering the
   configuration does not produce is the same refusal as asking for an
   analysis it cannot run. *)
let drawing = function
  | Some d -> d
  | None -> raise (Answered Unsupported_config)

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
              | Malformed -> output_string oc "M\n"
              | Unsupported_config -> output_string oc "U\n");
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
                 | "M" -> Ok Malformed
                 | "U" -> Ok Unsupported_config
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
                 (match String.index_opt contents '\n' with
                  | Some i when String.sub contents 0 i = "E" ->
                    ": " ^ String.sub contents (i + 1) (String.length contents - i - 1)
                  | _ -> "")
               with Sys_error _ | End_of_file -> ""
             in
             Error (Printf.sprintf "analysis subprocess exited with code %d%s" code detail)
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
        | "sign" -> Voblint_CLI.Generated.Sign_Analysis
        | "interval" -> Voblint_CLI.Generated.Interval_Analysis
        | "int" -> Voblint_CLI.Generated.Int_Analysis
        | "parity" -> Voblint_CLI.Generated.Parity_Analysis
        | "congruence" -> Voblint_CLI.Generated.Congruence_Analysis
        | _ -> prerr_endline ("unknown --analysis value: " ^ name); exit 1
      in
      let names = String.split_on_char ',' v |> List.filter (fun n -> n <> "") in
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
       | "join" -> solver := Some Voblint_CLI.Generated.Solver_Join
       | "per-origin" -> solver := Some Voblint_CLI.Generated.Solver_PerOrigin
       | "warrow" -> solver := Some Voblint_CLI.Generated.Solver_Warrow
       | "warrow-per-origin" ->
         solver := Some Voblint_CLI.Generated.Solver_WarrowPerOrigin
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
     than folded into Ctx_CallString's own construction. Once matched, the
     depth itself is handed to Ctx_CallString unchecked (a negative
     --context-depth clamps to nat's own zero via nat_of_integer, and k = 0 is
     then rejected the ordinary way, as an unsupported configuration -- no
     second k >= 1 check here). *)
  let context =
    match !context_kind, !context_depth with
    | CK_None, None -> Voblint_CLI.Generated.Ctx_None
    | CK_EntryState, None -> Voblint_CLI.Generated.Ctx_EntryState
    | CK_CallString, Some k ->
      Voblint_CLI.Generated.Ctx_CallString (Voblint_CLI.Generated.nat_of_integer (Z.of_int k))
    | CK_CallString, None ->
      prerr_endline "voblint: --context call-string requires --context-depth K"; exit 1
    | (CK_None | CK_EntryState), Some _ ->
      prerr_endline "voblint: --context-depth is only valid with --context call-string"; exit 1
  in
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
  let prog, check_positions, stmt_positions =
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
  (* expanded is meaningless without a context to expand -- reject rather than
     silently rendering the collapsed graph a bare --context-graph expanded
     might otherwise appear to have requested. *)
  if !context_graph = Some Expanded && context = Voblint_CLI.Generated.Ctx_None then begin
    prerr_endline "voblint: --context-graph expanded requires --context entry-state";
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
  (* --html can show an explicitly chosen solver: every solver route already
     solves a state table, and the report reads the one the requested
     discipline produced. The stdout graph renderings still cannot -- they
     annotate from a view that carries no per-node state. This is about which
     output shape can display a chosen discipline, not about whether the
     discipline itself is legal, so it stays here rather than in the
     analyzer's own configuration answer. *)
  if !solver <> None && (!dot || !dot_full || !graph_snapshot) then begin
    prerr_endline
      "voblint: --solver supports the plain text report and --html, not \
       --dot/--dot-full/--graph-snapshot";
    exit 1
  end;
  if !solver <> None && !html && context <> Voblint_CLI.Generated.Ctx_None then begin
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
  (* An entry-state run is drawn expanded by default: the collapsed rendering
     joins every context covering a point into one box, which is lossy in
     exactly the way the analysis is precise -- three activations of one callee
     become one box, and a point dead in one activation and live in another
     reads as live. --context-graph collapsed still asks for the joined view.
     Ctx_None has one context, so there is nothing to expand there. *)
  let expanded_supported = context = Voblint_CLI.Generated.Ctx_EntryState in
  let context_graph =
    match !context_graph with
    | Some mode -> mode
    | None -> if expanded_supported then Expanded else Collapsed
  in
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
  let output_for k view =
    match Voblint_CLI.Generated.run_voblint k !solver context view prog with
    | Voblint_CLI.Generated.Malformed_Program -> raise (Answered Malformed)
    | Voblint_CLI.Generated.Unsupported_Configuration -> raise (Answered Unsupported_config)
    | Voblint_CLI.Generated.Analysed out -> out
  in
  (* A graph drawn per context already annotates every node with its own
     context's state, so --dot-full has nothing left to add and both settings
     ask for the same view. That coincidence is stated once here instead of
     reappearing in each rendering below. *)
  let per_context_graph = !context_kind = CK_CallString || context_graph = Expanded in
  let graph_view ~full =
    if per_context_graph then Voblint_CLI.Generated.View_Contexts
    else if full then Voblint_CLI.Generated.View_States
    else Voblint_CLI.Generated.View_Checks
  in
  (* The HTML report puts a state in every node document and a verdict beside
     every check, which is one view; drawing contexts separately replaces it
     with the per-context one. *)
  let html_view =
    if per_context_graph then Voblint_CLI.Generated.View_Contexts
    else Voblint_CLI.Generated.View_Checked_States
  in
  (* The text report draws nothing, so neither --context-graph nor --dot-full
     reaches it: it wants the check column and nothing else, at every context.
     Asking for a drawing here would solve a graph no one prints, which on a
     recursive program under --context entry-state is the whole running time. *)
  let report_view = Voblint_CLI.Generated.View_Report in
  (* Checked here, not inside the contained child: a refusal to write into the
     given directory is an argument error the user should see as one, not as a
     subprocess exit code relayed through the analysis timeout wrapper. The
     directory is only emptied later, once the analysis has answered. *)
  if !html then check_report_dir !html_dir;
  match
    run_contained ~timeout:!timeout (fun () ->
      try
        if !html then
          let dir = !html_dir in
          (* Everything a report browser reads back is one solve per domain:
             the graph it draws, the states in its node documents, the check
             column beside the source and the solved globals all come off the
             same result, under the same view. *)
          let payload_for k =
            let out = output_for k html_view in
            ( drawing (Voblint_CLI.Generated.out_graph out),
              Voblint_CLI.Generated.out_checks out,
              Voblint_CLI.Generated.out_globals out )
          in
          let payloads = List.map (fun k -> (analysis_label k, payload_for k)) !analyses in
          let graphs = List.map (fun (label, (g, _, _)) -> (label, g)) payloads in
          let globals =
            List.filter_map
              (fun (label, (_, _, gvs)) -> if gvs = [] then None else Some (label, gvs))
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
            | (_, (_, rows, _)) :: _ ->
              List.filter_map
                (fun (row, (line, column)) ->
                   match Voblint_CLI.Generated.row_verdict row with
                   | Voblint_CLI.Generated.Bot -> None
                   | Voblint_CLI.Generated.Lifted v ->
                     Some
                       { Html_report.line;
                         column;
                         verdict = verdict_label v;
                         cond = Voblint_CLI.Generated.row_condition row })
                (paired_checks rows check_positions)
            | [] ->
              (* --analysis names at least one domain or the run never got
                 here, so an empty list would mean a report with no findings
                 beside its graph. *)
              failwith "no --analysis domain to report"
          in
          let files, nodes, dead =
            Html_report.emit ~graphs ~source_file:(Filename.basename path) ~source_text:src
              ~fn:"main" ~checks ~positions:stmt_positions
              ~globals
          in
          clear_report_dir dir;
          List.iter (fun (f : Html_report.file) -> write_report_file dir f) files;
          Ok_report
            (Printf.sprintf "%d node(s), %d unreachable\n" nodes dead)
        else if !graph_snapshot then
          Ok_graph
            (drawing
               (Voblint_CLI.Generated.out_snapshot
                  (output_for kind (graph_view ~full:!dot_full))))
        else if !dot_full || !dot then
          Ok_dot
            (Dot_render.render
               (drawing
                  (Voblint_CLI.Generated.out_graph
                     (output_for kind (graph_view ~full:!dot_full)))))
        else
          Ok_text
            (render_report
               (Voblint_CLI.Generated.out_checks (output_for kind report_view))
               check_positions)
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
       which serves and opens it for you).\n\
       Needs a browser that still applies XSLT: Chrome removes it in M155/M158\n\
       (November 2026), and this frontend uses it for the entry point and for\n\
       every pane. See README.md for the migration routes.\n"
      dir dir dir
  | Ok Malformed -> Printf.eprintf "%s: program is not well-formed\n" path; exit 4
  | Ok Unsupported_config ->
    prerr_endline "voblint: unsupported --analysis/--context/--solver combination";
    exit 1
  | Error msg -> Printf.eprintf "voblint: %s\n" msg; exit 3
