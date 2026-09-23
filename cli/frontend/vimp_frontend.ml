(* Hand-written glue between the generated frontend (Vimp_parser/Vimp_lexer
   -- both generated from manifests/vimp-grammar.yaml by scripts/gen_vimp_menhir.py;
   see cli/frontend/vimp_parser.mly, cli/frontend/vimp_lexer.mll) and its callers: a single
   `program` entry point, (file, source text) -> (imp_prog, stmt_positions,
   header_positions), so the CLI entries and tests/property/ast_driver.ml need
   not drive Menhir's own lexbuf-driven interface.

   Checks need no position table: each carries its own source position as its
   label (Vimp_positions.label), and the analysis result lists it under that
   label. *)

exception Parse_error of { file : string; line : int; col : int; msg : string }

let position_of (lexbuf : Lexing.lexbuf) : int * int =
  let pos = Lexing.lexeme_start_p lexbuf in
  (pos.Lexing.pos_lnum, pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)

(* Which Statement index each recorded source position belongs to.

   Both sides of this pairing are keyed by definition, and neither could be a
   flat list. The parser records bottom-up, so its positions come out in
   post-order over each body; compile lays indices out procedure by procedure
   with main last, whatever order the source wrote the definitions in.
   prog_stmt_post_order (Compile_Invariants) answers both at once -- per
   definition, that body's indices in the order a bottom-up parser finishes
   them -- so all this does is zip.

   A definition whose two lists disagree in length contributes nothing rather
   than a shifted map: every position after the mismatch would be attributed to
   the wrong command, and a wrong line is worse than a missing one. *)
let stmt_positions (prog : unit Voblint_CLI.Generated.imp_prog_ext) :
    (int * (int * int * int * int)) list =
  let recorded =
    List.map
      (fun (d : Vimp_positions.definition) -> (d.name, d.statements))
      (Vimp_positions.definitions ())
  in
  let index_of = function
    | Voblint_CLI.Generated.Statement k ->
        Some (Z.to_int (Voblint_CLI.Generated.integer_of_nat k))
    | _ -> None
  in
  List.concat_map
    (fun (name, nodes) ->
      match List.assoc_opt name recorded with
      | Some ps when List.length ps = List.length nodes ->
          List.concat
            (List.map2
               (fun node (p : Vimp_positions.pos) ->
                 match index_of node with
                 | Some i ->
                     [
                       ( i,
                         ( p.Vimp_positions.line,
                           p.Vimp_positions.column,
                           p.Vimp_positions.end_line,
                           p.Vimp_positions.end_column ) );
                     ]
                 | None -> [])
               nodes ps)
      | _ -> [])
    (Voblint_CLI.Generated.prog_stmt_post_order prog)

(* Each procedure's header span, by name, for the browser's parameter hints. *)
let header_positions () : (string * (int * int * int * int)) list =
  List.map
    (fun (d : Vimp_positions.definition) ->
      let h = d.header in
      (d.name, (h.line, h.column, h.end_line, h.end_column)))
    (Vimp_positions.definitions ())

let program (file : string) (src : string) :
    unit Voblint_CLI.Generated.imp_prog_ext
    * (int * (int * int * int * int)) list
    * (string * (int * int * int * int)) list =
  let lexbuf = Lexing.from_string src in
  Vimp_positions.reset ();
  try
    let module I = Vimp_parser.MenhirInterpreter in
    let supplier = I.lexer_lexbuf_to_supplier Vimp_lexer.token lexbuf in
    let checkpoint = Vimp_parser.Incremental.program lexbuf.lex_curr_p in
    let prog = I.loop supplier checkpoint in
    (prog, stmt_positions prog, header_positions ())
  with
  | Vimp_lexer.Lex_error { line; col; msg } ->
      raise (Parse_error { file; line; col; msg })
  | Vimp_parser.Error ->
      let line, col = position_of lexbuf in
      raise (Parse_error { file; line; col; msg = "syntax error" })
  | Failure msg ->
      let line, col = position_of lexbuf in
      raise (Parse_error { file; line; col; msg })
