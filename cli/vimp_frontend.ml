(* Hand-written glue between the generated frontend (Vimp_parser/Vimp_lexer
   -- both generated from grammar/vimp.yaml by scripts/gen_vimp_menhir.py;
   see cli/vimp_parser.mly, cli/vimp_lexer.mll) and what callers need: a
   single `program` entrypoint of the shape they already expect --
   (file, source text) -> (imp_prog, check_positions) -- so main.ml and
   tests/property/ast_driver.ml need only rename their call site
   (Vimp_parser.program -> Vimp_frontend.program), not restructure around
   Menhir's own lexbuf-driven interface.

   check_positions is a CLI reporting concern (each "__voblint_check(...)"
   occurrence's source position, in encounter order, for the text report's
   line:col column -- see main.ml's render_text_report), not a language
   one, so it doesn't belong in the generated grammar; tracked here by
   wrapping the token function to note each CHECK token's position as it's
   consumed. *)

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
let stmt_positions (prog : unit Voblint_CLI.Core.imp_prog_ext) :
    (int * (int * int * int * int)) list =
  let recorded = Vimp_positions.definitions () in
  let index_of = function
    | Voblint_CLI.Core.Statement k -> Some (Z.to_int (Voblint_CLI.Core.integer_of_nat k))
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
                   [ ( i,
                       ( p.Vimp_positions.line,
                         p.Vimp_positions.column,
                         p.Vimp_positions.end_line,
                         p.Vimp_positions.end_column ) ) ]
                 | None -> [])
              nodes ps)
       | _ -> [])
    (Voblint_CLI.Core.prog_stmt_post_order prog)

let program (file : string) (src : string) :
  unit Voblint_CLI.Core.imp_prog_ext * (int * int) list * (int * (int * int * int * int)) list =
  let lexbuf = Lexing.from_string src in
  Vimp_positions.reset ();
  let check_positions = ref [] in
  let tracked_token lexbuf =
    let tok = Vimp_lexer.token lexbuf in
    (if tok = Vimp_parser.CHECK then check_positions := position_of lexbuf :: !check_positions);
    tok
  in
  try
    let prog = Vimp_parser.program tracked_token lexbuf in
    (prog, List.rev !check_positions, stmt_positions prog)
  with
  | Vimp_lexer.Lex_error { line; col; msg } -> raise (Parse_error { file; line; col; msg })
  | Vimp_parser.Error ->
    let line, col = position_of lexbuf in
    raise (Parse_error { file; line; col; msg = "syntax error" })
  | Failure msg ->
    let line, col = position_of lexbuf in
    raise (Parse_error { file; line; col; msg })
