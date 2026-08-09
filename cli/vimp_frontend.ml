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

let program (file : string) (src : string) : unit Voblint_CLI.Core.imp_prog_ext * (int * int) list =
  let lexbuf = Lexing.from_string src in
  let check_positions = ref [] in
  let tracked_token lexbuf =
    let tok = Vimp_lexer.token lexbuf in
    (if tok = Vimp_parser.CHECK then check_positions := position_of lexbuf :: !check_positions);
    tok
  in
  try
    let prog = Vimp_parser.program tracked_token lexbuf in
    (prog, List.rev !check_positions)
  with
  | Vimp_lexer.Lex_error { line; col; msg } -> raise (Parse_error { file; line; col; msg })
  | Vimp_parser.Error ->
    let line, col = position_of lexbuf in
    raise (Parse_error { file; line; col; msg = "syntax error" })
  | Failure msg ->
    let line, col = position_of lexbuf in
    raise (Parse_error { file; line; col; msg })
