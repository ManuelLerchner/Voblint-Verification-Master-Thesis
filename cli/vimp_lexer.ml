(* Hand-written lexer for the VIMP surface syntax, mirroring the concrete
   grammar in src/VIMP/VIMP_Notation.thy's parse_translation (the "imp2_*"
   nonterminals and their literal tokens). That syntax is Isabelle frontend
   machinery (parse_translation, ML-level) and is not itself executable or
   code-generatable -- see docs/CLI_DESIGN.md -- so this lexer/parser is a
   new, unverified, native reimplementation of the same surface grammar. *)

type token =
  | IDENT of string
  | NUM of int
  | KW_PROGRAM
  | KW_GLOBAL
  | KW_VOID
  | KW_SKIP
  | KW_RANDOM
  | KW_RETURN
  | KW_CHECK
  | KW_IF
  | KW_ELSE
  | KW_WHILE
  | KW_TRUE
  | KW_FALSE
  | LBRACE
  | RBRACE
  | LPAREN
  | RPAREN
  | SEMI
  | COMMA
  | ASSIGN
  | PLUS
  | MINUS
  | STAR
  | LT
  | EQEQ
  | AND
  | OR
  | NOT
  | EOF

type positioned_token = { tok : token; line : int; col : int }

exception Lex_error of { line : int; col : int; msg : string }

let keyword_of_ident = function
  | "program" -> Some KW_PROGRAM
  | "global" -> Some KW_GLOBAL
  | "void" -> Some KW_VOID
  | "skip" -> Some KW_SKIP
  | "random" -> Some KW_RANDOM
  | "return" -> Some KW_RETURN
  | "__voblint_check" -> Some KW_CHECK
  | "if" -> Some KW_IF
  | "else" -> Some KW_ELSE
  | "while" -> Some KW_WHILE
  | "true" -> Some KW_TRUE
  | "false" -> Some KW_FALSE
  | _ -> None

let is_ident_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_ident_char c = is_ident_start c || (c >= '0' && c <= '9')
let is_digit c = c >= '0' && c <= '9'

(* Scans the whole source once, up front: simpler to reason about than an
   interleaved lex/parse loop, and VIMP source files are small. *)
let tokenize (src : string) : positioned_token list =
  let n = String.length src in
  let line = ref 1 and col = ref 1 in
  let pos = ref 0 in
  let toks = ref [] in
  let peek off = if !pos + off < n then Some src.[!pos + off] else None in
  let advance () =
    (match peek 0 with
     | Some '\n' -> incr line; col := 1
     | Some _ -> incr col
     | None -> ());
    incr pos
  in
  let emit tok start_line start_col = toks := { tok; line = start_line; col = start_col } :: !toks in
  let rec skip_trivia () =
    match peek 0 with
    | Some (' ' | '\t' | '\r' | '\n') -> advance (); skip_trivia ()
    | Some '/' when peek 1 = Some '/' ->
      while peek 0 <> None && peek 0 <> Some '\n' do advance () done;
      skip_trivia ()
    | _ -> ()
  in
  while (skip_trivia (); !pos < n) do
    let sl = !line and sc = !col in
    let c = Option.get (peek 0) in
    if is_ident_start c then begin
      let start = !pos in
      while (match peek 0 with Some c -> is_ident_char c | None -> false) do advance () done;
      let text = String.sub src start (!pos - start) in
      match keyword_of_ident text with
      | Some kw -> emit kw sl sc
      | None -> emit (IDENT text) sl sc
    end else if is_digit c then begin
      let start = !pos in
      while (match peek 0 with Some c -> is_digit c | None -> false) do advance () done;
      emit (NUM (int_of_string (String.sub src start (!pos - start)))) sl sc
    end else begin
      let two = match peek 0, peek 1 with Some a, Some b -> Some (a, b) | _ -> None in
      match two with
      | Some (':', '=') -> advance (); advance (); emit ASSIGN sl sc
      | Some ('=', '=') -> advance (); advance (); emit EQEQ sl sc
      | Some ('&', '&') -> advance (); advance (); emit AND sl sc
      | Some ('|', '|') -> advance (); advance (); emit OR sl sc
      | _ ->
        (advance ();
         match c with
         | '{' -> emit LBRACE sl sc
         | '}' -> emit RBRACE sl sc
         | '(' -> emit LPAREN sl sc
         | ')' -> emit RPAREN sl sc
         | ';' -> emit SEMI sl sc
         | ',' -> emit COMMA sl sc
         | '+' -> emit PLUS sl sc
         | '-' -> emit MINUS sl sc
         | '*' -> emit STAR sl sc
         | '<' -> emit LT sl sc
         | '!' -> emit NOT sl sc
         | c -> raise (Lex_error { line = sl; col = sc; msg = Printf.sprintf "unexpected character %C" c }))
    end
  done;
  emit EOF !line !col;
  List.rev !toks
