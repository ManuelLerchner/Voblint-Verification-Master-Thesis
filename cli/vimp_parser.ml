(* Recursive-descent parser over Vimp_lexer's token stream, building an
   imp_prog directly from the exported AST constructors (Voblint_CLI.Core) --
   no parser-owned intermediate representation, per docs/CLI_DESIGN.md's
   trust-boundary note. Grammar matches VIMP_Notation.thy's parse_translation
   exactly, including the "program { ... }" wrapper: exact surface-language
   compatibility with the Isabelle notation is preferred over the minor
   convenience of treating the file boundary as the program boundary. *)

open Vimp_lexer

exception Parse_error of { file : string; line : int; col : int; msg : string }

type state = {
  file : string;
  mutable toks : positioned_token list;
  (* Source (line, col) of each "__voblint_check(...)" occurrence, in
     encounter order -- analyse_with_state's report is empirically in the
     same relative order (every existing case relies on this already), so
     zipping this list against report entries recovers the check's real
     source line for line-number-keyed test matching, the same way
     Goblint's own harness keys expected results by line rather than by
     position-in-file of the annotation comment. *)
  mutable check_positions : (int * int) list;
}

let cur st = match st.toks with t :: _ -> t | [] -> assert false

let fail st msg =
  let t = cur st in
  raise (Parse_error { file = st.file; line = t.line; col = t.col; msg })

let advance st = match st.toks with _ :: rest -> st.toks <- rest | [] -> ()

let expect st tok msg =
  if (cur st).tok = tok then advance st else fail st msg

let ident st =
  match (cur st).tok with
  | IDENT s -> advance st; s
  | _ -> fail st "expected identifier"

(* -- Arithmetic expressions ------------------------------------------ *)
(* No parenthesization: matches the source grammar's imp2_aexp productions,
   which never declare a "(" aexp ")" case (unlike imp2_bexp's bparen). *)

let aexp_atom st =
  match (cur st).tok with
  | NUM n -> advance st; Voblint_CLI.Core.N (Voblint_CLI.Core.Int_of_integer (Z.of_int n))
  | IDENT x -> advance st; Voblint_CLI.Core.V x
  | MINUS ->
    advance st;
    (match (cur st).tok with
     | NUM n -> advance st; Voblint_CLI.Core.N (Voblint_CLI.Core.Int_of_integer (Z.of_int (-n)))
     | IDENT x -> advance st; Voblint_CLI.Core.Minus (Voblint_CLI.Core.N (Voblint_CLI.Core.Int_of_integer Z.zero), Voblint_CLI.Core.V x)
     | _ -> fail st "expected a number or identifier after unary '-'")
  | _ -> fail st "expected an arithmetic expression"

let aexp_prod st =
  let a = ref (aexp_atom st) in
  let continue_ = ref true in
  while !continue_ do
    match (cur st).tok with
    | STAR -> advance st; a := Voblint_CLI.Core.Times (!a, aexp_atom st)
    | _ -> continue_ := false
  done;
  !a

let aexp st =
  let a = ref (aexp_prod st) in
  let continue_ = ref true in
  while !continue_ do
    match (cur st).tok with
    | PLUS -> advance st; a := Voblint_CLI.Core.Plus (!a, aexp_prod st)
    | MINUS -> advance st; a := Voblint_CLI.Core.Minus (!a, aexp_prod st)
    | _ -> continue_ := false
  done;
  !a

(* -- Boolean expressions ---------------------------------------------- *)

let rec bexp_prim st =
  match (cur st).tok with
  | KW_TRUE -> advance st; Voblint_CLI.Core.Bc true
  | KW_FALSE -> advance st; Voblint_CLI.Core.Bc false
  | NOT -> advance st; Voblint_CLI.Core.Not (bexp_prim st)
  | LPAREN -> advance st; let b = bexp_or st in expect st RPAREN "expected ')'"; b
  | _ ->
    let a1 = aexp st in
    (match (cur st).tok with
     | LT -> advance st; Voblint_CLI.Core.Less (a1, aexp st)
     | EQEQ -> advance st; Voblint_CLI.Core.Eqa (a1, aexp st)
     | _ -> fail st "expected '<' or '==' after arithmetic expression")

and bexp_and st =
  let b = ref (bexp_prim st) in
  let continue_ = ref true in
  while !continue_ do
    match (cur st).tok with
    | AND -> advance st; b := Voblint_CLI.Core.And (!b, bexp_prim st)
    | _ -> continue_ := false
  done;
  !b

and bexp_or st =
  let b = ref (bexp_and st) in
  let continue_ = ref true in
  while !continue_ do
    match (cur st).tok with
    | OR -> advance st; b := Voblint_CLI.Core.Or (!b, bexp_and st)
    | _ -> continue_ := false
  done;
  !b

let bexp = bexp_or

(* -- Actuals ------------------------------------------------------------ *)

let actuals st =
  if (cur st).tok = RPAREN then []
  else begin
    let es = ref [ aexp st ] in
    while (cur st).tok = COMMA do
      advance st;
      es := aexp st :: !es
    done;
    List.rev !es
  end

(* -- Statements ---------------------------------------------------------- *)

(* Left-folds ';'-chained statements into nested Seq, matching
   VIMP_Notation.thy's stmts_tr (stmts_seq ss s = Seq(stmts_tr ss, stmt_tr s)). *)
let rec stmt st : Voblint_CLI.Core.com =
  match (cur st).tok with
  | KW_SKIP -> advance st; Voblint_CLI.Core.SKIP
  | KW_RETURN -> advance st; Voblint_CLI.Core.Return (Some (aexp st))
  | KW_CHECK ->
    let pos = cur st in
    st.check_positions <- st.check_positions @ [ (pos.line, pos.col) ];
    advance st;
    expect st LPAREN "expected '(' after __voblint_check";
    let b = bexp st in
    expect st RPAREN "expected ')'";
    Voblint_CLI.Core.Check b
  | KW_IF ->
    advance st;
    expect st LPAREN "expected '(' after if";
    let cond = bexp st in
    expect st RPAREN "expected ')'";
    let c1 = block st in
    (match (cur st).tok with
     | KW_ELSE -> advance st; Voblint_CLI.Core.If (cond, c1, block st)
     | _ -> fail st "expected 'else' (if has no else-less form in VIMP)")
  | KW_WHILE ->
    advance st;
    expect st LPAREN "expected '(' after while";
    let cond = bexp st in
    expect st RPAREN "expected ')'";
    Voblint_CLI.Core.While (cond, block st)
  | IDENT name ->
    advance st;
    (match (cur st).tok with
     | LPAREN ->
       advance st;
       let es = actuals st in
       expect st RPAREN "expected ')'";
       Voblint_CLI.Core.Call (None, name, es)
     | ASSIGN ->
       advance st;
       (match (cur st).tok with
        | KW_RANDOM ->
          advance st;
          expect st LPAREN "expected '(' after random"; expect st RPAREN "expected ')'";
          Voblint_CLI.Core.Random name
        | IDENT callee ->
          (* Lookahead: "x := f(...)" (callret) vs "x := f" being read as a
             one-token aexp is impossible here since aexp has no bare
             procedure-name form, so IDENT-then-'(' always disambiguates. *)
          let save = st.toks in
          advance st;
          if (cur st).tok = LPAREN then begin
            advance st;
            let es = actuals st in
            expect st RPAREN "expected ')'";
            Voblint_CLI.Core.Call (Some name, callee, es)
          end else begin
            st.toks <- save;
            Voblint_CLI.Core.Assign (name, aexp st)
          end
        | _ -> Voblint_CLI.Core.Assign (name, aexp st))
     | _ -> fail st "expected ':=' or '(' after identifier")
  | _ -> fail st "expected a statement"

and stmts st : Voblint_CLI.Core.com =
  let c = ref (stmt st) in
  while (cur st).tok = SEMI do
    advance st;
    c := Voblint_CLI.Core.Seq (!c, stmt st)
  done;
  !c

and block st : Voblint_CLI.Core.com =
  expect st LBRACE "expected '{'";
  let c = stmts st in
  expect st RBRACE "expected '}'";
  c

(* -- Procedures and programs -------------------------------------------- *)

let ident_list st =
  let xs = ref [ ident st ] in
  while (cur st).tok = COMMA do advance st; xs := ident st :: !xs done;
  List.rev !xs

let check_distinct st kind xs =
  let rec dup = function
    | [] -> None
    | x :: rest -> if List.mem x rest then Some x else dup rest
  in
  match dup xs with
  | Some x -> fail st (Printf.sprintf "duplicate %s: %s" kind x)
  | None -> ()

let func st =
  expect st KW_VOID "expected 'void'";
  let name = ident st in
  expect st LPAREN "expected '('";
  let formals = if (cur st).tok = RPAREN then [] else ident_list st in
  expect st RPAREN "expected ')'";
  check_distinct st (Printf.sprintf "formal parameter of '%s'" name) formals;
  let body = block st in
  (name, formals, body)

(* "program { [global x, y, ...;] void f(...) { ... } ... }", matching
   VIMP_Notation.thy's "_PROGKW0"/"_PROGKW" productions exactly (global
   declaration optional, at most once, must come first if present). *)
let program (file : string) (src : string) :
    unit Voblint_CLI.Core.imp_prog_ext * (int * int) list =
  let st = { file; toks = tokenize src; check_positions = [] } in
  expect st KW_PROGRAM "expected 'program'";
  expect st LBRACE "expected '{'";
  let globals =
    if (cur st).tok = KW_GLOBAL then begin
      advance st;
      let xs = ident_list st in
      expect st SEMI "expected ';' after global declaration";
      xs
    end else []
  in
  check_distinct st "declared global" globals;
  let funcs = ref [] in
  while (cur st).tok <> RBRACE do
    funcs := func st :: !funcs
  done;
  expect st RBRACE "expected '}'";
  expect st EOF "expected end of file";
  let funcs = List.rev !funcs in
  check_distinct st "procedure" (List.map (fun (n, _, _) -> n) funcs);
  List.iter
    (fun (n, formals, _) ->
       match List.filter (fun f -> List.mem f globals) formals with
       | [] -> ()
       | bad ->
         fail st
           (Printf.sprintf "'%s' declares global(s) as formal(s): %s" n (String.concat ", " bad)))
    funcs;
  let mains, procs = List.partition (fun (n, _, _) -> n = "main") funcs in
  let main_body =
    match mains with
    | [ ("main", [], body) ] -> body
    | [ ("main", _ :: _, _) ] -> fail st "'main' must have no formals"
    | [] -> fail st "missing 'void main() { ... }'"
    | _ -> fail st "more than one 'void main()'"
  in
  let proc_rep =
    List.map (fun (n, formals, body) -> (n, Voblint_CLI.Core.proc_decl_of formals body)) procs
  in
  (Voblint_CLI.Core.make proc_rep main_body globals, st.check_positions)
