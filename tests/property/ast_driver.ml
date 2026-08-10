(* Property-test oracle driver: reads an S-expression-encoded imp_prog AST
   from stdin, builds it via the exported Isabelle constructors (NOT via
   Vimp_parser -- the whole point is an independently-constructed AST, so a
   parser bug can't hide by round-tripping consistently with itself), prints
   it through the Isabelle-generated pretty_string_of_program, re-parses
   that text with Vimp_parser, and checks the result is structurally equal
   (OCaml's polymorphic (=), which works across the module's abstract types
   at the value level regardless of the signature hiding constructors) to
   the original.

   Default mode prints "OK" or "FAIL <reason>" to stdout. `--print-source`
   instead prints just the generated VIMP source for the AST on stdin, with
   no round-trip check -- used by the mutation-fuzzing property, which needs
   valid source text to mutate rather than a verdict.

   Never used by the main voblint binary; test-only, kept out of the shipped
   CLI. *)

(* -- Minimal S-expression reader (no external dependency) --------------- *)

type sexp = Atom of string | Slist of sexp list

let tokenize (s : string) : string list =
  let n = String.length s in
  let toks = ref [] in
  let i = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\t' || c = '\r' in
  while !i < n do
    let c = s.[!i] in
    if is_space c then incr i
    else if c = '(' || c = ')' then begin
      toks := String.make 1 c :: !toks;
      incr i
    end else begin
      let start = !i in
      while !i < n && (not (is_space s.[!i])) && s.[!i] <> '(' && s.[!i] <> ')' do
        incr i
      done;
      toks := String.sub s start (!i - start) :: !toks
    end
  done;
  List.rev !toks

let parse_sexp (input : string) : sexp =
  let toks = ref (tokenize input) in
  let rec one () =
    match !toks with
    | "(" :: rest ->
      toks := rest;
      Slist (list [])
    | atom :: rest ->
      toks := rest;
      Atom atom
    | [] -> failwith "ast_driver: unexpected end of input"
  and list acc =
    match !toks with
    | ")" :: rest -> toks := rest; List.rev acc
    | [] -> failwith "ast_driver: unterminated list"
    | _ -> let e = one () in list (e :: acc)
  in
  one ()

(* -- sexp -> exported AST constructors ----------------------------------- *)

open Voblint_CLI.Core

let int_of_atom s = Int_of_integer (Z.of_string s)

let rec build_aexp = function
  | Slist [ Atom "N"; Atom n ] -> N (int_of_atom n)
  | Slist [ Atom "V"; Atom x ] -> V x
  | Slist [ Atom "Plus"; a; b ] -> Plus (build_aexp a, build_aexp b)
  | Slist [ Atom "Minus"; a; b ] -> Minus (build_aexp a, build_aexp b)
  | Slist [ Atom "Times"; a; b ] -> Times (build_aexp a, build_aexp b)
  | s -> failwith ("ast_driver: bad aexp sexp: " ^ show_sexp s)

and build_bexp = function
  | Slist [ Atom "Bc"; Atom "true" ] -> Bc true
  | Slist [ Atom "Bc"; Atom "false" ] -> Bc false
  | Slist [ Atom "Not"; b ] -> Not (build_bexp b)
  | Slist [ Atom "And"; b1; b2 ] -> And (build_bexp b1, build_bexp b2)
  | Slist [ Atom "Or"; b1; b2 ] -> Or (build_bexp b1, build_bexp b2)
  | Slist [ Atom "Less"; a1; a2 ] -> Less (build_aexp a1, build_aexp a2)
  | Slist [ Atom "Eq"; a1; a2 ] -> Eqa (build_aexp a1, build_aexp a2)
  | s -> failwith ("ast_driver: bad bexp sexp: " ^ show_sexp s)

and build_aexp_opt = function
  | Atom "None" -> None
  | Slist [ Atom "Some"; a ] -> Some (build_aexp a)
  | s -> failwith ("ast_driver: bad aexp option sexp: " ^ show_sexp s)

and build_dst_opt = function
  | Atom "None" -> None
  | Slist [ Atom "Some"; Atom x ] -> Some x
  | s -> failwith ("ast_driver: bad dst option sexp: " ^ show_sexp s)

and build_actuals = function
  | Slist es -> List.map build_aexp es
  | s -> failwith ("ast_driver: bad actuals sexp: " ^ show_sexp s)

and build_com = function
  | Atom "Skip" -> SKIP
  | Slist [ Atom "Assign"; Atom x; a ] -> Assign (x, build_aexp a)
  | Slist [ Atom "Random"; Atom x ] -> Random x
  | Slist [ Atom "Check"; b ] -> Check (build_bexp b)
  | Slist [ Atom "Seq"; c1; c2 ] -> Seq (build_com c1, build_com c2)
  | Slist [ Atom "If"; b; c1; c2 ] -> If (build_bexp b, build_com c1, build_com c2)
  | Slist [ Atom "While"; b; c ] -> While (build_bexp b, build_com c)
  | Slist [ Atom "Call"; dst; Atom p; actuals ] ->
    Call (build_dst_opt dst, p, build_actuals actuals)
  | Slist [ Atom "Return"; aopt ] -> Return (build_aexp_opt aopt)
  | s -> failwith ("ast_driver: bad com sexp: " ^ show_sexp s)

and show_sexp = function
  | Atom s -> s
  | Slist ss -> "(" ^ String.concat " " (List.map show_sexp ss) ^ ")"

let build_names = function
  | Slist atoms -> List.map (function Atom s -> s | s -> failwith ("bad name: " ^ show_sexp s)) atoms
  | s -> failwith ("ast_driver: bad name list sexp: " ^ show_sexp s)

let build_proc = function
  | Slist [ Atom name; formals; body ] -> (name, proc_decl_of (build_names formals) (build_com body))
  | s -> failwith ("ast_driver: bad proc sexp: " ^ show_sexp s)

let build_program = function
  | Slist [ Slist procs; main_body; globals ] ->
    mk_program (List.map build_proc procs) (build_com main_body) (build_names globals)
  | s -> failwith ("ast_driver: bad program sexp: " ^ show_sexp s)

(* -- Driver --------------------------------------------------------------- *)

let source_text_of_program original =
  let source_chars =
    pretty_string_of_program (prog_table original) (prog_procs original) (prog_main original)
      (declared_global_vars original)
  in
  String.concat "" (List.map (fun c -> String.make 1 (Char.chr (Z.to_int (integer_of_char c)))) source_chars)


let mode = if Array.length Sys.argv > 1 then Sys.argv.(1) else ""

let () =
  let input = In_channel.input_all stdin in
  try
    let original = build_program (parse_sexp input) in
    let source_text = source_text_of_program original in
    if mode = "--print-source" then (print_string source_text; exit 0);
    match Vimp_frontend.program "<generated>" source_text with
    | reparsed, _ when mode = "--print-reprinted" ->
      (* Prints pretty(parse(pretty(original))) -- the print/parse/print
         invariant is implied by original = reparsed (pretty_string_of_program
         is a pure function, so structurally equal ASTs print identically),
         but checking it directly gives a source-text diff on failure instead
         of "the trees differ", and catches the (structural-equality
         assumption) breaking silently. *)
      print_string (source_text_of_program reparsed);
      exit 0
    | reparsed, _ ->
      if original = reparsed then print_endline "OK"
      else begin
        Printf.printf "FAIL round-trip mismatch\n--- generated source ---\n%s\n--- end ---\n" source_text;
        exit 1
      end
    | exception Vimp_frontend.Parse_error { line; col; msg; _ } when mode = "--print-reprinted" ->
      Printf.printf "FAIL re-parse error at %d:%d: %s\n" line col msg;
      exit 1
    | exception Vimp_frontend.Parse_error { line; col; msg; _ } ->
      Printf.printf "FAIL re-parse error at %d:%d: %s\n--- generated source ---\n%s\n--- end ---\n"
        line col msg source_text;
      exit 1
  with
  | Failure msg ->
    Printf.printf "FAIL driver error: %s\n" msg;
    exit 1
  | e ->
    Printf.printf "FAIL unexpected exception: %s\n" (Printexc.to_string e);
    exit 1
