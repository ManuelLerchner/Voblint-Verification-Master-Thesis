(* Property-test oracle driver: reads an S-expression-encoded imp_prog AST
   from stdin, builds it via the exported Isabelle constructors (NOT via
   Vimp_parser -- the whole point is an independently-constructed AST, so a
   parser bug can't hide by round-tripping consistently with itself), prints
   it through the grammar-generated Vimp_printer, re-parses
   that text with Vimp_parser, and checks the result is structurally equal
   (OCaml's polymorphic (=), which works across the module's abstract types
   at the value level regardless of the signature hiding constructors) to
   the original.

   The input carries the kind of every variable beside the program, as the
   parser returns it; a round-trip compares both.

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
    end
    else begin
      let start = !i in
      while
        !i < n && (not (is_space s.[!i])) && s.[!i] <> '(' && s.[!i] <> ')'
      do
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
    | ")" :: rest ->
        toks := rest;
        List.rev acc
    | [] -> failwith "ast_driver: unterminated list"
    | _ ->
        let e = one () in
        list (e :: acc)
  in
  one ()

(* -- sexp -> exported AST constructors ----------------------------------- *)

open Voblint

let int_of_atom s = Int_of_integer (Z.of_string s)

(* The parser labels a check with its own source position, which a generated
   AST cannot know before it is printed; round-trips compare modulo labels. *)
let unlabelled = (nat_of_integer Z.zero, nat_of_integer Z.zero)

let rec erase_labels = function
  | Check (a, _, e) -> Check (a, unlabelled, e)
  | Seq (c1, c2) -> Seq (erase_labels c1, erase_labels c2)
  | If (a, b, c1, c2) -> If (a, b, erase_labels c1, erase_labels c2)
  | While (a, b, c) -> While (a, b, erase_labels c)
  | c -> c

let erase_program_labels prog =
  let proc f =
    match prog_table prog f with
    | Some (Gproc_decl_ext (formals, body, ())) ->
        (f, Gproc_decl_ext (formals, erase_labels body, ()))
    | None -> failwith ("ast_driver: undeclared procedure " ^ f)
  in
  mk_program
    (List.map proc (prog_procs prog))
    (erase_labels (prog_main prog))
    (declared_global_vars prog)

let rec build_exp = function
  | Slist [ Atom "N"; Atom n ] -> N (int_of_atom n)
  | Slist [ Atom "V"; Atom x ] -> V x
  | Slist [ Atom "Plus"; a; b ] -> Plus (build_exp a, build_exp b)
  | Slist [ Atom "Minus"; a; b ] -> Minus (build_exp a, build_exp b)
  | Slist [ Atom "Times"; a; b ] -> Times (build_exp a, build_exp b)
  | Slist [ Atom "Div"; a; b ] -> Div (build_exp a, build_exp b)
  | Slist [ Atom "Mod"; a; b ] -> Mod (build_exp a, build_exp b)
  | Slist [ Atom "Less"; a; b ] -> Less (build_exp a, build_exp b)
  | Slist [ Atom "LessEq"; a; b ] -> LessEq (build_exp a, build_exp b)
  | Slist [ Atom "Greater"; a; b ] -> Greater (build_exp a, build_exp b)
  | Slist [ Atom "GreaterEq"; a; b ] -> GreaterEq (build_exp a, build_exp b)
  | Slist [ Atom "NotEq"; a; b ] -> NotEq (build_exp a, build_exp b)
  | Slist [ Atom "Eq"; a; b ] -> Eq (build_exp a, build_exp b)
  | Slist [ Atom "Not"; a ] -> Not (build_exp a)
  | Slist [ Atom "And"; a; b ] -> And (build_exp a, build_exp b)
  | Slist [ Atom "Or"; a; b ] -> Or (build_exp a, build_exp b)
  | Slist [ Atom "Cast"; Atom k; a ] -> Cast (build_kind k, build_exp a)
  | s -> failwith ("ast_driver: bad exp sexp: " ^ show_sexp s)

and build_kind = function
  | "i8" -> I8
  | "u8" -> U8
  | "i16" -> I16
  | "u16" -> U16
  | "i32" -> I32
  | "u32" -> U32
  | "i64" -> I64
  | "u64" -> U64
  | k -> failwith ("ast_driver: bad kind: " ^ k)

and build_exp_opt = function
  | Atom "None" -> None
  | Slist [ Atom "Some"; a ] -> Some (build_exp a)
  | s -> failwith ("ast_driver: bad exp option sexp: " ^ show_sexp s)

and build_dst_opt = function
  | Atom "None" -> None
  | Slist [ Atom "Some"; Atom x ] -> Some x
  | s -> failwith ("ast_driver: bad dst option sexp: " ^ show_sexp s)

and build_actuals = function
  | Slist es -> List.map build_exp es
  | s -> failwith ("ast_driver: bad actuals sexp: " ^ show_sexp s)

and build_com = function
  | Atom "Skip" -> SKIP ()
  | Slist [ Atom "Assign"; Atom x; a ] -> Assign ((), x, build_exp a)
  | Slist [ Atom "Random"; Atom x ] ->
      Call ((), Some x, "__voblint_nondet_int", [])
  | Slist [ Atom "Check"; b ] -> Check ((), unlabelled, build_exp b)
  | Slist [ Atom "Seq"; c1; c2 ] -> Seq (build_com c1, build_com c2)
  | Slist [ Atom "If"; b; c1; c2 ] ->
      If ((), build_exp b, build_com c1, build_com c2)
  | Slist [ Atom "While"; b; c ] -> While ((), build_exp b, build_com c)
  | Slist [ Atom "Call"; dst; Atom p; actuals ] ->
      Call ((), build_dst_opt dst, p, build_actuals actuals)
  | Slist [ Atom "Return"; aopt ] -> Return ((), build_exp_opt aopt)
  | s -> failwith ("ast_driver: bad com sexp: " ^ show_sexp s)

and show_sexp = function
  | Atom s -> s
  | Slist ss -> "(" ^ String.concat " " (List.map show_sexp ss) ^ ")"

let build_names = function
  | Slist atoms ->
      List.map
        (function Atom s -> s | s -> failwith ("bad name: " ^ show_sexp s))
        atoms
  | s -> failwith ("ast_driver: bad name list sexp: " ^ show_sexp s)

(* ((x k) ...): names with their kinds. *)
let build_typed = function
  | Slist entries ->
      List.map
        (function
          | Slist [ Atom x; Atom k ] -> (x, build_kind k)
          | s -> failwith ("ast_driver: bad typed name: " ^ show_sexp s))
        entries
  | s -> failwith ("ast_driver: bad typed list sexp: " ^ show_sexp s)

let scoped proc = List.map (fun (x, k) -> (ScopedId (proc, x), k))

(* (name ret formals locals body), ret None or a kind. *)
let build_proc = function
  | Slist [ Atom name; ret; formals; locals; body ] ->
      let formals = build_typed formals and locals = build_typed locals in
      let ret =
        match ret with
        | Atom "None" -> []
        | Atom k -> [ (ReturnId name, build_kind k) ]
        | s -> failwith ("ast_driver: bad return kind: " ^ show_sexp s)
      in
      ( (name, Gproc_decl_ext (List.map fst formals, build_com body, ())),
        scoped name formals @ scoped name locals @ ret )
  | s -> failwith ("ast_driver: bad proc sexp: " ^ show_sexp s)

(* (procs (main_locals main_body) globals): the program and its kind
   declarations. *)
let build_program = function
  | Slist [ Slist procs; Slist [ main_locals; main_body ]; globals ] ->
      let procs = List.map build_proc procs and globals = build_typed globals in
      ( mk_program (List.map fst procs) (build_com main_body)
          (List.map fst globals),
        List.map (fun (g, k) -> (GlobalId g, k)) globals
        @ scoped "main" (build_typed main_locals)
        @ List.concat_map snd procs )
  | s -> failwith ("ast_driver: bad program sexp: " ^ show_sexp s)

(* -- Driver --------------------------------------------------------------- *)

let source_text_of_program decls = Vimp_printer.string_of_imp_prog ~decls
let mode = if Array.length Sys.argv > 1 then Sys.argv.(1) else ""

let () =
  let input = In_channel.input_all stdin in
  try
    let original, decls = build_program (parse_sexp input) in
    let source_text = source_text_of_program decls original in
    if mode = "--print-source" then (
      print_string source_text;
      exit 0);
    match Vimp_frontend.program "<generated>" source_text with
    | reparsed, reparsed_decls, _, _ when mode = "--print-reprinted" ->
        (* Prints pretty(parse(pretty(original))) -- the print/parse/print
         invariant is implied by original = reparsed (the printer
         is a pure function, so structurally equal ASTs print identically),
         but checking it directly gives a source-text diff on failure instead
         of "the trees differ", and catches the (structural-equality
         assumption) breaking silently. *)
        print_string (source_text_of_program reparsed_decls reparsed);
        exit 0
    | reparsed, reparsed_decls, _, _ ->
        if
          erase_program_labels original = erase_program_labels reparsed
          && List.sort compare decls = List.sort compare reparsed_decls
        then print_endline "OK"
        else begin
          Printf.printf
            "FAIL round-trip mismatch\n\
             --- generated source ---\n\
             %s\n\
             --- end ---\n"
            source_text;
          exit 1
        end
    | exception Vimp_frontend.Parse_error { line; col; msg; _ }
      when mode = "--print-reprinted" ->
        Printf.printf "FAIL re-parse error at %d:%d: %s\n" line col msg;
        exit 1
    | exception Vimp_frontend.Parse_error { line; col; msg; _ } ->
        Printf.printf
          "FAIL re-parse error at %d:%d: %s\n\
           --- generated source ---\n\
           %s\n\
           --- end ---\n"
          line col msg source_text;
        exit 1
  with
  | Failure msg ->
      Printf.printf "FAIL driver error: %s\n" msg;
      exit 1
  | e ->
      Printf.printf "FAIL unexpected exception: %s\n" (Printexc.to_string e);
      exit 1
