(* Property-test oracle driver: reads an S-expression-encoded imp_prog AST
   from stdin, builds it via the exported Isabelle constructors (NOT via
   Vimp_parser -- the whole point is an independently-constructed AST, so a
   parser bug can't hide by round-tripping consistently with itself), prints
   it through the Isabelle-generated pretty_string_of_program, completes the
   declarations that printer leaves out (see "Declaration completion" below),
   re-parses that text with Vimp_parser, and checks the result is structurally
   equal
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

let rec build_exp = function
  | Slist [ Atom "N"; Atom n ] -> N (int_of_atom n)
  | Slist [ Atom "V"; Atom x ] -> V x
  | Slist [ Atom "Plus"; a; b ] -> Plus (build_exp a, build_exp b)
  | Slist [ Atom "Minus"; a; b ] -> Minus (build_exp a, build_exp b)
  | Slist [ Atom "Times"; a; b ] -> Times (build_exp a, build_exp b)
  | Slist [ Atom "Less"; a; b ] -> Less (build_exp a, build_exp b)
  | Slist [ Atom "Eq"; a; b ] -> Eq (build_exp a, build_exp b)
  | Slist [ Atom "Not"; a ] -> Not (build_exp a)
  | Slist [ Atom "And"; a; b ] -> And (build_exp a, build_exp b)
  | Slist [ Atom "Or"; a; b ] -> Or (build_exp a, build_exp b)
  | s -> failwith ("ast_driver: bad exp sexp: " ^ show_sexp s)

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
  | Atom "Skip" -> SKIP
  | Slist [ Atom "Assign"; Atom x; a ] -> Assign (x, build_exp a)
  | Slist [ Atom "Random"; Atom x ] -> Call (Some x, "__voblint_nondet_int", [])
  | Slist [ Atom "Check"; b ] -> Check (build_exp b)
  | Slist [ Atom "Seq"; c1; c2 ] -> Seq (build_com c1, build_com c2)
  | Slist [ Atom "If"; b; c1; c2 ] -> If (build_exp b, build_com c1, build_com c2)
  | Slist [ Atom "While"; b; c ] -> While (build_exp b, build_com c)
  | Slist [ Atom "Call"; dst; Atom p; actuals ] ->
    Call (build_dst_opt dst, p, build_actuals actuals)
  | Slist [ Atom "Return"; aopt ] -> Return (build_exp_opt aopt)
  | s -> failwith ("ast_driver: bad com sexp: " ^ show_sexp s)

and show_sexp = function
  | Atom s -> s
  | Slist ss -> "(" ^ String.concat " " (List.map show_sexp ss) ^ ")"

let build_names = function
  | Slist atoms -> List.map (function Atom s -> s | s -> failwith ("bad name: " ^ show_sexp s)) atoms
  | s -> failwith ("ast_driver: bad name list sexp: " ^ show_sexp s)

let build_proc = function
  | Slist [ Atom name; formals; body ] -> (name, build_names formals, build_com body)
  | s -> failwith ("ast_driver: bad proc sexp: " ^ show_sexp s)

(* The sexp describes a program the way the printer prints one: procedures and
   a main body, with no declarations. Completion below turns that skeleton into
   both a fully declared AST and the matching source text. *)
let build_skeleton = function
  | Slist [ Slist procs; main_body; globals ] ->
    (List.map build_proc procs, build_com main_body, build_names globals)
  | s -> failwith ("ast_driver: bad program sexp: " ^ show_sexp s)

(* -- Declaration completion ----------------------------------------------

   Every declaration in VIMP is explicit: a global and a formal each carry a
   kind, a value-returning procedure declares its return kind, and every other
   variable a body touches is a declared local. pretty_string_of_program prints
   none of that -- its output is a declaration skeleton -- so a printed program
   is not source the frontend accepts until the declarations are put back.

   One fixed kind is used throughout: which kind a declaration carries is not
   what these properties are about, and holding it constant keeps the AST the
   text re-parses to exactly the AST that was printed. Locals are the variables
   a body uses that are neither globals nor its own formals, in first-use
   order; a procedure gets a return kind exactly when its body returns a value.
   Both the tree and the text are built from this one derivation, so they
   cannot drift apart. *)

let decl_kind = I32
let decl_kind_text = "int32"

let rec exp_vars acc = function
  | V x -> x :: acc
  | N _ -> acc
  | Plus (a, b) | Minus (a, b) | Times (a, b) | Less (a, b) | Eq (a, b)
  | And (a, b) | Or (a, b) -> exp_vars (exp_vars acc a) b
  | Not a -> exp_vars acc a

(* A call's callee is a Call field, never a V, so a procedure name is never
   counted as a variable here -- and neither are the specials, which are
   calls too. *)
let rec com_vars acc = function
  | SKIP | Restore | Unwind -> acc
  | Assign (x, e) -> exp_vars (x :: acc) e
  | Check e -> exp_vars acc e
  | Seq (a, b) -> com_vars (com_vars acc a) b
  | If (e, a, b) -> com_vars (com_vars (exp_vars acc e) a) b
  | While (e, a) -> com_vars (exp_vars acc e) a
  | Call (dst, _, args) ->
    List.fold_left exp_vars (match dst with Some x -> x :: acc | None -> acc) args
  | Return (Some e) -> exp_vars acc e
  | Return None -> acc

let rec returns_value = function
  | Return e -> e <> None
  | Seq (a, b) | If (_, a, b) -> returns_value a || returns_value b
  | While (_, a) -> returns_value a
  | SKIP | Assign _ | Check _ | Call _ | Restore | Unwind -> false

(* A procedure declares a return kind only when it delivers a value on every
   path that can leave it, which is the contract the frontend enforces. The
   "some path returns" form above is the wrong test for that: an if that
   returns from one arm only would be declared value-returning and then
   rejected. A loop never counts, since it may not be entered. *)
let rec always_returns_value = function
  | Return e -> e <> None
  | Seq (a, b) -> always_returns_value a || always_returns_value b
  | If (_, a, b) -> always_returns_value a && always_returns_value b
  | While _ -> false
  | SKIP | Assign _ | Check _ | Call _ | Restore | Unwind -> false

let rec dedup = function
  | [] -> []
  | x :: rest -> x :: dedup (List.filter (fun y -> y <> x) rest)

type definition = {
  d_name : string;
  d_formals : string list;
  d_locals : string list;
  d_ret : ikind option;
  d_body : com;
}

(* main is never value-returning: mk_program_typed builds its entry with
   proc_decl_of [] and the frontend leaves "main may not return" to
   wf_program_compile_input_exec, so a generated main keeps the void form
   whatever its body does. *)
let definition_of globals is_main (name, formals, body) =
  let used = dedup (List.rev (com_vars [] body)) in
  { d_name = name;
    d_formals = formals;
    d_locals =
      List.filter (fun x -> not (List.mem x globals || List.mem x formals)) used;
    d_ret = (if (not is_main) && always_returns_value body then Some decl_kind else None);
    d_body = body }

(* Definitions in printed order: pretty_string_of_program emits the globals
   line, then prog_procs in order, then main. *)
let definitions_of (procs, main_body, globals) =
  List.map (definition_of globals false) procs
  @ [ definition_of globals true (prog_main_name, [], main_body) ]

let program_of (_, main_body, globals) defs =
  let proc_defs = List.filter (fun d -> d.d_name <> prog_main_name) defs in
  let entry d =
    match d.d_ret with
    | None -> (d.d_name, proc_decl_of d.d_formals d.d_body)
    | Some k -> (d.d_name, proc_decl_of_typed d.d_formals k d.d_body)
  in
  (* Mirrors the parser's own kind environment: globals, formals *and*
     locals. A local's declared kind has to reach compilation, so the parser
     puts it here; a driver that left it out would build an AST the parser
     never produces and the round trip would compare unequal things. *)
  let kinds =
    List.map (fun g -> TV (g, decl_kind)) globals
    @ List.concat_map
        (fun d -> List.map (fun x -> TV (x, decl_kind)) d.d_formals)
        defs
    @ List.concat_map
        (fun d -> List.map (fun x -> TV (x, decl_kind)) d.d_locals)
        defs
  in
  (* Annotated formals are scoped alongside the locals, exactly as the parser
     records them: every formal the printer emits carries a kind, so every
     formal reaches the scoped table too. *)
  let scoped_decls =
    List.concat_map
      (fun d ->
         List.map (fun x -> (d.d_name, TV (x, decl_kind))) d.d_formals
         @ List.map (fun x -> (d.d_name, TV (x, decl_kind))) d.d_locals)
      defs
  in
  mk_program_typed (List.map entry proc_defs) main_body globals kinds scoped_decls

(* -- Declaration completion, on the printed text -------------------------

   The printer writes the globals line and every procedure header at column
   zero and indents every body line, so those two line shapes locate the
   places a declaration belongs without parsing the text back. Headers arrive
   in the same order `definitions_of` produced. *)

(* -- Driver --------------------------------------------------------------- *)

(* The printer emits strict source: a kind on every global and formal, a
   return kind on every procedure, and each procedure's locals as a prologue.
   Nothing is spliced in afterwards, so what the parser reads back is exactly
   what the printer produced -- which is what makes this an AST -> print ->
   parse round trip rather than a comparison against a repaired text. *)
let source_text_of_program _defs original =
  let source_chars =
    pretty_string_of_program
      (prog_tyenv original) (declared_scoped original)
      (prog_table original) (prog_procs original) (prog_main original)
      (declared_global_vars original)
  in
  String.concat ""
    (List.map
       (fun c -> String.make 1 (Char.chr (Z.to_int (integer_of_char c))))
       source_chars)


let mode = if Array.length Sys.argv > 1 then Sys.argv.(1) else ""

let () =
  let input = In_channel.input_all stdin in
  try
    let skeleton = build_skeleton (parse_sexp input) in
    let defs = definitions_of skeleton in
    let original = program_of skeleton defs in
    let source_text = source_text_of_program defs original in
    if mode = "--print-source" then (print_string source_text; exit 0);
    match Vimp_frontend.program "<generated>" source_text with
    | reparsed, _, _ when mode = "--print-reprinted" ->
      (* Prints pretty(parse(pretty(original))) -- the print/parse/print
         invariant is implied by original = reparsed (pretty_string_of_program
         is a pure function, so structurally equal ASTs print identically),
         but checking it directly gives a source-text diff on failure instead
         of "the trees differ", and catches the (structural-equality
         assumption) breaking silently. *)
      print_string (source_text_of_program defs reparsed);
      exit 0
    | reparsed, _, _ ->
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
