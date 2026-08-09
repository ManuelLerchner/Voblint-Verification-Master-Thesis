(* Validates aexp_paren (grammar/vimp.yaml) end to end for arbitrary (not
   just left-associated) aexp trees -- the capability the pre-cutover
   grammar structurally couldn't have; see paren_strategies.py's docstring
   for why this needs its own generator/printer rather than reusing
   ast_driver's S-expression route (pretty_string_of_program, VIMP_Source_
   Print.thy, still can't parenthesize -- only the Python-side printer here
   can, so only source built by that printer can exercise this).

   Reads one line of VIMP source on stdin, already wrapped by the Python
   side as "void main() { x := <aexp> }" (paren_strategies.print_aexp
   supplies the parenthesized <aexp> text). Parses with the shipped
   grammar, pulls the aexp back out of the resulting Assign, and prints it
   back out as an s-expression in the exact format strategies.py's sexp()
   produces -- so the Python side can compare the parsed-back tree against
   its own generator input by plain string equality, no second parser
   needed on the Python side. *)

let rec aexp_to_sexp = function
  | Voblint_CLI.Core.N (Voblint_CLI.Core.Int_of_integer z) -> Printf.sprintf "(N %s)" (Z.to_string z)
  | Voblint_CLI.Core.V x -> Printf.sprintf "(V %s)" x
  | Voblint_CLI.Core.Plus (a, b) -> Printf.sprintf "(Plus %s %s)" (aexp_to_sexp a) (aexp_to_sexp b)
  | Voblint_CLI.Core.Minus (a, b) -> Printf.sprintf "(Minus %s %s)" (aexp_to_sexp a) (aexp_to_sexp b)
  | Voblint_CLI.Core.Times (a, b) -> Printf.sprintf "(Times %s %s)" (aexp_to_sexp a) (aexp_to_sexp b)

let () =
  let src = In_channel.input_all stdin in
  try
    let prog = Vimp_parser.program Vimp_lexer.token (Lexing.from_string src) in
    match Voblint_CLI.Core.prog_main prog with
    | Voblint_CLI.Core.Assign (_, a) -> print_string (aexp_to_sexp a)
    | _ -> Printf.printf "FAIL unexpected main shape\n"; exit 1
  with e ->
    Printf.printf "FAIL %s\n--- source ---\n%s\n--- end ---\n" (Printexc.to_string e) src;
    exit 1
