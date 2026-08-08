(* Regression driver for the generated Voblint_Analyse OCaml module.
   Constructs a VIMP program purely through the exported AST constructors
   (never touching Isabelle), runs it through the exported `analyse`
   dispatcher for both domains, and checks the result against the values
   already proved inside Isabelle by
   src/Examples/Mixed/Example_Analysis_Dispatch.thy's
   dispatch_demo_sign_unknown / dispatch_demo_interval_precise lemmas.

   Do not hand-edit codegen/generated/Voblint_Analyse_OCaml.ocaml; regenerate
   it with `make codegen` instead. *)

open Voblint_Analyse_OCaml.Voblint_Analyse

(* `HOL-Library.Code_Target_Numeral` (imported by Example_Analysis_Dispatch)
   backs Isabelle's `int`/`nat` by the target language's native
   arbitrary-precision integer -- Zarith's `Z.t` on the OCaml side -- so
   construction/inspection go through `Int_of_integer`/`nat_of_integer` and
   their inverses rather than walking a `num`/Peano-successor term. *)
let mk_int n = Int_of_integer (Z.of_int n)

let mk_nat n = nat_of_integer (Z.of_int n)

(* `vname`/`pname` are Isabelle's `String.literal`, which is already OCaml's
   native `string` (see Example_Analysis_Dispatch.thy), so variable/procedure
   names need no conversion at all. *)

(* y := 1; check(0 < y); y := 0 - 1; check(0 < y)
   Same program as dispatch_demo_prog in Example_Analysis_Dispatch.thy. *)
let check_cond = Less (N (mk_int 0), V "y")

let demo_prog =
  make []
    (Seq
       (Seq
          (Seq (Assign ("y", N (mk_int 1)), Check check_cond),
           Assign ("y", Minus (N (mk_int 0), N (mk_int 1))))
       , Check check_cond))
    []

let expected_sign =
  [ (Statement (mk_nat 1), (check_cond, Check_Unknown));
    (Statement (mk_nat 3), (check_cond, Check_Unknown)) ]

let expected_interval =
  [ (Statement (mk_nat 1), (check_cond, Check_Proved));
    (Statement (mk_nat 3), (check_cond, Check_Refuted)) ]

let show_int i = Z.to_string (integer_of_int i)

let rec show_aexp = function
  | N i -> show_int i
  | V s -> s
  | Plus (a, b) -> "(" ^ show_aexp a ^ " + " ^ show_aexp b ^ ")"
  | Minus (a, b) -> "(" ^ show_aexp a ^ " - " ^ show_aexp b ^ ")"
  | Times (a, b) -> "(" ^ show_aexp a ^ " * " ^ show_aexp b ^ ")"

let rec show_bexp = function
  | Bc b -> string_of_bool b
  | Not b -> "!" ^ show_bexp b
  | And (a, b) -> "(" ^ show_bexp a ^ " && " ^ show_bexp b ^ ")"
  | Or (a, b) -> "(" ^ show_bexp a ^ " || " ^ show_bexp b ^ ")"
  | Less (a, b) -> "(" ^ show_aexp a ^ " < " ^ show_aexp b ^ ")"
  | Eqa (a, b) -> "(" ^ show_aexp a ^ " == " ^ show_aexp b ^ ")"

let show_check_result = function
  | Check_Proved -> "Check_Proved"
  | Check_Refuted -> "Check_Refuted"
  | Check_Unknown -> "Check_Unknown"

let show_nat n = Z.to_string (integer_of_nat n)

let show_entry (n, (b, r)) =
  Printf.sprintf "(%s, %s, %s)"
    (match n with
     | Statement k -> "Statement " ^ show_nat k
     | FunctionEntry s -> "FunctionEntry " ^ s
     | FunctionResult s -> "FunctionResult " ^ s)
    (show_bexp b) (show_check_result r)

let check_case label actual expected =
  if actual = expected then (
    print_endline ("OK   " ^ label);
    true)
  else (
    print_endline ("FAIL " ^ label);
    print_endline ("  expected: " ^ String.concat "; " (List.map show_entry expected));
    print_endline ("  actual:   " ^ String.concat "; " (List.map show_entry actual));
    false)

let () =
  let actual_sign = analyse Sign_Analysis demo_prog in
  let actual_interval = analyse Interval_Analysis demo_prog in
  let ok_sign = check_case "Sign_Analysis demo report" actual_sign expected_sign in
  let ok_interval = check_case "Interval_Analysis demo report" actual_interval expected_interval in
  if ok_sign && ok_interval then print_endline "All regression checks passed."
  else exit 1
