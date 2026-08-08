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

(* Isabelle's `num`/`int`/`nat` are unbounded unary/binary encodings with no
   native-int bridge in the generated code, so small literals are built by
   hand here rather than exported from Isabelle. *)
let rec mk_num = function
  | 1 -> One
  | n when n mod 2 = 0 -> Bit0 (mk_num (n / 2))
  | n -> Bit1 (mk_num (n / 2))

let mk_int = function
  | 0 -> int_zero
  | n when n > 0 -> Pos (mk_num n)
  | n -> Neg (mk_num (-n))

let rec mk_nat = function
  | 0 -> nat_zero
  | n -> Suc (mk_nat (n - 1))

(* `vname = char list` uses Isabelle's own bit-vector `char` (`Chara` in
   OCaml), not OCaml's native `char`, with bit 0 as the least-significant
   bit -- confirmed by decoding the generated `ret_var` constant from the
   Haskell output to "#ret". *)
let mk_char c =
  let n = Char.code c in
  let bit i = n land (1 lsl i) <> 0 in
  Chara (bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

let mk_string s = List.init (String.length s) (fun i -> mk_char s.[i])

let un_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  let bit i b = if b then 1 lsl i else 0 in
  Char.chr (bit 0 b0 lor bit 1 b1 lor bit 2 b2 lor bit 3 b3 lor bit 4 b4
            lor bit 5 b5 lor bit 6 b6 lor bit 7 b7)

let un_string cs = String.init (List.length cs) (fun i -> un_char (List.nth cs i))

(* y := 1; check(0 < y); y := 0 - 1; check(0 < y)
   Same program as dispatch_demo_prog in Example_Analysis_Dispatch.thy. *)
let check_cond = Less (N (mk_int 0), V (mk_string "y"))

let demo_prog =
  make []
    (Seq
       (Seq
          (Seq (Assign (mk_string "y", N (mk_int 1)), Check check_cond),
           Assign (mk_string "y", Minus (N (mk_int 0), N (mk_int 1))))
       , Check check_cond))
    []

let expected_sign =
  [ (Statement (mk_nat 1), (check_cond, Check_Unknown));
    (Statement (mk_nat 3), (check_cond, Check_Unknown)) ]

let expected_interval =
  [ (Statement (mk_nat 1), (check_cond, Check_Proved));
    (Statement (mk_nat 3), (check_cond, Check_Refuted)) ]

let rec show_num n =
  match n with
  | One -> "1"
  | Bit0 m -> string_of_int (2 * int_of_string (show_num m))
  | Bit1 m -> string_of_int ((2 * int_of_string (show_num m)) + 1)

let show_int = function
  | Zero_int -> "0"
  | Pos n -> show_num n
  | Neg n -> "-" ^ show_num n

let rec show_aexp = function
  | N i -> show_int i
  | V s -> un_string s
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

let rec show_nat = function
  | Zero_nat -> "0"
  | Suc n -> string_of_int (1 + int_of_string (show_nat n))

let show_entry (n, (b, r)) =
  Printf.sprintf "(%s, %s, %s)"
    (match n with
     | Statement k -> "Statement " ^ show_nat k
     | FunctionEntry s -> "FunctionEntry " ^ un_string s
     | FunctionResult s -> "FunctionResult " ^ un_string s)
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
