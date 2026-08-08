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

(* `string_of_bexp` renders a check's condition directly, as an alternative
   to pattern-matching the `bexp` AST. Its Isabelle return type is `string`
   (`char list`), and `char` is still the opaque Code_Abstract_Char type
   here (only `vname`/`pname` moved to native `String.literal`), so the
   result needs the same `integer_of_char` bridge as everywhere else `char`
   is inspected directly -- and OCaml's `string`/`char list` are distinct
   types besides, unlike Haskell's `type String = [Char]` pun. *)
let un_char c = Char.chr (Z.to_int (integer_of_char c))
let un_string cs = String.concat "" (List.map (fun c -> String.make 1 (un_char c)) cs)

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

(* global `total`, procedure `inc` with formal `n`, two calls, two checks.
   Exercises `make`'s procedure list, `proc_decl_of`'s formals, and `Call`
   together -- not just straight-line assignment/check.
   Same program as proc_demo_prog in Example_Analysis_Dispatch.thy; checked
   against proc_demo_sign_unknown / proc_demo_cfg_intra / proc_demo_cfg_calls.
   Interval_Analysis on this program used to hang/segfault under the always-join backend (a
   flow-insensitive global read-and-grow has no widening there); the exported `analyse`
   dispatcher now routes Interval through the warrowing backend, which terminates (at
   Check_Unknown precision) -- see Example_Analysis_Dispatch.thy's proc_demo_interval_terminates. *)
let proc_demo_prog =
  make
    [ ("inc", proc_decl_of ["n"] (Assign ("total", Plus (V "total", V "n")))) ]
    (Seq
       (Seq
          (Seq
             (Seq (Assign ("total", N (mk_int 0)), Call (None, "inc", [ N (mk_int 3) ])),
              Call (None, "inc", [ N (mk_int 4) ])),
           Check (Less (N (mk_int 0), V "total"))),
        Check (Less (V "total", N (mk_int 100)))))
    [ "total" ]

let expected_proc_demo_sign =
  [ (Statement (mk_nat 5), (Less (N (mk_int 0), V "total"), Check_Unknown));
    (Statement (mk_nat 6), (Less (V "total", N (mk_int 100)), Check_Unknown)) ]

(* Same shape as expected_proc_demo_sign, but this is the case that used to hang: a global read
   and grown across two calls, now solved via warrowing (Check_Unknown, not a crash). *)
let expected_proc_demo_interval =
  [ (Statement (mk_nat 5), (Less (N (mk_int 0), V "total"), Check_Unknown));
    (Statement (mk_nat 6), (Less (V "total", N (mk_int 100)), Check_Unknown)) ]

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

(* Compact renderers matching string_of_cfg_node/string_of_action/
   string_of_call_action in Analysis_GraphViz.thy exactly (no spaces around
   infix operators, "pp"/"entry_"/"result_" node prefixes) -- deliberately
   not show_aexp/show_bexp above, which use the driver's own spaced format
   for the straight-line demo's own display purposes. *)
let show_cfg_node_compact = function
  | Statement n -> "pp" ^ show_nat n
  | FunctionEntry s -> "entry_" ^ s
  | FunctionResult s -> "result_" ^ s

let rec show_aexp_compact = function
  | N i -> show_int i
  | V s -> s
  | Plus (a, b) -> "(" ^ show_aexp_compact a ^ "+" ^ show_aexp_compact b ^ ")"
  | Minus (a, b) -> "(" ^ show_aexp_compact a ^ "-" ^ show_aexp_compact b ^ ")"
  | Times (a, b) -> "(" ^ show_aexp_compact a ^ "*" ^ show_aexp_compact b ^ ")"

let rec show_bexp_compact = function
  | Bc b -> string_of_bool b
  | Not b -> "!(" ^ show_bexp_compact b ^ ")"
  | And (a, b) -> "(" ^ show_bexp_compact a ^ "&&" ^ show_bexp_compact b ^ ")"
  | Or (a, b) -> "(" ^ show_bexp_compact a ^ "||" ^ show_bexp_compact b ^ ")"
  | Less (a, b) -> show_aexp_compact a ^ "<" ^ show_aexp_compact b
  | Eqa (a, b) -> show_aexp_compact a ^ "==" ^ show_aexp_compact b

let show_edge_action = function
  | EA_Nop -> "nop"
  | EA_Assign (x, a) -> x ^ " := " ^ show_aexp_compact a
  | EA_Random x -> x ^ " := random()"
  | EA_Assume b -> "[" ^ show_bexp_compact b ^ "]"
  | EA_AssumeNot b -> "![" ^ show_bexp_compact b ^ "]"
  | EA_Ret (None, _) -> "return"
  | EA_Ret (Some e, _) -> "return " ^ show_aexp_compact e
  | EA_Check b -> "check(" ^ show_bexp_compact b ^ ")"

let show_call_action = function
  | CallEdge (None, _, es) -> "call(" ^ String.concat "" (List.map show_aexp_compact es) ^ ")"
  | CallEdge (Some x, _, es) ->
    x ^ " := call(" ^ String.concat "" (List.map show_aexp_compact es) ^ ")"

let show_intra_list es =
  String.concat "; "
    (List.map
       (fun (u, (a, v)) ->
         show_cfg_node_compact u ^ " --[" ^ show_edge_action a ^ "]--> "
         ^ show_cfg_node_compact v)
       es)

let show_calls_list es =
  String.concat "; "
    (List.map
       (fun (call, (ca, (entry, cont))) ->
         show_cfg_node_compact call ^ " --[" ^ show_call_action ca ^ "]--> "
         ^ show_cfg_node_compact entry ^ " ~cont~> " ^ show_cfg_node_compact cont)
       es)

let expected_proc_demo_intra =
  "pp0 --[total := (total+n)]--> pp1; pp1 --[return]--> result_inc; "
  ^ "pp2 --[total := 0]--> pp3; pp5 --[check(0<total)]--> pp6; "
  ^ "pp6 --[check(total<100)]--> pp7; pp7 --[return]--> result_main; "
  ^ "entry_inc --[nop]--> pp0; entry_main --[nop]--> pp2"

let expected_proc_demo_calls =
  "pp3 --[call(3)]--> entry_inc ~cont~> pp4; pp4 --[call(4)]--> entry_inc ~cont~> pp5"

let check_case label actual expected =
  if actual = expected then (
    print_endline ("OK   " ^ label);
    true)
  else (
    print_endline ("FAIL " ^ label);
    print_endline ("  expected: " ^ String.concat "; " (List.map show_entry expected));
    print_endline ("  actual:   " ^ String.concat "; " (List.map show_entry actual));
    false)

let check_case_str label actual expected =
  if actual = expected then (
    print_endline ("OK   " ^ label);
    true)
  else (
    print_endline ("FAIL " ^ label);
    print_endline ("  expected: " ^ expected);
    print_endline ("  actual:   " ^ actual);
    false)

let () =
  let actual_sign = analyse Sign_Analysis demo_prog in
  let actual_interval = analyse Interval_Analysis demo_prog in
  let actual_proc_demo_sign = analyse Sign_Analysis proc_demo_prog in
  let actual_proc_demo_interval = analyse Interval_Analysis proc_demo_prog in
  let proc_demo_cfg = prog_cfg prog_main_name proc_demo_prog in
  let actual_proc_demo_intra = show_intra_list (cfg_intra_list proc_demo_cfg) in
  let actual_proc_demo_calls = show_calls_list (cfg_calls_list proc_demo_cfg) in
  let ok_sign = check_case "Sign_Analysis demo report" actual_sign expected_sign in
  let ok_interval = check_case "Interval_Analysis demo report" actual_interval expected_interval in
  let ok_proc_demo_sign =
    check_case "Sign_Analysis proc_demo report" actual_proc_demo_sign expected_proc_demo_sign
  in
  let ok_proc_demo_interval =
    check_case "Interval_Analysis proc_demo report (warrowing, was hanging)"
      actual_proc_demo_interval expected_proc_demo_interval
  in
  let ok_proc_demo_intra =
    check_case_str "proc_demo CFG intra edges" actual_proc_demo_intra expected_proc_demo_intra
  in
  let ok_proc_demo_calls =
    check_case_str "proc_demo CFG calls edges" actual_proc_demo_calls expected_proc_demo_calls
  in
  let ok_check_cond_rendered =
    check_case_str "string_of_bexp check condition" (un_string (string_of_bexp check_cond)) "0<y"
  in
  if
    ok_sign && ok_interval && ok_proc_demo_sign && ok_proc_demo_interval && ok_proc_demo_intra
    && ok_proc_demo_calls && ok_check_cond_rendered
  then print_endline "All regression checks passed."
  else exit 1
