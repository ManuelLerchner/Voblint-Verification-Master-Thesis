(* Regression driver for the generated Voblint_CLI OCaml module.
   Constructs a VIMP program purely through the exported AST constructors
   (never touching Isabelle), runs it through the exported `analyse`
   dispatcher for both domains, and checks the result against the values
   already proved inside Isabelle by
   src/Examples/Regression/Example_Analysis_Dispatch_Regression.thy's
   dispatch_demo_sign_precise / dispatch_demo_interval_precise lemmas.

   This reads the same generated module the CLI itself links against. It
   used to read a second, separately exported one (Voblint_Analyse_OCaml),
   which differed only by the CFG-inspection constants below -- those are
   now named in the single export block, so there is one generated artifact
   for one analysis rather than two near-copies of the same machinery.

   Do not hand-edit codegen/generated/ml/Voblint_CLI.ml; regenerate it with
   `pixi run codegen` instead. *)

open Voblint_CLI.Core
open Voblint_CLI.Analyse_Dispatch

(* `HOL-Library.Code_Target_Numeral` (imported by Example_Analysis_Dispatch)
   backs Isabelle's `int`/`nat` by the target language's native
   arbitrary-precision integer -- Zarith's `Z.t` on the OCaml side -- so
   construction/inspection go through `Int_of_integer`/`nat_of_integer` and
   their inverses rather than walking a `num`/Peano-successor term. *)
let mk_int n = Int_of_integer (Z.of_int n)

let mk_nat n = nat_of_integer (Z.of_int n)

(* `vname`/`pname` are Isabelle's `String.literal`, which is already OCaml's
   native `string` (see Example_Analysis_Dispatch_Regression.thy), so variable/procedure
   names need no conversion at all. *)

(* `string_of_exp` renders a check's condition directly, as an alternative
   to pattern-matching the `exp` AST. Its Isabelle return type is `string`
   (`char list`), and `char` is still the opaque Code_Abstract_Char type
   here (only `vname`/`pname` moved to native `String.literal`), so the
   result needs the same `integer_of_char` bridge as everywhere else `char`
   is inspected directly -- and OCaml's `string`/`char list` are distinct
   types besides, unlike Haskell's `type String = [Char]` pun. *)
let un_char c = Char.chr (Z.to_int (integer_of_char c))
let un_string cs = String.concat "" (List.map (fun c -> String.make 1 (un_char c)) cs)

(* y := 1; check(0 < y); y := 0 - 1; check(0 < y)
   Same program as dispatch_demo_prog in Example_Analysis_Dispatch_Regression.thy. *)
let check_cond = Less (N (mk_int 0), V "y")

let demo_prog =
  mk_program []
    (Seq
       (Seq
          (Seq (Assign ("y", N (mk_int 1)), Check check_cond),
           Assign ("y", Minus (N (mk_int 0), N (mk_int 1))))
       , Check check_cond))
    []

let expected_sign =
  [ (Statement (mk_nat 1), (check_cond, Check_Proved));
    (Statement (mk_nat 3), (check_cond, Check_Refuted)) ]

let expected_interval =
  [ (Statement (mk_nat 1), (check_cond, Check_Proved));
    (Statement (mk_nat 3), (check_cond, Check_Refuted)) ]

(* global `total`, procedure `inc` with formal `n`, two calls, two checks.
   Exercises `mk_program`'s procedure list, `proc_decl_of`'s formals, and `Call`
   together -- not just straight-line assignment/check.
   Same program as proc_demo_prog in Example_Analysis_Dispatch_Regression.thy; checked
   against proc_demo_sign_result / proc_demo_cfg_intra / proc_demo_cfg_calls.
   Interval_Analysis on this program used to hang/segfault under the always-join backend (a
   flow-insensitive global read-and-grow has no widening there); the exported `analyse`
   dispatcher now routes Interval through the warrowing backend, which terminates -- see
   Example_Analysis_Dispatch_Regression.thy's proc_demo_interval_terminates. Since the
   Base-style migration, total lives in the reachability-lifted local unknown flow-sensitively
   through both calls, so the first check (0 < total) is Check_Proved; the second
   (total < 100) stays Check_Unknown -- inc's entry is reached by two call sites, so warrowing
   widens the entered parameter's upper bound on the second visit. *)
let proc_demo_prog =
  mk_program
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
  [ (Statement (mk_nat 5), (Less (N (mk_int 0), V "total"), Check_Proved));
    (Statement (mk_nat 6), (Less (V "total", N (mk_int 100)), Check_Unknown)) ]

(* Same shape as expected_proc_demo_sign, but this is the case that used to hang: a global read
   and grown across two calls, now solved via warrowing. *)
let expected_proc_demo_interval =
  [ (Statement (mk_nat 5), (Less (N (mk_int 0), V "total"), Check_Proved));
    (Statement (mk_nat 6), (Less (V "total", N (mk_int 100)), Check_Unknown)) ]

(* Acceptance regression A (no-call global self-feedback): no procedure, no call, just a
   global write that reads its own prior value. Same program as no_call_global_self_ref_prog in
   Example_Analysis_Dispatch_Regression.thy; checked against
   no_call_global_self_ref_interval_terminates. Isolates that the call/return summary was never
   the actual hazard -- a single self-referential global write reproduces it alone. Under the
   Base-style pipeline there is no separate flow-insensitive global summary for total to read
   back through, so the result is Check_Proved. *)
let no_call_global_self_ref_prog =
  mk_program []
    (Seq
       (Seq (Assign ("total", N (mk_int 0)), Assign ("total", Plus (V "total", N (mk_int 3)))),
        Check (Less (N (mk_int 0), V "total"))))
    [ "total" ]

let expected_no_call_global_self_ref_interval =
  [ (Statement (mk_nat 2), (Less (N (mk_int 0), V "total"), Check_Proved)) ]

(* Acceptance regression B (interprocedural global self-feedback): a single call to a
   procedure that reads and grows the same global. Same program as one_call_prog in
   Example_Analysis_Dispatch_Regression.thy; checked against one_call_interval_terminates --
   confirms the fix also survives entry/combine (call/return) handling, not just a
   straight-line write. inc's single call site reaches its entry node once, so no
   repeated-visit widening applies, and total's exact value survives the combine step. *)
let one_call_prog =
  mk_program
    [ ("inc", proc_decl_of ["n"] (Assign ("total", Plus (V "total", V "n")))) ]
    (Seq
       (Seq (Assign ("total", N (mk_int 0)), Call (None, "inc", [ N (mk_int 3) ])),
        Check (Less (N (mk_int 0), V "total"))))
    [ "total" ]

let expected_one_call_interval =
  [ (Statement (mk_nat 4), (Less (N (mk_int 0), V "total"), Check_Proved)) ]

let show_int i = Z.to_string (integer_of_int i)

(* `exp` is one unified integer-valued expression language (no separate
   aexp/bexp split -- see VIMP_Syntax.thy), so a single recursive renderer
   covers arithmetic and comparison/logical constructors alike. *)
let rec show_exp = function
  | N i -> show_int i
  | V s -> s
  | Plus (a, b) -> "(" ^ show_exp a ^ " + " ^ show_exp b ^ ")"
  | Minus (a, b) -> "(" ^ show_exp a ^ " - " ^ show_exp b ^ ")"
  | Times (a, b) -> "(" ^ show_exp a ^ " * " ^ show_exp b ^ ")"
  | Not b -> "!" ^ show_exp b
  | And (a, b) -> "(" ^ show_exp a ^ " && " ^ show_exp b ^ ")"
  | Or (a, b) -> "(" ^ show_exp a ^ " || " ^ show_exp b ^ ")"
  | Less (a, b) -> "(" ^ show_exp a ^ " < " ^ show_exp b ^ ")"
  | Eq (a, b) -> "(" ^ show_exp a ^ " == " ^ show_exp b ^ ")"

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
    (show_exp b) (show_check_result r)

(* Compact renderers matching string_of_cfg_node/string_of_action/
   string_of_call_action in Analysis_GraphViz.thy exactly (no spaces around
   infix operators, "pp"/"entry_"/"result_" node prefixes) -- deliberately
   not show_exp above, which uses the driver's own spaced format for the
   straight-line demo's own display purposes. *)
let show_cfg_node_compact = function
  | Statement n -> "pp" ^ show_nat n
  | FunctionEntry s -> "entry_" ^ s
  | FunctionResult s -> "result_" ^ s

let rec show_exp_compact = function
  | N i -> show_int i
  | V s -> s
  | Plus (a, b) -> "(" ^ show_exp_compact a ^ "+" ^ show_exp_compact b ^ ")"
  | Minus (a, b) -> "(" ^ show_exp_compact a ^ "-" ^ show_exp_compact b ^ ")"
  | Times (a, b) -> "(" ^ show_exp_compact a ^ "*" ^ show_exp_compact b ^ ")"
  | Not b -> "!(" ^ show_exp_compact b ^ ")"
  | And (a, b) -> "(" ^ show_exp_compact a ^ "&&" ^ show_exp_compact b ^ ")"
  | Or (a, b) -> "(" ^ show_exp_compact a ^ "||" ^ show_exp_compact b ^ ")"
  | Less (a, b) -> show_exp_compact a ^ "<" ^ show_exp_compact b
  | Eq (a, b) -> show_exp_compact a ^ "==" ^ show_exp_compact b

let show_edge_action = function
  | EA_Nop -> "nop"
  | EA_Assign (x, a) -> x ^ " := " ^ show_exp_compact a
  | EA_Special (Nondet_Int, x) -> x ^ " := __voblint_nondet_int()"
  | EA_Special (Min (a, b), x) ->
    x ^ " := min(" ^ show_exp_compact a ^ ", " ^ show_exp_compact b ^ ")"
  | EA_Special (Max (a, b), x) ->
    x ^ " := max(" ^ show_exp_compact a ^ ", " ^ show_exp_compact b ^ ")"
  | EA_Assume b -> "[" ^ show_exp_compact b ^ "]"
  | EA_AssumeNot b -> "![" ^ show_exp_compact b ^ "]"
  | EA_Ret (None, _) -> "return"
  | EA_Ret (Some e, _) -> "return " ^ show_exp_compact e
  | EA_Check b -> "check(" ^ show_exp_compact b ^ ")"

let show_call_action = function
  | CallEdge (None, _, es) -> "call(" ^ String.concat "" (List.map show_exp_compact es) ^ ")"
  | CallEdge (Some x, _, es) ->
    x ^ " := call(" ^ String.concat "" (List.map show_exp_compact es) ^ ")"

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

(* [~line] is always [__LINE__] at the call site -- an OCaml builtin
   expanded there, not here, so a FAIL points at the specific
   check_case[_str] call that produced it, not this shared helper.
   [__LOC__] embeds only the filename ocamlopt was invoked with
   ("main.ml", relative to codegen/regression/ocaml/), not clickable once
   back at the repo root this driver is normally run from -- building the
   repo-relative path explicitly instead keeps it clickable there. *)
let driver_path = "codegen/regression/ocaml/main.ml"

let check_case ~line label actual expected =
  if actual = expected then (
    print_endline ("OK   " ^ label);
    true)
  else (
    print_endline (Printf.sprintf "FAIL %s (%s:%d)" label driver_path line);
    print_endline ("  expected: " ^ String.concat "; " (List.map show_entry expected));
    print_endline ("  actual:   " ^ String.concat "; " (List.map show_entry actual));
    false)

let check_case_str ~line label actual expected =
  if actual = expected then (
    print_endline ("OK   " ^ label);
    true)
  else (
    print_endline (Printf.sprintf "FAIL %s (%s:%d)" label driver_path line);
    print_endline ("  expected: " ^ expected);
    print_endline ("  actual:   " ^ actual);
    false)

let () =
  let actual_sign = analyse Sign_Analysis demo_prog in
  let actual_interval = analyse Interval_Analysis demo_prog in
  let actual_proc_demo_sign = analyse Sign_Analysis proc_demo_prog in
  let actual_proc_demo_interval = analyse Interval_Analysis proc_demo_prog in
  let proc_demo_cfg = compile_program proc_demo_prog in
  let actual_proc_demo_intra = show_intra_list (cfg_intra_list proc_demo_cfg) in
  let actual_proc_demo_calls = show_calls_list (cfg_calls_list proc_demo_cfg) in
  let actual_no_call_global_self_ref_interval =
    analyse Interval_Analysis no_call_global_self_ref_prog
  in
  let actual_one_call_interval = analyse Interval_Analysis one_call_prog in
  let ok_sign = check_case ~line:__LINE__ "Sign_Analysis demo report" actual_sign expected_sign in
  let ok_interval =
    check_case ~line:__LINE__ "Interval_Analysis demo report" actual_interval expected_interval
  in
  let ok_proc_demo_sign =
    check_case ~line:__LINE__ "Sign_Analysis proc_demo report" actual_proc_demo_sign
      expected_proc_demo_sign
  in
  let ok_proc_demo_interval =
    check_case ~line:__LINE__ "Interval_Analysis proc_demo report (warrowing, was hanging)"
      actual_proc_demo_interval expected_proc_demo_interval
  in
  let ok_proc_demo_intra =
    check_case_str ~line:__LINE__ "proc_demo CFG intra edges" actual_proc_demo_intra
      expected_proc_demo_intra
  in
  let ok_proc_demo_calls =
    check_case_str ~line:__LINE__ "proc_demo CFG calls edges" actual_proc_demo_calls
      expected_proc_demo_calls
  in
  let ok_no_call_global_self_ref_interval =
    check_case ~line:__LINE__ "Interval_Analysis no-call global self-feedback (acceptance A)"
      actual_no_call_global_self_ref_interval expected_no_call_global_self_ref_interval
  in
  let ok_one_call_interval =
    check_case ~line:__LINE__ "Interval_Analysis interprocedural global self-feedback (acceptance B)"
      actual_one_call_interval expected_one_call_interval
  in
  let ok_check_cond_rendered =
    check_case_str ~line:__LINE__ "string_of_exp check condition"
      (un_string (string_of_exp (mk_nat 0) check_cond)) "0<y"
  in
  if
    ok_sign && ok_interval && ok_proc_demo_sign && ok_proc_demo_interval && ok_proc_demo_intra
    && ok_proc_demo_calls && ok_no_call_global_self_ref_interval && ok_one_call_interval
    && ok_check_cond_rendered
  then print_endline "All regression checks passed."
  else exit 1
