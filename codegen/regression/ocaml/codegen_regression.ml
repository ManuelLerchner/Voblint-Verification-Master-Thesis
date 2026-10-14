(* Regression driver for the generated Voblint_Generated OCaml module.
   Constructs a VIMP program purely through the exported AST constructors
   (never touching Isabelle), runs it through the exported `run_voblint`
   entry point, and checks the result against the values
   src/Examples/CLI/Example_Run_Voblint_Regression.thy proves by evaluation and
   tests/regression/ carries as CLI fixtures. This driver is the layer that
   pins the *generated* module's agreement with both.

   This reads the same generated module the CLI itself links against; the
   CFG-inspection constants below are export roots for this driver alone.

   Do not hand-edit codegen/generated/ml/Voblint_Generated.ml; regenerate it with
   `pixi run codegen` instead. *)

open Voblint_Generated.Generated

(* `HOL-Library.Code_Target_Numeral` (imported by Analyse_Dispatch)
   backs Isabelle's `int`/`nat` by the target language's native
   arbitrary-precision integer -- Zarith's `Z.t` on the OCaml side -- so
   construction/inspection go through `Int_of_integer`/`nat_of_integer` and
   their inverses rather than walking a `num`/Peano-successor term. *)
let mk_int n = Int_of_integer (Z.of_int n)
let mk_nat n = nat_of_integer (Z.of_int n)

(* Notation-built checks in the Isabelle twins of these programs carry the
   placeholder label (0, 0); so do these. *)
let unlabelled = (mk_nat 0, mk_nat 0)

(* `vname`/`pname` are Isabelle's `String.literal`, which is already OCaml's
   native `string` (see Example_Analysis_Dispatch_Regression.thy), so variable/procedure
   names need no conversion at all. *)

let domain_label = function
  | Typed_Sign -> "Sign"
  | Typed_Interval -> "Interval"
  | Typed_Int _ -> "Int"
  | Typed_Parity -> "Parity"
  | Typed_Congruence -> "Congruence"
  | Typed_Order -> "Order"

(* y := 1; check(0 < y); y := 0 - 1; check(0 < y)
   Same program as demo_prog in Example_Run_Voblint_Regression.thy. *)
let check_cond = Less (N (mk_int 0), V "y")

let demo_prog =
  mk_program []
    (Seq
       ( Seq
           ( Seq
               ( Assign ((), "y", N (mk_int 1)),
                 Check ((), unlabelled, check_cond) ),
             Assign ((), "y", Minus (N (mk_int 0), N (mk_int 1))) ),
         Check ((), unlabelled, check_cond) ))
    []

(* Conditions are compared as show_texp_compact renders them below. *)
let expected_sign =
  [
    (Statement (mk_nat 1), ("0<y", Lifted Check_Proved));
    (Statement (mk_nat 3), ("0<y", Lifted Check_Refuted));
  ]

let expected_interval =
  [
    (Statement (mk_nat 1), ("0<y", Lifted Check_Proved));
    (Statement (mk_nat 3), ("0<y", Lifted Check_Refuted));
  ]

(* global `total`, procedure `inc` with formal `n`, two calls, two checks.
   Exercises `mk_program`'s procedure list, a procedure's formals, and `Call`
   together -- not just straight-line assignment/check.
   Same program as tests/regression/04-globals/precision/02-global_var.vimp and its
   known-imprecision sibling 01-repeated_call_site_widening.vimp; the CFG-shape
   expectations below have no fixture counterpart and live only here.
   The verdicts are below with the expectations. *)
let proc_demo_prog =
  mk_program
    [
      ( "inc",
        Gproc_decl_ext
          ([ "n" ], Assign ((), "total", Plus (V "total", V "n")), ()) );
    ]
    (Seq
       ( Seq
           ( Seq
               ( Seq
                   ( Assign ((), "total", N (mk_int 0)),
                     Call ((), None, "inc", [ N (mk_int 3) ]) ),
                 Call ((), None, "inc", [ N (mk_int 4) ]) ),
             Check ((), unlabelled, Less (N (mk_int 0), V "total")) ),
         Check ((), unlabelled, Less (V "total", N (mk_int 100))) ))
    [ "total" ]

(* Two calls grow a global, without contexts: total + n at i32 may overflow under
   the default assume_top, so neither domain decides either check. Pinned by
   Example_Run_Voblint_Regression.thy's proc_demo_sign and proc_demo_interval. *)
let expected_proc_demo_sign =
  [
    (Statement (mk_nat 5), ("0<total", Lifted Check_Unknown));
    (Statement (mk_nat 6), ("total<100", Lifted Check_Unknown));
  ]

let expected_proc_demo_interval =
  [
    (Statement (mk_nat 5), ("0<total", Lifted Check_Unknown));
    (Statement (mk_nat 6), ("total<100", Lifted Check_Unknown));
  ]

(* Acceptance regression A (no-call global self-feedback): no procedure, no call, just a
   global write that reads its own prior value. Same program as
   tests/regression/12-widening/precision/01-global_self_feedback.vimp.
   Isolates that the call/return summary was never
   the actual hazard -- a single self-referential global write reproduces it alone. Under the
   Base-style pipeline there is no separate flow-insensitive global summary for total to read
   back through, so the result is Check_Proved. *)
let no_call_global_self_ref_prog =
  mk_program []
    (Seq
       ( Seq
           ( Assign ((), "total", N (mk_int 0)),
             Assign ((), "total", Plus (V "total", N (mk_int 3))) ),
         Check ((), unlabelled, Less (N (mk_int 0), V "total")) ))
    [ "total" ]

let expected_no_call_global_self_ref_interval =
  [ (Statement (mk_nat 2), ("0<total", Lifted Check_Proved)) ]

(* Acceptance regression B (interprocedural global self-feedback): a single call to a
   procedure that reads and grows the same global. Same program as
   tests/regression/12-widening/precision/02-global_self_feedback_call.vimp.
   Confirms the fix also survives entry/combine (call/return) handling, not just a
   straight-line write. inc's single call site reaches its entry node once, so no
   repeated-visit widening applies, and total's exact value survives the combine step. *)
let one_call_prog =
  mk_program
    [
      ( "inc",
        Gproc_decl_ext
          ([ "n" ], Assign ((), "total", Plus (V "total", V "n")), ()) );
    ]
    (Seq
       ( Seq
           ( Assign ((), "total", N (mk_int 0)),
             Call ((), None, "inc", [ N (mk_int 3) ]) ),
         Check ((), unlabelled, Less (N (mk_int 0), V "total")) ))
    [ "total" ]

let expected_one_call_interval =
  [ (Statement (mk_nat 4), ("0<total", Lifted Check_Proved)) ]

let show_int i = Z.to_string (integer_of_int i)

(* Bot is the proved-unreachable verdict: no execution reaches the check, so
   none was computed. Naming it keeps "proved unreachable" comparable rather
   than collapsing it into one of the three decided answers. *)
let show_verdict = function
  | Bot -> "Bot"
  | Lifted Check_Proved -> "Check_Proved"
  | Lifted Check_Refuted -> "Check_Refuted"
  | Lifted Check_Unknown -> "Check_Unknown"

let show_nat n = Z.to_string (integer_of_nat n)

let show_entry (n, (cond, verdict)) =
  Printf.sprintf "(%s, %s, %s)"
    (match n with
    | Statement k -> "Statement " ^ show_nat k
    | FunctionEntry s -> "FunctionEntry " ^ s
    | FunctionResult s -> "FunctionResult " ^ s)
    cond (show_verdict verdict)

(* Compact renderers for the expectations below: no spaces around infix
   operators, "pp"/"entry_"/"result_" node prefixes. *)
let show_cfg_node_compact = function
  | Statement n -> "pp" ^ show_nat n
  | FunctionEntry s -> "entry_" ^ s
  | FunctionResult s -> "result_" ^ s

let show_kind = function
  | I8 -> "i8"
  | U8 -> "u8"
  | I16 -> "i16"
  | U16 -> "u16"
  | I32 -> "i32"
  | U32 -> "u32"
  | I64 -> "i64"
  | U64 -> "u64"

(* A variable by its own name: the report qualifies a local by its procedure. *)
let show_var x =
  let l = var_label x in
  match String.rindex_opt l ':' with
  | Some i -> String.sub l (i + 1) (String.length l - i - 1)
  | None -> l

let show_aop = function
  | AAdd -> "+"
  | ASub -> "-"
  | AMul -> "*"
  | ADiv -> "/"
  | AMod -> "%"

let show_cop = function
  | CLt -> "<"
  | CLe -> "<="
  | CGt -> ">"
  | CGe -> ">="
  | CEq -> "=="
  | CNe -> "!="

(* A typed expression in the same compact form, its kinds left out but for a
   conversion's. *)
let rec show_texp_compact = function
  | TN (_, i) -> show_int i
  | TVar (_, x) -> show_var x
  | TArith (_, op, a, b) ->
      "(" ^ show_texp_compact a ^ show_aop op ^ show_texp_compact b ^ ")"
  | TCast (k, a) -> "(" ^ show_kind k ^ ")" ^ show_texp_compact a
  | TCmp (op, a, b) -> show_texp_compact a ^ show_cop op ^ show_texp_compact b
  | TNot b -> "!(" ^ show_texp_compact b ^ ")"
  | TAnd (a, b) -> "(" ^ show_texp_compact a ^ "&&" ^ show_texp_compact b ^ ")"
  | TOr (a, b) -> "(" ^ show_texp_compact a ^ "||" ^ show_texp_compact b ^ ")"

(* One analysis run, reduced to the column this driver compares: the check
   point, the condition, and the lifted verdict, at the configuration
   Example_Run_Voblint_Regression.thy's demo_conf names. The programs declare no
   kinds. Every program here is well-formed, so `Malformed_Program` is a defect
   in the export rather than a failed expectation. *)
let report domain prog =
  match
    map_analysis_answer
      (typed_render_report string_of_typed_value)
      (run_voblint
         (Voblint_conf_ext
            ( [ domain ],
              Typed_Call_String (mk_nat 0),
              Globals_Warrow,
              Program_Globals_Flow_Sensitive,
              default_sem_conf,
              () ))
         [] prog)
  with
  | Invalid_Activation ->
      print_endline ("FAIL " ^ domain_label domain ^ ": invalid activation list");
      exit 1
  | Malformed_Program ->
      print_endline
        ("FAIL " ^ domain_label domain ^ ": program is not well-formed");
      exit 1
  | No_Answer ->
      print_endline
        ("FAIL " ^ domain_label domain ^ ": the solver returned no answer");
      exit 1
  | Analysed res ->
      List.map
        (fun chk ->
          ( check_point chk,
            (show_texp_compact (check_exp chk), check_verdict chk) ))
        (res_checks res)

let show_edge_action = function
  | EA_Nop -> "nop"
  | EA_Assign (x, a) -> show_var x ^ " := " ^ show_texp_compact a
  | EA_Special (Nondet_Int, x) -> show_var x ^ " := __voblint_nondet_int()"
  | EA_Special (Min (a, b), x) ->
      show_var x ^ " := min(" ^ show_texp_compact a ^ ", " ^ show_texp_compact b
      ^ ")"
  | EA_Special (Max (a, b), x) ->
      show_var x ^ " := max(" ^ show_texp_compact a ^ ", " ^ show_texp_compact b
      ^ ")"
  | EA_Body p -> "body(" ^ p ^ ")"
  | EA_Assume b -> "[" ^ show_texp_compact b ^ "]"
  | EA_AssumeNot b -> "![" ^ show_texp_compact b ^ "]"
  | EA_Ret (None, _) -> "return"
  | EA_Ret (Some e, _) -> "return " ^ show_texp_compact e
  | EA_Check (_, b) -> "check(" ^ show_texp_compact b ^ ")"

let show_call_action = function
  | CallEdge (None, _, es) ->
      "call(" ^ String.concat "" (List.map show_texp_compact es) ^ ")"
  | CallEdge (Some x, _, es) ->
      show_var x ^ " := call("
      ^ String.concat "" (List.map show_texp_compact es)
      ^ ")"

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
         ^ show_cfg_node_compact entry
         ^ " ~cont~> " ^ show_cfg_node_compact cont)
       es)

let expected_proc_demo_intra =
  "pp0 --[total := (total+n)]--> pp1; pp1 --[return]--> result_inc; "
  ^ "pp2 --[total := 0]--> pp3; pp5 --[check(0<total)]--> pp6; "
  ^ "pp6 --[check(total<100)]--> pp7; pp7 --[return]--> result_main; "
  ^ "entry_inc --[body(inc)]--> pp0; entry_main --[body(main)]--> pp2"

let expected_proc_demo_calls =
  "pp3 --[call(3)]--> entry_inc ~cont~> pp4; pp4 --[call(4)]--> entry_inc \
   ~cont~> pp5"

(* [~line] is always [__LINE__] at the call site -- an OCaml builtin
   expanded there, not here, so a FAIL points at the specific
   check_case[_str] call that produced it, not this shared helper.
   [__LOC__] embeds only the filename ocamlopt was invoked with
   ("codegen_regression.ml", relative to codegen/regression/ocaml/), not clickable once
   back at the repo root this driver is normally run from -- building the
   repo-relative path explicitly instead keeps it clickable there. *)
let driver_path = "codegen/regression/ocaml/codegen_regression.ml"

let check_case ~line label actual expected =
  if actual = expected then (
    print_endline ("OK   " ^ label);
    true)
  else (
    print_endline (Printf.sprintf "FAIL %s (%s:%d)" label driver_path line);
    print_endline
      ("  expected: " ^ String.concat "; " (List.map show_entry expected));
    print_endline
      ("  actual:   " ^ String.concat "; " (List.map show_entry actual));
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
  let actual_sign = report Typed_Sign demo_prog in
  let actual_interval = report Typed_Interval demo_prog in
  let actual_proc_demo_sign = report Typed_Sign proc_demo_prog in
  let actual_proc_demo_interval = report Typed_Interval proc_demo_prog in
  let proc_demo_cfg = typed_cfg proc_demo_prog [] in
  let actual_proc_demo_intra =
    show_intra_list (tcfg_intra_edges proc_demo_cfg)
  in
  let actual_proc_demo_calls =
    show_calls_list (tcfg_call_edges proc_demo_cfg)
  in
  let actual_no_call_global_self_ref_interval =
    report Typed_Interval no_call_global_self_ref_prog
  in
  let actual_one_call_interval = report Typed_Interval one_call_prog in
  let ok_sign =
    check_case ~line:__LINE__ "Sign demo report" actual_sign expected_sign
  in
  let ok_interval =
    check_case ~line:__LINE__ "Interval demo report" actual_interval
      expected_interval
  in
  let ok_proc_demo_sign =
    check_case ~line:__LINE__ "Sign proc_demo report" actual_proc_demo_sign
      expected_proc_demo_sign
  in
  let ok_proc_demo_interval =
    check_case ~line:__LINE__ "Interval proc_demo report"
      actual_proc_demo_interval expected_proc_demo_interval
  in
  let ok_proc_demo_intra =
    check_case_str ~line:__LINE__ "proc_demo CFG intra edges"
      actual_proc_demo_intra expected_proc_demo_intra
  in
  let ok_proc_demo_calls =
    check_case_str ~line:__LINE__ "proc_demo CFG calls edges"
      actual_proc_demo_calls expected_proc_demo_calls
  in
  let ok_no_call_global_self_ref_interval =
    check_case ~line:__LINE__
      "Interval no-call global self-feedback (acceptance A)"
      actual_no_call_global_self_ref_interval
      expected_no_call_global_self_ref_interval
  in
  let ok_one_call_interval =
    check_case ~line:__LINE__
      "Interval interprocedural global self-feedback (acceptance B)"
      actual_one_call_interval expected_one_call_interval
  in
  if
    ok_sign && ok_interval && ok_proc_demo_sign && ok_proc_demo_interval
    && ok_proc_demo_intra && ok_proc_demo_calls
    && ok_no_call_global_self_ref_interval && ok_one_call_interval
  then print_endline "All regression checks passed."
  else exit 1
