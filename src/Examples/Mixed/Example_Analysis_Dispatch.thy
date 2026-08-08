theory Example_Analysis_Dispatch
  imports
    Example_Sign_Codegen
    Voblint_Analysis.Interval_Checks
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

section \<open>A unified, verified check-report API across domains\<close>

text \<open>
  \<open>analyse_sign_report\<close> (\<^theory>\<open>Voblint_Examples.Example_Sign_Codegen\<close>) and
  \<open>interval_check_report\<close>/\<open>analyse_interval_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) already share one observable
  result type, \<open>check_report_entry list\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>), even though the two domains'
  internal abstract states (\<open>sign abs_state\<close> vs \<open>ivl abs_state\<close>) genuinely
  differ. \<open>analyse\<close> below is therefore a thin dispatcher, not a new proof:
  each branch reuses the domain's own already-generic, already-sound report
  function unchanged.

  Interval's warrowing variant (\<open>analyse_interval_td\<close>) is deliberately not a
  branch here: it has no soundness theorem yet (see
  \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>), so it stays outside this
  verified frontend rather than silently reporting an unbacked
  \<open>Check_Proved\<close>/\<open>Check_Refuted\<close>.
\<close>

datatype analysis_kind = Sign_Analysis | Interval_Analysis

fun analyse :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse Sign_Analysis p = analyse_sign_report p"
| "analyse Interval_Analysis p = analyse_interval_report p"

subsection \<open>A program that tells the two domains apart\<close>

text \<open>
  \<open>y := 1\<close> then check \<open>0 < y\<close> (should hold), then \<open>y := 0 - 1\<close> and check
  \<open>0 < y\<close> again (should now fail): a case where Interval's numeric bounds
  settle both checks precisely, while Sign's native D/G pipeline reports
  \<open>Check_Unknown\<close> for both --- the same always-join imprecision
  \<open>dgEx_inspect\<close> (\<^theory>\<open>Voblint_Examples.Exec_Sign_DG_Run\<close>) already
  documents for that pipeline, not a new limitation introduced here.
\<close>

definition dispatch_demo_prog :: imp_prog where
  "dispatch_demo_prog =
     program {
       void main() {
         y := 1;
         __voblint_check(0 < y);
         y := 0 - 1;
         __voblint_check(0 < y)
       }
     }"

lemma dispatch_demo_sign_unknown:
  "analyse Sign_Analysis dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Unknown),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Unknown)]"
  by eval

lemma dispatch_demo_interval_precise:
  "analyse Interval_Analysis dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted)]"
  by eval

subsection \<open>Executable code generation\<close>

text \<open>
  \<open>analyse\<close> genuinely takes the domain choice and the program as runtime
  arguments, not constants baked in at export time. The raw AST constructors,
  \<open>imp_prog.make\<close>, and \<open>proc_decl_of\<close> are exported alongside it so external
  Haskell/OCaml code can build a fresh \<open>imp_prog\<close> and hand it to \<open>analyse\<close>.

  \<^typ>\<open>vname\<close>/\<^typ>\<open>pname\<close> are \<^typ>\<open>String.literal\<close>
  (\<^theory>\<open>Voblint_VIMP.VIMP_Syntax\<close>/\<^theory>\<open>Voblint_VIMP.VIMP_Globals\<close>), already
  the target language's native string (\<^verbatim>\<open>String\<close> in Haskell,
  \<^verbatim>\<open>string\<close> in OCaml --- \<^theory>\<open>HOL.String\<close> ships that mapping
  unconditionally), so \<open>V\<close>/\<open>Assign\<close>/\<open>Random\<close>/\<open>com.Call\<close>/\<open>FunctionEntry\<close>/
  \<open>FunctionResult\<close>/\<open>proc_decl_of\<close>/\<open>imp_prog.make\<close> below already take and
  return native strings directly --- no separate construction facade needed.

  \<^theory>\<open>HOL-Library.Code_Target_Numeral\<close> makes \<open>int\<close>/\<open>nat\<close> abstract types
  backed by the target language's native arbitrary-precision integer
  (Haskell's \<open>Integer\<close>, OCaml's target-numeral representation) instead of
  Isabelle's own binary-numeral/Peano-successor encodings, so arithmetic and
  comparisons inside the exported analyser run on native integers rather
  than walking a \<open>Num\<close>/\<open>Nat\<close> term. \<open>int_of_integer\<close>/\<open>nat_of_integer\<close> and
  their inverses \<open>integer_of_int\<close>/\<open>integer_of_nat\<close> are the resulting
  bridge --- the only way external code can build or inspect an \<open>int\<close>/\<open>nat\<close>
  once the representation is opaque.

  \<^theory>\<open>HOL-Library.Code_Abstract_Char\<close> does the same for \<open>char\<close>, relevant
  wherever a \<open>char\<close> is inspected directly (e.g. \<^const>\<open>String.explode\<close>'s
  result) rather than through the opaque \<open>String.literal\<close> above.
  \<open>char_of_integer\<close>/\<open>integer_of_char\<close> are that bridge.
\<close>

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make proc_decl_of
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  prog_cfg prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Random EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge
  checking Haskell

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make proc_decl_of
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  prog_cfg prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Random EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge
  in Haskell module_name Voblint_Analyse file_prefix "Voblint_Analyse"

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make proc_decl_of
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  prog_cfg prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Random EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make proc_decl_of
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  prog_cfg prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Random EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge
  in OCaml module_name Voblint_Analyse file_prefix "Voblint_Analyse_OCaml"

end
