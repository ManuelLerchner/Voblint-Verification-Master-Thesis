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

subsection \<open>A program with a global, a procedure, and a call\<close>

text \<open>
  \<open>total\<close> is a declared global; \<open>inc\<close> takes one formal and adds it to
  \<open>total\<close>; \<open>main\<close> calls \<open>inc\<close> twice, then checks the accumulated total ---
  exercising \<open>imp_prog.make\<close>'s procedure list, \<open>proc_decl_of\<close>'s formals, and
  \<open>com.Call\<close> together, not just straight-line assignment/check as
  \<open>dispatch_demo_prog\<close> does above.
\<close>

definition proc_demo_prog :: imp_prog where
  "proc_demo_prog =
     program {
       global total;
       void inc(n) {
         total := total + n
       }
       void main() {
         total := 0;
         inc(3);
         inc(4);
         __voblint_check(0 < total);
         __voblint_check(total < 100)
       }
     }"

text \<open>
  \<^const>\<open>string_of_check_report\<close>/\<^const>\<open>string_of_action\<close>/
  \<^const>\<open>string_of_call_action\<close> (\<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close>,
  already an ancestor via \<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>) already
  print a report/edge/call action; only the two CFG-edge-list joiners are new
  here.
\<close>

definition string_of_intra_list ::
  "(cfg_node \<times> edge_action \<times> cfg_node) list \<Rightarrow> string" where
  "string_of_intra_list es = join_source ''; ''
     (map (\<lambda>(u, a, v). string_of_cfg_node u @ '' --['' @ string_of_action a
             @ '']--> '' @ string_of_cfg_node v) es)"

definition string_of_calls_list ::
  "(cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) list \<Rightarrow> string" where
  "string_of_calls_list es = join_source ''; ''
     (map (\<lambda>(call, ca, entry, cont). string_of_cfg_node call @ '' --['' @
             string_of_call_action ca @ '']--> '' @ string_of_cfg_node entry
             @ '' ~cont~> '' @ string_of_cfg_node cont) es)"

lemma proc_demo_sign_unknown:
  "analyse Sign_Analysis proc_demo_prog =
     [(Statement 5, Less (N 0) (V (STR ''total'')), Check_Unknown),
      (Statement 6, Less (V (STR ''total'')) (N 100), Check_Unknown)]"
  by eval

lemma proc_demo_cfg_intra:
  "string_of_intra_list (cfg_intra_list (prog_cfg prog_main_name proc_demo_prog)) =
     ''pp0 --[total := (total+n)]--> pp1; pp1 --[return]--> result_inc; ''
     @ ''pp2 --[total := 0]--> pp3; pp5 --[check(0<total)]--> pp6; ''
     @ ''pp6 --[check(total<100)]--> pp7; pp7 --[return]--> result_main; ''
     @ ''entry_inc --[nop]--> pp0; entry_main --[nop]--> pp2''"
  by eval

lemma proc_demo_cfg_calls:
  "string_of_calls_list (cfg_calls_list (prog_cfg prog_main_name proc_demo_prog)) =
     ''pp3 --[call(3)]--> entry_inc ~cont~> pp4; pp4 --[call(4)]--> entry_inc ~cont~> pp5''"
  by eval

text \<open>
  \<open>analyse Interval_Analysis proc_demo_prog\<close> (this program: a global, one
  procedure with a formal, two calls, two checks) does not terminate within
  several minutes and crashes the evaluating process outright --- reproduced
  independently in a batch build (segfault after ~145s), an I/R REPL
  (crashed the daemon), and an I/Q jEdit session (crashed the backend).
  Confirmed independent of the \<^typ>\<open>String.literal\<close> migration in this
  branch --- no existing example anywhere in this project previously
  exercised \<^const>\<open>analyse_interval_report\<close> end-to-end on a program
  containing an actual \<^const>\<open>com.Call\<close> edge, so this is a pre-existing
  latent non-termination in Interval's procedure/call handling, newly
  exposed here, not caused by this migration. Left unevaluated; needs its
  own investigation.
\<close>


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
