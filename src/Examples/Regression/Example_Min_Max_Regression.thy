theory Example_Min_Max_Regression
  imports "Voblint_CLI.Analyse_Dispatch"
begin

section \<open>Regression: Min/Max special calls across Sign, Interval, and Parity\<close>

text \<open>
  VIMP recognizes the otherwise ordinary identifiers \<open>min\<close> and \<open>max\<close>
  (\<^theory>\<open>Voblint_VIMP.VIMP_Special\<close>) as built-in special calls when used
  with two arguments -- a VIMP library-modeling convention, not an ISO C
  claim: standard C provides floating-point \<open>fmin\<close>/\<open>fmax\<close> via \<open>math.h\<close>,
  while bare \<open>min\<close>/\<open>max\<close> are commonly implementation-specific macros or
  functions, not a language builtin. Unlike \<open>__voblint_nondet_int\<close>, neither
  needs a splicing workaround here: both are ordinary lexable identifiers, so
  they parse inside \<open>program { ... }\<close> exactly like any other call. This is
  a small end-to-end witness that the special call reaches each domain's
  generic \<open>sound_special_ops\<close> dispatch (\<^theory>\<open>Voblint_Core.Special_Ops\<close>,
  instantiated per domain in \<^theory>\<open>Voblint_Analysis.Sign_Special\<close>/
  \<open>Interval_Special\<close>/\<open>Parity_Special\<close>), not a flagship precision showcase.
\<close>

subsection \<open>Sign and Interval: min/max of a positive and a negative constant\<close>

definition min_max_demo_prog :: imp_prog where
  "min_max_demo_prog =
     program {
       void main() {
         x := 3;
         y := 0 - 5;
         z := min(x, y);
         w := max(x, y);
         __voblint_check(z < 0);
         __voblint_check(0 < w)
       }
     }"

lemma min_max_demo_sign_precise:
  "analyse Sign_Analysis min_max_demo_prog =
     [(Statement 4, Less (V (STR ''z'')) (N 0), Check_Proved),
      (Statement 5, Less (N 0) (V (STR ''w'')), Check_Proved)]"
  by eval

lemma min_max_demo_interval_precise:
  "analyse Interval_Analysis min_max_demo_prog =
     [(Statement 4, Less (V (STR ''z'')) (N 0), Check_Proved),
      (Statement 5, Less (N 0) (V (STR ''w'')), Check_Proved)]"
  by eval

subsection \<open>Parity: min/max of two odd constants stays odd, not top\<close>

text \<open>
  \<open>parity_min\<close>/\<open>parity_max\<close> return exactly one of their two arguments, never
  a synthesized value, so when both arguments share a known parity the
  result provably shares it too. \<open>3\<close> and \<open>0 - 5\<close> are both odd; \<open>z\<close>/\<open>w\<close> stay
  \<open>POdd\<close> here, not \<open>PTop\<close>. The exit state is read through
  \<^const>\<open>analyse_parity_result_for\<close>, the same routed table
  \<^const>\<open>analyse_parity_report_for\<close> -- and hence the runtime dispatcher's
  Parity branch -- serves.
\<close>

definition min_max_demo_parity_env :: "vname \<Rightarrow> parity" where
  "min_max_demo_parity_env =
     (case lookup_context
             (analyse_parity_result_for (declared_global min_max_demo_prog) min_max_demo_prog)
             (cfg_exit (prog_cfg prog_main_name min_max_demo_prog)) () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

lemma min_max_demo_parity_z_odd:
  "min_max_demo_parity_env (STR ''z'') = POdd"
  by (simp add: min_max_demo_parity_env_def) eval

lemma min_max_demo_parity_w_odd:
  "min_max_demo_parity_env (STR ''w'') = POdd"
  by (simp add: min_max_demo_parity_env_def) eval

subsection \<open>Wrong arity is rejected by well-formedness, not silently reinterpreted\<close>

text \<open>
  \<open>classify_special\<close> only matches an exact two-argument list for \<open>Min\<close>/\<open>Max\<close>;
  a wrong-arity call such as \<open>min(x)\<close> falls through to its catch-all \<open>None\<close>
  clause. \<open>wf_source_com\<close> requires \<open>classify_special desc actuals \<noteq> None\<close>
  whenever the callee resolves through \<open>special_table\<close>, so a wrong-arity
  \<open>min\<close>/\<open>max\<close> call is rejected by source well-formedness -- it never falls
  through to being treated as an ordinary call to an undeclared procedure
  named \<open>min\<close>, since \<open>special_table\<close> already claimed that name first.
  Whether the CLI itself enforces \<open>wf_source_program\<close> before compiling and
  analyzing a parsed program is a separate, pre-existing question this
  regression does not address.
\<close>

lemma min_wrong_arity_not_classified:
  "classify_special SD_Min [V (STR ''x'')] = None"
  by simp

lemma min_wrong_arity_call_not_wf:
  "\<not> wf_source_com (\<lambda>_. None)
       (VIMP_Proc.com.Call (Some (STR ''z'')) special_pname_min [V (STR ''x'')])"
  by eval

text \<open>
  End-to-end witness for the same fact through \<^const>\<open>wf_program_compile_input_exec\<close>
  (\<^theory>\<open>Voblint_CFG.Compile_Invariants\<close>), the executable reformulation the CLI's
  well-formedness gate actually calls: a whole program, not just one bare
  \<open>com\<close> value, confirming the gate itself would reject this program (issue
  tracked for the CLI \<open>wf_source_program\<close> enforcement gate). Contrasted with
  \<open>min_max_demo_prog\<close> above, which is well-formed.
\<close>

definition min_wrong_arity_prog :: imp_prog where
  "min_wrong_arity_prog =
     program {
       void main() {
         x := 3;
         z := min(x)
       }
     }"

lemma min_max_demo_prog_wf:
  "wf_program_compile_input_exec min_max_demo_prog"
  by eval

lemma min_wrong_arity_prog_not_wf:
  "\<not> wf_program_compile_input_exec min_wrong_arity_prog"
  by eval

end
