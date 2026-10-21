theory Example_Call_String_Precision
  imports "Voblint_CLI.Analysis_Certified"
    "Voblint_Examples_Sign.Example_Sign_DG_CallString_K2"
begin

section \<open>Longer call strings decide a check through the analyzer\<close>

text \<open>
  \<^theory>\<open>Voblint_Examples_Sign.Example_Sign_DG_CallString_K2\<close> compares two hand-built
  routed equation systems. This theory makes the same comparison on the public
  operation \<^const>\<open>run_voblint\<close>, by evaluation. \<open>f\<close> passes its argument to \<open>g\<close>, and
  \<open>main\<close> calls \<open>f\<close> with a positive and a negative value. Under Sign with call strings
  of length 1, both activations of \<open>g\<close> share the context of its one call site in \<open>f\<close>,
  so Sign joins the two arguments to \<open>\<top>\<close> and neither check is decided. Call strings
  of length 2 also record the call in \<open>main\<close>, keep the two activations apart, and
  prove both checks.
\<close>

definition cs_nest_prog :: imp_prog where
  "cs_nest_prog = program {
     fun g(p) { return p + p; }
     fun f(p) { t = g(p); return t; }
     fun main() {
       x = f(3);
       y = f(-10);
       __voblint_check(0 < x);
       __voblint_check(y < 0);
     }
   }"

abbreviation cs_nest_config :: "nat \<Rightarrow> analysis_config" where
  "cs_nest_config k \<equiv> Analysis_Config [Sign_Analysis] Globals_Warrow (Ctx_CallString k)
     Program_Globals_Flow_Sensitive"

abbreviation cs_nest_checks where
  "cs_nest_checks res \<equiv> map (\<lambda>c. (check_point c, check_exp c, check_verdict c)) (report_checks res)"

abbreviation cs_x_pos :: exp where "cs_x_pos \<equiv> Less (N 0) (V (STR ''x''))"
abbreviation cs_y_neg :: exp where "cs_y_neg \<equiv> Less (V (STR ''y'')) (N 0)"

lemma cs_nest_reports:
  "(case (run_voblint (cs_nest_config 1) cs_nest_prog, run_voblint (cs_nest_config 2) cs_nest_prog) of
      (Analysed res1, Analysed res2) \<Rightarrow>
        cs_nest_checks res1
          = [(Statement 7, cs_x_pos, Decided Check_Unknown),
             (Statement 8, cs_y_neg, Decided Check_Unknown)]
      \<and> cs_nest_checks res2
          = [(Statement 7, cs_x_pos, Decided Check_Proved),
             (Statement 8, cs_y_neg, Decided Check_Proved)]
    | _ \<Rightarrow> False)"
  by eval

lemma HAS_VERDICT_of_checks:
  assumes "cs_nest_checks res = xs" and "(v, e, Decided r) \<in> set xs"
  shows "HAS_VERDICT res v e r"
proof -
  from assms obtain c where "c \<in> set (report_checks res)" "check_point c = v"
    and "check_exp c = e" "check_verdict c = Decided r"
    by auto
  then show ?thesis unfolding HAS_VERDICT_def by auto
qed

text \<open>
  The two runs, read through the report's verdicts: length 1 leaves both checks
  \<open>UNKNOWN\<close>, length 2 proves both.
\<close>

theorem run_voblint_call_string_2_decides:
  "\<exists>res1 res2.
     run_voblint (cs_nest_config 1) cs_nest_prog = Analysed res1
   \<and> run_voblint (cs_nest_config 2) cs_nest_prog = Analysed res2
   \<and> UNKNOWN res1 (Statement 7) cs_x_pos \<and> UNKNOWN res1 (Statement 8) cs_y_neg
   \<and> PROVED res2 (Statement 7) cs_x_pos \<and> PROVED res2 (Statement 8) cs_y_neg"
proof -
  obtain res1 res2 where
      run1: "run_voblint (cs_nest_config 1) cs_nest_prog = Analysed res1"
    and run2: "run_voblint (cs_nest_config 2) cs_nest_prog = Analysed res2"
    and c1: "cs_nest_checks res1
               = [(Statement 7, cs_x_pos, Decided Check_Unknown),
                  (Statement 8, cs_y_neg, Decided Check_Unknown)]"
    and c2: "cs_nest_checks res2
               = [(Statement 7, cs_x_pos, Decided Check_Proved),
                  (Statement 8, cs_y_neg, Decided Check_Proved)]"
    using cs_nest_reports
    by (auto split: analysis_answer.splits)
  have "UNKNOWN res1 (Statement 7) cs_x_pos" "UNKNOWN res1 (Statement 8) cs_y_neg"
    by (rule HAS_VERDICT_of_checks[OF c1], simp)+
  moreover have "PROVED res2 (Statement 7) cs_x_pos" "PROVED res2 (Statement 8) cs_y_neg"
    by (rule HAS_VERDICT_of_checks[OF c2], simp)+
  ultimately show ?thesis using run1 run2 by blast
qed

text \<open>
  With the soundness theorem, the length-2 verdicts are facts about the program: every
  store that reaches either check satisfies it.
\<close>

corollary cs_nest_checks_hold:
  assumes "s \<in> \<C>\<^bsub>declared_global cs_nest_prog,prog_cfg cs_nest_prog,
                   cinit_stores (declared_global cs_nest_prog)\<^esub> (Statement 7)"
    and "t \<in> \<C>\<^bsub>declared_global cs_nest_prog,prog_cfg cs_nest_prog,
                   cinit_stores (declared_global cs_nest_prog)\<^esub> (Statement 8)"
  shows "truthy (\<lbrakk>cs_x_pos\<rbrakk>\<^sub>e s)" and "truthy (\<lbrakk>cs_y_neg\<rbrakk>\<^sub>e t)"
  using run_voblint_call_string_2_decides run_voblint_proved assms by blast+

end
