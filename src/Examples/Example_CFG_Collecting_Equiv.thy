section \<open>Example: IMP collecting equals CFG collecting at exit\<close>

text \<open>\label{sec:example-cfg-collect-equiv}\<close>

theory Example_CFG_Collecting_Equiv
  imports CFG_Collecting
begin

text \<open>
  This theory instantiates the proved bridge
  @{thm cfg_collect_exit_eq_collect} on a concrete program.
  It shows exactly what the theorem means operationally:
  the set of final stores from AST-level @{const collect} equals the set
  at the compiled CFG exit from @{const cfg_collect}.
\<close>

(* \<midarrow>\<midarrow> Program and stores \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition collecting_example_prog :: com where
  "collecting_example_prog =
     (''x'' ::= N 5) ;; (''y'' ::= Plus (V ''x'') (N 1))"

text \<open>\<^verbatim>\<open>x := 5;
y := x + 1\<close>\<close>

definition collecting_example_s0 :: store where
  "collecting_example_s0 = (\<lambda>_. 0)"

definition collecting_example_t :: store where
  "collecting_example_t = (collecting_example_s0(''x'' := 5))(''y'' := 6)"

subsection \<open>Concrete execution\<close>

lemma collecting_example_big_step:
  "(collecting_example_prog, collecting_example_s0) \<Rightarrow> collecting_example_t"
  unfolding collecting_example_prog_def collecting_example_s0_def collecting_example_t_def
proof (rule Seq)
  show "(''x'' ::= N 5, \<lambda>_. 0) \<Rightarrow> (\<lambda>_. 0)(''x'' := 5)"
    by (metis AExp.aval.simps(1) big_step.Assign IMP2_BigStep.aval.simps(1))
next
  show "(''y'' ::= Plus (V ''x'') (N 1), (\<lambda>_. 0)(''x'' := 5)) \<Rightarrow> (\<lambda>_. 0)(''x'' := 5, ''y'' := 6)"
  proof -
    have h: "(\<lambda>_. 0)(''x'' := 5, ''y'' := 6) =
             ((\<lambda>_. 0)(''x'' := 5))(''y'' := aval (Plus (V ''x'') (N 1)) ((\<lambda>_. 0)(''x'' := 5)))"
      by simp
    show ?thesis by (subst h) (rule big_step.Assign)
  qed
qed

subsection \<open>AST collecting semantics\<close>

lemma collecting_example_collect:
  "collect collecting_example_prog {collecting_example_s0} = {collecting_example_t}"
  using IMP2_Collecting.collect_def big_step_determ collecting_example_big_step by auto


text \<open>
  Compiled graph for @{const collecting_example_prog}:
  PP0 @{text \<open>--[x := 5]-->\<close>} PP1 @{text \<open>--[nop]-->\<close>} PP2 @{text \<open>--[y := x+1]-->\<close>} PP3 (exit).
\<close>

definition cfg where "cfg  = (to_cfg collecting_example_prog)"
value cfg

subsection \<open>CFG collecting at exit (via the bridge)\<close>

theorem collecting_example_both_views_agree:
  "collect collecting_example_prog {collecting_example_s0}
   = cfg_collect cfg {collecting_example_s0} (cfg_exit cfg)"
  by (simp add: cfg_collect_exit_eq_collect cfg_def)
 
corollary collecting_example_final_in_both:
  "collecting_example_t \<in> collect collecting_example_prog {collecting_example_s0}
   \<and> collecting_example_t \<in> cfg_collect cfg {collecting_example_s0} (cfg_exit cfg)"
  using collecting_example_both_views_agree collecting_example_collect by auto


end
