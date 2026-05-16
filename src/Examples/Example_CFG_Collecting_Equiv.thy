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

(* ── Program and stores ─────────────────────────────────────────── *)

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
proof -
  have x5: "(''x'' ::= N 5, collecting_example_s0) \<Rightarrow> collecting_example_s0(''x'' := 5)"
    by (simp add: assign_simp collecting_example_s0_def)
  have y6: "(''y'' ::= Plus (V ''x'') (N 1), collecting_example_s0(''x'' := 5))
            \<Rightarrow> (collecting_example_s0(''x'' := 5))(''y'' := 6)"
    by (simp add: assign_simp collecting_example_s0_def)
  show ?thesis
    unfolding collecting_example_prog_def collecting_example_t_def
    by (rule big_step.Seq[OF x5 y6])
qed

lemma collecting_example_big_step_det:
  "\<lbrakk> (collecting_example_prog, collecting_example_s0) \<Rightarrow> t;
      (collecting_example_prog, collecting_example_s0) \<Rightarrow> t' \<rbrakk>
   \<Longrightarrow> t = t'"
  by (rule big_step_determ)

subsection \<open>AST collecting semantics\<close>

lemma collecting_example_collect:
  "collect collecting_example_prog {collecting_example_s0} = {collecting_example_t}"
proof -
  have mem: "collecting_example_t
            \<in> {t. \<exists>s\<in>{collecting_example_s0}. (collecting_example_prog, s) \<Rightarrow> t}"
    using collecting_example_big_step by auto
  have uniq: "\<And>u. u \<in> {t. \<exists>s\<in>{collecting_example_s0}.
                (collecting_example_prog, s) \<Rightarrow> t}
              \<Longrightarrow> u = collecting_example_t"
    using big_step_determ[OF _ collecting_example_big_step]
    by simp
    
  show ?thesis
    unfolding collect_def using mem uniq by auto
qed

subsection \<open>Bridge theorem (what we proved in general)\<close>

lemma collecting_example_equiv:
  "cfg_collect (to_cfg collecting_example_prog) {collecting_example_s0}
     (cfg_exit (to_cfg collecting_example_prog))
   = collect collecting_example_prog {collecting_example_s0}"
  by (fact cfg_collect_exit_eq_collect)

subsection \<open>CFG collecting at exit (via the bridge)\<close>

lemma collecting_example_cfg_collect_exit:
  "cfg_collect (to_cfg collecting_example_prog) {collecting_example_s0}
     (cfg_exit (to_cfg collecting_example_prog))
   = {collecting_example_t}"
  using collecting_example_equiv collecting_example_collect by simp

theorem collecting_example_both_views_agree:
  "collect collecting_example_prog {collecting_example_s0}
   = cfg_collect (to_cfg collecting_example_prog) {collecting_example_s0}
       (cfg_exit (to_cfg collecting_example_prog))"
  using collecting_example_equiv by simp

corollary collecting_example_final_in_both:
  "collecting_example_t
   \<in> collect collecting_example_prog {collecting_example_s0}
   \<and> collecting_example_t
   \<in> cfg_collect (to_cfg collecting_example_prog) {collecting_example_s0}
       (cfg_exit (to_cfg collecting_example_prog))"
  using collecting_example_collect collecting_example_cfg_collect_exit
  by simp

subsection \<open>CFG shape (executable inspection)\<close>

text \<open>
  Compiled graph for @{const collecting_example_prog}:
  PP0 @{text \<open>--[x := 5]-->\<close>} PP1 @{text \<open>--[nop]-->\<close>} PP2 @{text \<open>--[y := x+1]-->\<close>} PP3 (exit).
\<close>

value "compile collecting_example_prog 0"
value "cfg_entry (to_cfg collecting_example_prog)"
value "cfg_exit  (to_cfg collecting_example_prog)"
value "cfg_edges (to_cfg collecting_example_prog)"

end
