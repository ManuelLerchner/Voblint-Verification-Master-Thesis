section \<open>Example: Interval Analysis of a Full Bounded Loop Program\<close>

theory Example_Interval_Loop_Coverage
  imports Voblint_CFG.CFG_Prune "Voblint_CFG.CFG_Collect_Unified"
    "Voblint_Analysis.Interval_Domain" "Voblint_Analysis.Constraint_System_Sound"
    "Voblint_IMP2.IMP2_Bridge" Trace_IP_Analysis_Sound
begin

text \<open>
  A full program carried end to end through the interval analyzer:

    \<^verbatim>\<open>x := 0; while (x < 20) { x := x + 1 }\<close>

  The interval domain proves the bounded invariant \<^verbatim>\<open>0 <= x <= 20\<close>
  (i.e. \<^verbatim>\<open>x \<in> [0, 20]\<close>) at the loop head over every reaching trace.  Both bounds
  are interval-specific: the lower bound \<^verbatim>\<open>0\<close> is the joined initial value, and the
  upper bound \<^verbatim>\<open>20\<close> comes from guard refinement -- @{const assume_ivl} narrows
  \<^verbatim>\<open>x\<close> to \<^verbatim>\<open>[.., 19]\<close> on entering the body (\<^verbatim>\<open>x < 20\<close>), so after \<^verbatim>\<open>x := x + 1\<close> and the
  join with the initial \<^verbatim>\<open>[0,0]\<close> the loop head stabilises at \<^verbatim>\<open>[0,20]\<close> with no
  widening needed.  The Sign lattice expresses neither bound (it collapses
  \<^verbatim>\<open>[0,0]\<close> joined with \<^verbatim>\<open>[1,1]\<close> to sign top).
\<close>

definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog =
     IMP2_Proc.com.Seq
       (IMP2_Proc.com.Assign ''x'' (BaseN (AExp.N 0)))
       (IMP2_Proc.com.While (IMP2_Syntax.bexp.Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20)))
          (IMP2_Proc.com.Assign ''x''
             (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1)))))"

subsection \<open>The compiled CFG\<close>

abbreviation "loop_cfg \<equiv> compile_prog Map.empty [] loop_prog"

lemma loop_cfg_entry: "cfg_entry loop_cfg = 0"
  by (simp add: compile_prog_def compile_prog_with_regions_def loop_prog_def Let_def)

lemma loop_cfg_combines: "combines loop_cfg = {}"
  by (simp add: compile_prog_def compile_prog_with_regions_def loop_prog_def Let_def)

lemma loop_cfg_edges:
  "edges loop_cfg =
     {(0, EA_Assign ''x'' (BaseN (AExp.N 0)), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (IMP2_Syntax.bexp.Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), 3),
      (2, EA_AssumeNot (IMP2_Syntax.bexp.Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), 5),
      (3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1))), 4),
      (4, EA_Nop, 2)}"
  by (auto simp: compile_prog_def compile_prog_with_regions_def loop_prog_def Let_def
             eval_nat_numeral)

subsection \<open>An exhibited interval post-fixpoint\<close>

text \<open>The abstract join is below @{term X} iff every member is.\<close>
lemma abs_join_set_le:
  fixes X :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes fin: "finite S" and le: "\<And>s. s \<in> S \<Longrightarrow> s \<le> X"
  shows "abs_join_set (\<squnion>) bot S \<le> X"
proof -
  have "abs_join_set (\<squnion>) bot S = Sup_fin (insert bot S)"
    unfolding abs_join_set_def using fin by (simp add: Sup_fin.eq_fold)
  also have "\<dots> \<le> X" using fin le by (intro Sup_fin.boundedI) auto
  finally show ?thesis .
qed

definition loop_s0 :: "ivl abs_state" where
  "loop_s0 = (\<lambda>_. Ivl MinInf PlusInf)"

text \<open>
  After \<^verbatim>\<open>x := 0\<close> node 1 holds \<^verbatim>\<open>x \<in> [0,0]\<close>; the loop head (node 2) stabilises
  at \<^verbatim>\<open>[0,20]\<close>.  Guard refinement narrows the body entry (node 3) to \<^verbatim>\<open>[0,19]\<close>, so
  after \<^verbatim>\<open>x := x + 1\<close> node 4 holds \<^verbatim>\<open>[1,20]\<close>; joined with \<^verbatim>\<open>[0,0]\<close> this is exactly the
  loop-head value -- a finite (non-widened) fixpoint.  Other variables stay at
  the full interval.
\<close>
definition loop_env :: "pp \<Rightarrow> ivl abs_state" where
  "loop_env v =
     (if v = 1 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 0))
      else if v = 3 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 19))
      else if v = 4 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 1) (Fin 20))
      else if v \<in> {2,5} then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 20))
      else (\<lambda>_. Ivl MinInf PlusInf))"

lemma loop_postfix:
  "is_post_fixpoint_ip loop_cfg ivl_tf (\<squnion>) bot loop_s0 loop_env"
  unfolding is_post_fixpoint_ip_def
proof (rule allI)
  fix v
  show "rhs_ip loop_cfg ivl_tf (\<squnion>) bot loop_s0 loop_env v \<le> loop_env v"
    apply (simp only: rhs_ip_eq_rhs_if_no_combines[OF loop_cfg_combines]
                      rhs_def Let_def loop_cfg_entry loop_cfg_edges)
    apply (rule abs_join_set_le)
    apply (rule finite_subset[where B=
            "insert loop_s0 ((\<lambda>(u,a). apply_tf ivl_tf a (loop_env u)) `
               {(0, EA_Assign ''x'' (BaseN (AExp.N 0))),
                (1, EA_Nop),
                (2, EA_Assume (IMP2_Syntax.bexp.Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20)))),
                (2, EA_AssumeNot (IMP2_Syntax.bexp.Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20)))),
                (3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1)))),
                (4, EA_Nop)})"])
    by (auto split: if_splits
               simp: loop_env_def loop_s0_def ivl_tf_def assign_ivl_def
                     aval_ivl.simps aval_ivl_hol.simps ivl_plus.simps eint_plus.simps
                     assume_ivl.simps assume_not_ivl.simps meet_ivl.simps
                     less_eq_ivl_def le_fun_def)
qed

subsection \<open>Soundness: @{text "0 \<le> x \<le> 20"} at the loop head\<close>

text \<open>The loop head is the assume node where @{term \<open>x < 20\<close>} is checked.\<close>
abbreviation "loop_head \<equiv> 2"

lemma loop_head_x_bounded:
  assumes S_sound: "S \<subseteq> ivl_domain.gamma_state loop_s0"
  assumes tr: "tr \<in> cfg_collect_trace_ip loop_cfg S loop_head"
  shows "0 \<le> (last tr) ''x'' \<and> (last tr) ''x'' \<le> 20"
proof -
  have fin_e: "finite (edges loop_cfg)" by (simp add: loop_cfg_edges)
  have fin_c: "finite (combines loop_cfg)" by (simp add: loop_cfg_combines)
  have s0_conv: "S \<subseteq> sound_domain.gamma_state gamma_ivl loop_s0"
    using S_sound unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have "(last tr) ''x'' \<in> gamma_ivl (loop_env loop_head ''x'')"
    by (rule Trace_IP_Analysis_Sound.sound_transfer.reaching_global_read_sound
          [OF ivl_sound_tf.sound_transfer_axioms fin_e fin_c loop_postfix s0_conv tr])
  then show ?thesis by (auto simp: loop_env_def)
qed

end
