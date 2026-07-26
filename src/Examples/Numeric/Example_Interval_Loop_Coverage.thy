section \<open>Example: Interval Analysis of a Full Bounded Loop Program\<close>

theory Example_Interval_Loop_Coverage
  imports Voblint_CFG.CFG_Prune
    "Voblint_Analysis.Interval_Domain" "Voblint_Analysis.LTR_Analysis_Sound"
    "Voblint_IMP2.IMP2_Notation"
begin

(* Disambiguate our N abbreviation from the phase datatype constructor. *)
hide_const phase.N

text \<open>
  A full program carried end to end through the interval analyzer:

    \<^verbatim>\<open>x := 0; while (x < 20) { x := x + 1 }\<close>

  The interval domain proves the bounded invariant \<^verbatim>\<open>0 <= x <= 20\<close>
  (i.e. \<^verbatim>\<open>x \<in> [0, 20]\<close>) at the loop head over every reaching store.  Both bounds
  are interval-specific: the lower bound \<^verbatim>\<open>0\<close> is the joined initial value, and the
  upper bound \<^verbatim>\<open>20\<close> comes from guard refinement -- @{const assume_ivl} narrows
  \<^verbatim>\<open>x\<close> to \<^verbatim>\<open>[.., 19]\<close> on entering the body (\<^verbatim>\<open>x < 20\<close>), so after \<^verbatim>\<open>x := x + 1\<close> and the
  join with the initial \<^verbatim>\<open>[0,0]\<close> the loop head stabilises at \<^verbatim>\<open>[0,20]\<close> with no
  widening needed.  The Sign lattice expresses neither bound (it collapses
  \<^verbatim>\<open>[0,0]\<close> joined with \<^verbatim>\<open>[1,1]\<close> to sign top).

  Certified backward-analysis story: @{text "Example_Guard_Refinement"}
  isolates the guard step; this theory carries the same @{const assume_ivl} transfers
  through the full CFG to the trace-native post-fixpoint soundness theorem.

  Executable mirror (Kleene / warrowing TD on @{text "ivl st"}, eval only):
  @{text "Exec_Ivl_Run"}.
\<close>

definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog = imp \<lbrakk>
     x := 0;
     while (x < 20) { x := x + 1 }
   \<rbrakk>"

subsection \<open>The compiled CFG\<close>

abbreviation "loop_cfg \<equiv> compile_prog Map.empty [] ''main'' loop_prog"

lemma loop_cfg_full:
  "loop_cfg =
     \<lparr> intra =
         {(FunctionEntry ''main'', EA_Nop, Statement 0),
          (Statement 0, EA_Assign ''x'' (N 0), Statement 1),
          (Statement 1, EA_Nop, Statement 2),
          (Statement 2, EA_Assume (Less (V ''x'') (N 20)), Statement 3),
          (Statement 2, EA_AssumeNot (Less (V ''x'') (N 20)), Statement 5),
          (Statement 3, EA_Assign ''x'' (Plus (V ''x'') (N 1)), Statement 4),
          (Statement 4, EA_Nop, Statement 2),
          (Statement 5, EA_Ret None ''main'', FunctionResult ''main'')},
       calls = {},
       cfg_entry = FunctionEntry ''main'' \<rparr>"
  by eval

lemma loop_cfg_entry: "cfg_entry loop_cfg = FunctionEntry ''main''"
  by (simp add: loop_cfg_full)
lemma loop_cfg_exit: "cfg_exit loop_cfg = FunctionResult ''main''"
  by (simp add: loop_cfg_full cfg_exit_def)
lemma loop_cfg_calls: "calls loop_cfg = {}"
  by (simp add: loop_cfg_full)
lemma loop_cfg_intra:
  "intra loop_cfg =
     {(FunctionEntry ''main'', EA_Nop, Statement 0),
      (Statement 0, EA_Assign ''x'' (N 0), Statement 1),
      (Statement 1, EA_Nop, Statement 2),
      (Statement 2, EA_Assume (Less (V ''x'') (N 20)), Statement 3),
      (Statement 2, EA_AssumeNot (Less (V ''x'') (N 20)), Statement 5),
      (Statement 3, EA_Assign ''x'' (Plus (V ''x'') (N 1)), Statement 4),
      (Statement 4, EA_Nop, Statement 2),
      (Statement 5, EA_Ret None ''main'', FunctionResult ''main'')}"
  by (simp add: loop_cfg_full)

subsection \<open>An exhibited interval post-fixpoint\<close>

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
     (if v = Statement 1 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 0))
      else if v = Statement 3 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 19))
      else if v = Statement 4 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 1) (Fin 20))
      else if v \<in> {Statement 2, Statement 5}
        then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 20))
      else (\<lambda>_. Ivl MinInf PlusInf))"

text \<open>The program is call-free, so both call-shaped sources of \<^const>\<open>rhs\<close> are empty and
  only the intra predecessors constrain \<^const>\<open>loop_env\<close>.\<close>

lemma loop_entry_calls: "entry_calls loop_cfg v = {}"
  by (simp add: entry_calls_def loop_cfg_calls)

lemma loop_return_calls: "return_calls loop_cfg v = {}"
  by (simp add: return_calls_def loop_cfg_calls)

lemma loop_intra_predecessors_finite: "finite (intra_predecessors loop_cfg v)"
  by (rule finite_intra_predecessors) (simp add: loop_cfg_intra)

lemma loop_postfix:
  "is_post_fixpoint loop_cfg ivl_tf (\<squnion>) bot loop_s0 loop_env"
  unfolding is_post_fixpoint_def
proof (rule allI)
  fix v
  let ?I = "(\<lambda>(u, a). apply_tf ivl_tf a (loop_env u)) ` intra_predecessors loop_cfg v"
  have finI: "finite ?I" using loop_intra_predecessors_finite by blast
  have leI: "\<And>t. t \<in> ?I \<Longrightarrow> t \<le> loop_env v"
    by (auto split: if_splits
             simp: intra_predecessors_def loop_cfg_intra loop_env_def ivl_tf_def
                   assign_ivl_def assume_ivl_def assume_not_ivl_def normalize_ivl_def
                   less_eq_ivl_def le_fun_def)
  show "rhs loop_cfg ivl_tf (\<squnion>) bot loop_s0 loop_env v \<le> loop_env v"
  proof (cases "v = cfg_entry loop_cfg")
    case True
    then have "loop_s0 \<le> loop_env v"
      by (simp add: loop_cfg_entry loop_s0_def loop_env_def)
    with True finI leI show ?thesis
      unfolding rhs_def Let_def
      by (auto simp: loop_entry_calls loop_return_calls intro!: abs_join_set_le)
  next
    case False
    with finI leI show ?thesis
      unfolding rhs_def Let_def
      by (auto simp: loop_entry_calls loop_return_calls intro!: abs_join_set_le)
  qed
qed

subsection \<open>Backward guard refinement at the body entry\<close>

text \<open>
  Edge from node 2 to node 3 is @{const EA_Assume} on @{text "x < 20"}.  The body-entry
  interval @{text "[0,19]"} in @{const loop_env} is exactly
  @{const assume_ivl} applied at the loop head --- not widening and not join
  alone (identity assume would keep @{text "[0,20]"}; see
  @{text "Example_Guard_Refinement"}).
\<close>

abbreviation "loop_body_entry \<equiv> Statement 3"

lemma loop_body_x_from_assume:
  "tf_assume ivl_tf (Less (V ''x'') (N 20)) (loop_env (Statement 2)) ''x'' = Ivl (Fin 0) (Fin 19)"
  unfolding ivl_tf_def assume_ivl_def loop_env_def
  by (simp add: inv_less_ivl.simps ivl_backward_domain.bfilter.simps
        ivl_backward_domain.afilter.simps aval_ivl.simps aval_ivl_hol.simps meet_ivl.simps)

lemma loop_body_entry_x:
  "loop_env loop_body_entry ''x'' = Ivl (Fin 0) (Fin 19)"
  by (simp add: loop_env_def)

subsection \<open>Soundness: @{text "0 \<le> x \<le> 20"} at the loop head\<close>

text \<open>The loop head is the assume node where @{term \<open>x < 20\<close>} is checked.\<close>
abbreviation "loop_head \<equiv> Statement 2"

lemma loop_head_x_bounded:
  assumes S_sound: "S \<subseteq> \<lbrakk>loop_s0\<rbrakk>"
  assumes s: "s \<in> ltr_collect loop_cfg S loop_head"
  shows "0 \<le> s ''x'' \<and> s ''x'' \<le> 20"
proof -
  have fin_e: "finite (intra loop_cfg)" by (simp add: loop_cfg_intra)
  have fin_c: "finite (calls loop_cfg)" by (simp add: loop_cfg_calls)
  have le: "ltr_collect loop_cfg S loop_head \<le> \<lbrakk>loop_env loop_head\<rbrakk>"
    using sound_transfer.unified_ltr_post_fixpoint_sound
          [OF ivl_sound_tf.sound_transfer_axioms fin_e fin_c loop_postfix S_sound]
    by blast
  from s le have "s \<in> \<lbrakk>loop_env loop_head\<rbrakk>" by blast
  then have "s ''x'' \<in> gamma (loop_env loop_head ''x'')"
    unfolding gamma_state_def by blast
  then show ?thesis by (auto simp: loop_env_def)
qed

end


