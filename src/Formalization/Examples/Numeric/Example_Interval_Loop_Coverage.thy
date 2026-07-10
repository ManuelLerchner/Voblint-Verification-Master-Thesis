section \<open>Example: Interval Analysis of a Full Bounded Loop Program\<close>

theory Example_Interval_Loop_Coverage
  imports Voblint_CFG.CFG_Prune "Voblint_CFG.CFG_Collect"
    "Voblint_Analysis.Interval_Domain" "Voblint_Analysis.Constraint_System_Sound"
    "Voblint_IMP2.IMP2_Notation" "Voblint_IMP2.IMP2_Bridge" Trace_Analysis_Sound
begin

(* Suppress AFP/IMP2 Syntax names that shadow our IMP2_Syntax abbreviations. *)
no_notation Syntax.Assign (\<open>_ ::= _\<close> [1000, 61] 61)
hide_const (open) Syntax.N Syntax.V
hide_const phase.N

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

  Certified backward-analysis story: @{text "Example_Guard_Refinement"}
  isolates the guard step; this theory carries the same @{const assume_ivl} transfers
  through the full CFG to a trace-level soundness theorem.

  Executable mirror (Kleene / warrowing TD on @{text "ivl st"}, eval only):
  @{text "Exec_Ivl_Run"}.
\<close>

definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog = \<lbrakk>
     x := 0;
     while (x < 20) { x := x + 1 }
   \<rbrakk>"

subsection \<open>The compiled CFG\<close>

abbreviation "loop_cfg \<equiv> compile_prog Map.empty [] loop_prog"

lemma loop_cfg_full:
  "loop_cfg = mk_cfg 0 5
     {(0, EA_Assign ''x'' (N 0), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (Less (V ''x'') (N 20)), 3),
      (2, EA_AssumeNot (Less (V ''x'') (N 20)), 5),
      (3, EA_Assign ''x'' (Plus (V ''x'') (N 1)), 4),
      (4, EA_Nop, 2)}
     {}"
  by (simp add: compile_prog_def compile_prog_with_regions_def compile_procs_list_def Let_def eval_nat_numeral loop_prog_def; blast)

lemma loop_cfg_entry:   "cfg_entry loop_cfg = 0" by (simp add: loop_cfg_full)
lemma loop_cfg_exit:    "cfg_exit  loop_cfg = 5" by (simp add: loop_cfg_full)
lemma loop_cfg_combines: "combines loop_cfg = {}" by (simp add: loop_cfg_full)
lemma loop_cfg_edges:
  "edges loop_cfg =
     {(0, EA_Assign ''x'' (N 0), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (Less (V ''x'') (N 20)), 3),
      (2, EA_AssumeNot (Less (V ''x'') (N 20)), 5),
      (3, EA_Assign ''x'' (Plus (V ''x'') (N 1)), 4),
      (4, EA_Nop, 2)}"
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
     (if v = 1 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 0))
      else if v = 3 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 19))
      else if v = 4 then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 1) (Fin 20))
      else if v \<in> {2,5} then (\<lambda>_. Ivl MinInf PlusInf)(''x'' := Ivl (Fin 0) (Fin 20))
      else (\<lambda>_. Ivl MinInf PlusInf))"

lemma loop_postfix:
  "is_post_fixpoint loop_cfg ivl_tf (\<squnion>) bot loop_s0 loop_env"
  unfolding is_post_fixpoint_def
proof (rule allI)
  fix v
  show "rhs loop_cfg ivl_tf (\<squnion>) bot loop_s0 loop_env v \<le> loop_env v"
    apply (simp only: rhs_def Let_def loop_cfg_entry loop_cfg_edges loop_cfg_combines)
    apply (rule abs_join_set_le)
    apply (rule finite_subset[where B=
            "insert loop_s0 ((\<lambda>(u,a). apply_tf ivl_tf a (loop_env u)) `
               {(0, EA_Assign ''x'' (N 0)),
                (1, EA_Nop),
                (2, EA_Assume (Less (V ''x'') (N 20))),
                (2, EA_AssumeNot (Less (V ''x'') (N 20))),
                (3, EA_Assign ''x'' (Plus (V ''x'') (N 1))),
                (4, EA_Nop)})"])
    by (auto split: if_splits
             simp: loop_env_def loop_s0_def ivl_tf_def assign_ivl_def
                   assume_ivl_def assume_not_ivl_def normalize_ivl_def less_eq_ivl_def le_fun_def)
qed

subsection \<open>Backward guard refinement at the body entry\<close>

text \<open>
  Edge from node 2 to node 3 is @{const EA_Assume} on @{text "x < 20"}.  The body-entry
  interval @{text "[0,19]"} in @{const loop_env} is exactly
  @{const assume_ivl} applied at the loop head --- not widening and not join
  alone (identity assume would keep @{text "[0,20]"}; see
  @{text "Example_Guard_Refinement"}).
\<close>

abbreviation "loop_body_entry \<equiv> 3"

lemma loop_body_x_from_assume:
  "tf_assume ivl_tf (Less (V ''x'') (N 20)) (loop_env 2) ''x'' = Ivl (Fin 0) (Fin 19)"
  unfolding ivl_tf_def assume_ivl_def loop_env_def
  by (simp add: inv_less_ivl.simps ivl_backward_domain.bfilter.simps
        ivl_backward_domain.afilter.simps aval_ivl.simps aval_ivl_hol.simps meet_ivl.simps)

lemma loop_body_entry_x:
  "loop_env loop_body_entry ''x'' = Ivl (Fin 0) (Fin 19)"
  by (simp add: loop_env_def)

subsection \<open>Soundness: @{text "0 \<le> x \<le> 20"} at the loop head\<close>

text \<open>The loop head is the assume node where @{term \<open>x < 20\<close>} is checked.\<close>
abbreviation "loop_head \<equiv> 2"

lemma loop_head_x_bounded:
  assumes S_sound: "S \<subseteq> \<lbrakk>loop_s0\<rbrakk>"
  assumes tr: "tr \<in> cfg_collect_trace loop_cfg S loop_head"
  shows "0 \<le> (last tr) ''x'' \<and> (last tr) ''x'' \<le> 20"
proof -
  have fin_e: "finite (edges loop_cfg)" by (simp add: loop_cfg_edges)
  have fin_c: "finite (combines loop_cfg)" by (simp add: loop_cfg_combines)
  have s0_conv: "S \<subseteq> \<lbrakk>loop_s0\<rbrakk>"
    using S_sound by simp
  have "(last tr) ''x'' \<in> gamma (loop_env loop_head ''x'')"
    by (rule Trace_Analysis_Sound.sound_transfer.reaching_global_read_sound
          [OF ivl_sound_tf.sound_transfer_axioms fin_e fin_c loop_postfix s0_conv tr])
  then show ?thesis by (auto simp: loop_env_def)
qed

end
