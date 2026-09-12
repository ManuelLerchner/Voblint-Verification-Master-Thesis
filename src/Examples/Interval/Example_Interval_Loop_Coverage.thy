section \<open>Example: Interval Analysis of a Full Bounded Loop Program\<close>

theory Example_Interval_Loop_Coverage
  imports Voblint_CFG.CFG_Prune
    "Voblint_Analysis_Interval.Interval_Domain"
    "Voblint_VIMP.VIMP_Notation" "Voblint_Compile.Compile_Wellformed"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N

text \<open>
  A full program carried end to end through the interval analyzer:

    \<^verbatim>\<open>x := 0; while (x < 20) { x := x + 1 }\<close>

  The interval domain proves the bounded invariant \<^verbatim>\<open>0 <= x <= 20\<close>
  (i.e. \<^verbatim>\<open>x \<in> [0, 20]\<close>) at the loop head over every reaching store.  Both bounds
  are interval-specific: the lower bound \<^verbatim>\<open>0\<close> is the joined initial value, and the
  upper bound \<^verbatim>\<open>20\<close> comes from guard refinement -- @{const bfilter_ivl} narrows
  \<^verbatim>\<open>x\<close> to \<^verbatim>\<open>[.., 19]\<close> on entering the body (\<^verbatim>\<open>x < 20\<close>), so after \<^verbatim>\<open>x := x + 1\<close> and the
  join with the initial \<^verbatim>\<open>[0,0]\<close> the loop head stabilises at \<^verbatim>\<open>[0,20]\<close> with no
  widening needed.  The Sign lattice expresses neither bound (it collapses
  \<^verbatim>\<open>[0,0]\<close> joined with \<^verbatim>\<open>[1,1]\<close> to sign top).

  Certified backward-analysis story: @{text "Example_Guard_Refinement"}
  isolates the guard step; this theory exhibits the same
  @{const bfilter_ivl} narrowing at the body entry (\<open>loop_body_entry_x\<close> below),
  computed from a hand-picked node-1 input rather than the analyzer's own
  computed environment.  The certified end-to-end bound at the loop head is
  the executable pipeline's own computed and soundness-backed result:
  @{text "Exec_Interval_Run"} (\<open>loop_head_ivl\<close>/\<open>loop_head_ivl_td\<close>, \<open>by eval\<close> against
  the same program).
\<close>

definition loop_prog :: imp_prog where
  "loop_prog = program {
     fun main() { x = 0; while (x < 20) { x = x + 1; } }
   }"

subsection \<open>The compiled CFG\<close>

abbreviation "loop_cfg \<equiv>
  compile_prog (prog_table loop_prog) (prog_procs loop_prog)"

lemma loop_cfg_full:
  "loop_cfg =
     \<lparr> intra =
         {(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0),
          (Statement 0, EA_Assign (STR ''x'') (N 0), Statement 1),
          (Statement 1, EA_Assume (Less (V (STR ''x'')) (N 20)), Statement 2),
          (Statement 1, EA_AssumeNot (Less (V (STR ''x'')) (N 20)), Statement 3),
          (Statement 2, EA_Assign (STR ''x'') (Plus (V (STR ''x'')) (N 1)), Statement 1),
          (Statement 3, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))},
       calls = {},
       cfg_entry = FunctionEntry (STR ''main''),
       checks = {} \<rparr>"
  by eval

lemma loop_cfg_entry: "cfg_entry loop_cfg = FunctionEntry (STR ''main'')"
  by (simp add: loop_cfg_full)
lemma loop_cfg_calls: "calls loop_cfg = {}"
  by (simp add: loop_cfg_full)
lemma loop_cfg_intra:
  "intra loop_cfg =
     {(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0),
      (Statement 0, EA_Assign (STR ''x'') (N 0), Statement 1),
      (Statement 1, EA_Assume (Less (V (STR ''x'')) (N 20)), Statement 2),
      (Statement 1, EA_AssumeNot (Less (V (STR ''x'')) (N 20)), Statement 3),
      (Statement 2, EA_Assign (STR ''x'') (Plus (V (STR ''x'')) (N 1)), Statement 1),
      (Statement 3, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  by (simp add: loop_cfg_full)

subsection \<open>An exhibited interval post-fixpoint\<close>

text \<open>
  The loop head (node 1) stabilises at \<^verbatim>\<open>[0,20]\<close>: the join of \<^verbatim>\<open>x := 0\<close> flowing in
  directly from node 0 and \<^verbatim>\<open>x := x + 1\<close> flowing back from the body.  Guard
  refinement narrows the body entry (node 2) to \<^verbatim>\<open>[0,19]\<close>; applying the body's
  own assignment to that value gives \<^verbatim>\<open>[1,20]\<close>, which joined with the initial
  \<^verbatim>\<open>[0,0]\<close> is exactly the loop-head value -- a finite (non-widened) fixpoint.
  \<open>loop_env\<close> below exhibits these hand-picked values as ordinary input to the
  guard-refinement computation; the certified computed environment for this
  program is @{text "Exec_Interval_Run"}'s.
\<close>
definition loop_env :: "pp \<Rightarrow> ivl abs_state" where
  "loop_env v =
     (if v = Statement 2 then (\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 0) (Fin 19))
      else if v \<in> {Statement 1, Statement 3}
        then (\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 0) (Fin 20))
      else (\<lambda>_. Ivl MinInf PlusInf))"

subsection \<open>Backward guard refinement at the body entry\<close>

text \<open>
  Edge from node 2 to node 3 is @{const EA_Assume} on @{text "x < 20"}.  The body-entry
  interval @{text "[0,19]"} in @{const loop_env} is exactly
  @{const bfilter_ivl} applied at the loop head --- not widening and not join
  alone (identity assume would keep @{text "[0,20]"}; see
  @{text "Example_Guard_Refinement"}).
\<close>

abbreviation "loop_body_entry \<equiv> Statement 2"

lemma loop_head_guard_feasible:
  "feasible_ivl (Less (V (STR ''x'')) (N 20)) True (loop_env (Statement 1))"
  unfolding loop_env_def by simp eval

lemma bfilter_loop_head_state:
  "bfilter_ivl (Less (V (STR ''x'')) (N 20)) True (loop_env (Statement 1))
     = (\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 0) (Fin 19))"
  unfolding loop_env_def by (simp add: normalize_ivl_def)

lemma bfilter_loop_head_live:
  "\<not> is_empty_state (bfilter_ivl (Less (V (STR ''x'')) (N 20)) True (loop_env (Statement 1)))"
  unfolding bfilter_loop_head_state
  by (auto simp: is_empty_state_def is_bottom_ivl_def split: if_splits)

lemma loop_body_x_from_assume:
  "ivl_tf_abs (EA_Assume (Less (V (STR ''x'')) (N 20)))
     (loop_env (Statement 1)) (STR ''x'') = Ivl (Fin 0) (Fin 19)"
proof -
  have tf: "ivl_tf_abs (EA_Assume (Less (V (STR ''x'')) (N 20)))
              = branch_ivl (Less (V (STR ''x'')) (N 20)) True" by simp
  have "branch_ivl (Less (V (STR ''x'')) (N 20)) True (loop_env (Statement 1))
          = bfilter_ivl (Less (V (STR ''x'')) (N 20)) True (loop_env (Statement 1))"
    using loop_head_guard_feasible bfilter_loop_head_live
    by (simp add: ivl_backward_domain.branch_def ivl_backward_domain.branch_lifted_def)
  then show ?thesis
    unfolding tf bfilter_loop_head_state by simp
qed

lemma loop_body_entry_x:
  "loop_env loop_body_entry (STR ''x'') = Ivl (Fin 0) (Fin 19)"
  by (simp add: loop_env_def)

subsection \<open>The environment is a post-fixpoint of this program's equations\<close>

text \<open>
  The negated guard is the one edge the lemmas above leave out: at the loop head
  it narrows \<open>x\<close> to \<open>[20,20]\<close>, which the exit value \<open>[0,20]\<close> already contains.
\<close>

lemma loop_head_guard_feasible_neg:
  "feasible_ivl (Less (V (STR ''x'')) (N 20)) False (loop_env (Statement 1))"
  unfolding loop_env_def by simp eval

lemma bfilter_loop_head_state_neg:
  "bfilter_ivl (Less (V (STR ''x'')) (N 20)) False (loop_env (Statement 1))
     = (\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 20) (Fin 20))"
  unfolding loop_env_def by (simp add: normalize_ivl_def)

lemma bfilter_loop_head_live_neg:
  "\<not> is_empty_state
       (bfilter_ivl (Less (V (STR ''x'')) (N 20)) False (loop_env (Statement 1)))"
  unfolding bfilter_loop_head_state_neg
  by (auto simp: is_empty_state_def is_bottom_ivl_def split: if_splits)

lemma loop_env_head:
  "loop_env (Statement 1)
     = (\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 0) (Fin 20))"
  by (simp add: loop_env_def)

lemma branch_at_head_true:
  "branch_ivl (Less (V (STR ''x'')) (N 20)) True
     ((\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 0) (Fin 20)))
   = (\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 0) (Fin 19))"
  using loop_head_guard_feasible bfilter_loop_head_live
  unfolding loop_env_head[symmetric] bfilter_loop_head_state[symmetric]
  by (simp add: ivl_backward_domain.branch_def ivl_backward_domain.branch_lifted_def)

lemma branch_at_head_false:
  "branch_ivl (Less (V (STR ''x'')) (N 20)) False
     ((\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 0) (Fin 20)))
   = (\<lambda>_. Ivl MinInf PlusInf)((STR ''x'') := Ivl (Fin 20) (Fin 20))"
  using loop_head_guard_feasible_neg bfilter_loop_head_live_neg
  unfolding loop_env_head[symmetric] bfilter_loop_head_state_neg[symmetric]
  by (simp add: ivl_backward_domain.branch_def ivl_backward_domain.branch_lifted_def)

theorem loop_env_post_fixpoint:
  "\<forall>(u, a, v) \<in> intra loop_cfg. ivl_tf_abs a (loop_env u) \<le> loop_env v"
  unfolding loop_cfg_intra
  by (auto simp: loop_env_def branch_at_head_true branch_at_head_false
                 ivl_tf.assign_def ivl_tf.body_def ivl_tf.ret_def
                 le_fun_def less_eq_ivl_def normalize_ivl_def)

end


