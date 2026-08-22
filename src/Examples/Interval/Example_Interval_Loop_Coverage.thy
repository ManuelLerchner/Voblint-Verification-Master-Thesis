section \<open>Example: Interval Analysis of a Full Bounded Loop Program\<close>

theory Example_Interval_Loop_Coverage
  imports Voblint_CFG.CFG_Prune
    "Voblint_Analysis.Interval_Domain"
    "Voblint_VIMP.VIMP_Notation"
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
     void main() { x := 0; while (x < 20) { x := x + 1 } }
   }"

subsection \<open>The compiled CFG\<close>

abbreviation "loop_cfg \<equiv>
  compile_prog (prog_table loop_prog) (prog_procs loop_prog) prog_main_name (prog_main loop_prog)"

lemma loop_cfg_full:
  "loop_cfg =
     \<lparr> intra =
         {(FunctionEntry (STR ''main''), EA_Nop, Statement 0),
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
     {(FunctionEntry (STR ''main''), EA_Nop, Statement 0),
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

lemma loop_body_x_from_assume:
  "tf_branch (ivl_tf_for gs) (Less (V (STR ''x'')) (N 20)) True (loop_env (Statement 1)) (STR ''x'') = Ivl (Fin 0) (Fin 19)"
proof -
  have "tf_branch (ivl_tf_for gs) = branch_ivl" by (simp add: ivl_tf_for_def)
  then show ?thesis unfolding loop_env_def by (simp only:) eval
qed

lemma loop_body_entry_x:
  "loop_env loop_body_entry (STR ''x'') = Ivl (Fin 0) (Fin 19)"
  by (simp add: loop_env_def)

end


