section \<open>Example: checks_proven/checks_proven_sound alone, store-only, Interval\<close>

theory Example_Interval_Checks_Store_Only
  imports "Voblint_Core.Checks" "Voblint_Analysis.Interval_Exec_Sound" "Voblint_Analysis.Interval_Checks"
          "Voblint_Analysis.Sign_Checks" "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

text \<open>
  The Interval analogue of \<open>Example_Checks_Store_Only\<close> (Sign): exercises
  \<^const>\<open>checks_proven\<close> against a computed Interval post-solution, discharged
  node-locally through \<open>Interval_Checks\<close> rather than by forwarding stores to
  the procedure exit. Unlike the Sign example, the checks sit inside a guard
  that bounds \<open>x\<close> on both sides (\<open>0 < x \<and> x < 10\<close>), so Interval's numeric
  bounds --- not just its sign --- narrow the checked variable.
\<close>

definition checks_ivl_ex_program :: imp_prog where
  "checks_ivl_ex_program = program {
     void main() {
       x := random();
       if (0 < x && x < 10) {
         __voblint_check(x < 11);
         __voblint_check(x < 0);
         __voblint_check(x == 5)
       } else {
         y := 0
       }
     }
   }"

text \<open>Computed, not asserted: the three \<open>__voblint_check(...)\<close> statements land
  at the nodes \<^const>\<open>compile\<close> actually assigns them, inside the guarded
  branch.\<close>
lemma checks_ivl_ex_checks_eval:
  "checks (prog_cfg ''main'' checks_ivl_ex_program) =
     {(Statement 2, Less (V ''x'') (N 11)),
      (Statement 3, Less (V ''x'') (N 0)),
      (Statement 4, Eq (V ''x'') (N 5))}"
  unfolding prog_cfg_def by eval

lemma checks_ivl_ex_solver_terminates: "ivl_terminates_prog ''main'' checks_ivl_ex_program"
  by (rule ivl_terminates_prog_via_solve_c) eval

definition checks_ivl_ex_reach :: "pp \<Rightarrow> store set" where
  "checks_ivl_ex_reach v = ltr_collect is_global (prog_cfg ''main'' checks_ivl_ex_program) (cinit_stores is_global) v"

text \<open>The computed Interval environment at an arbitrary node, not fixed to the
  exit: \<^const>\<open>ivl_exec_prog_at\<close> queries the same solver result
  \<^const>\<open>ivl_exec_prog\<close> reads only at the exit.\<close>
definition checks_ivl_ex_env :: "pp \<Rightarrow> ivl abs_state" where
  "checks_ivl_ex_env v = ivl_exec_prog_at ''main'' checks_ivl_ex_program v"

text \<open>The compiled edges, read off \<^const>\<open>prog_cfg\<close>'s own \<open>eval\<close>-computed
  shape: \<open>Statement 1\<close> (\<open>x := random()\<close>'s successor) branches on
  \<open>0 < x \<and> x < 10\<close> to \<open>Statement 2\<close> (the guarded branch, holding all three
  checks) or to \<open>Statement 5\<close> (\<open>y := 0\<close>, the else branch); both rejoin at
  \<open>Statement 6\<close>.\<close>
lemma checks_ivl_ex_intra_eval:
  "intra (prog_cfg ''main'' checks_ivl_ex_program) =
     {(FunctionEntry ''main'', EA_Nop, Statement 0),
      (Statement 0, EA_Random ''x'', Statement 1),
      (Statement 1, EA_Assume (And (Less (N 0) (V ''x'')) (Less (V ''x'') (N 10))), Statement 2),
      (Statement 1, EA_AssumeNot (And (Less (N 0) (V ''x'')) (Less (V ''x'') (N 10))), Statement 5),
      (Statement 2, EA_Check (Less (V ''x'') (N 11)), Statement 3),
      (Statement 3, EA_Check (Less (V ''x'') (N 0)), Statement 4),
      (Statement 4, EA_Check (Eq (V ''x'') (N 5)), Statement 6),
      (Statement 5, EA_Assign ''y'' (N 0), Statement 6),
      (Statement 6, EA_Ret None ''main'', FunctionResult ''main'')}"
  unfolding prog_cfg_def by eval

lemma checks_ivl_ex_exit_eval: "cfg_exit (prog_cfg ''main'' checks_ivl_ex_program) = FunctionResult ''main''"
  unfolding prog_cfg_def by eval

lemma checks_ivl_ex_entry_eval: "cfg_entry (prog_cfg ''main'' checks_ivl_ex_program) = FunctionEntry ''main''"
  unfolding prog_cfg_def by eval

text \<open>Structural reachability to the exit, for each check node --- a fact
  about the CFG's shape, not about any concrete store: it does not forward
  stores.\<close>
lemma checks_ivl_ex_statement2_reaches_exit:
  "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 2)
     (cfg_exit (prog_cfg ''main'' checks_ivl_ex_program))"
proof -
  have r2: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 2) (Statement 3)"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  have r3: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 3) (Statement 4)"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  have r4: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 4) (Statement 6)"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  have r6: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 6) (FunctionResult ''main'')"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  show ?thesis
    unfolding checks_ivl_ex_exit_eval
    using r2 r3 r4 r6 cfg_reaches_trans by blast
qed

lemma checks_ivl_ex_statement3_reaches_exit:
  "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 3)
     (cfg_exit (prog_cfg ''main'' checks_ivl_ex_program))"
proof -
  have r3: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 3) (Statement 4)"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  have r4: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 4) (Statement 6)"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  have r6: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 6) (FunctionResult ''main'')"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  show ?thesis
    unfolding checks_ivl_ex_exit_eval
    using r3 r4 r6 cfg_reaches_trans by blast
qed

lemma checks_ivl_ex_statement4_reaches_exit:
  "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 4)
     (cfg_exit (prog_cfg ''main'' checks_ivl_ex_program))"
proof -
  have r4: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 4) (Statement 6)"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  have r6: "cfg_reaches (prog_cfg ''main'' checks_ivl_ex_program) (Statement 6) (FunctionResult ''main'')"
    by (rule cfg_reaches_intra) (simp add: checks_ivl_ex_intra_eval)
  show ?thesis
    unfolding checks_ivl_ex_exit_eval
    using r4 r6 cfg_reaches_trans by blast
qed

text \<open>Node-local collecting soundness at each check node, via
  \<open>ivl_exec_prog_sound_collecting_at\<close> and the reachability facts above ---
  no store is forwarded to the exit.\<close>
lemma checks_ivl_ex_node_sound_2:
  "checks_ivl_ex_reach (Statement 2) \<le> \<lbrakk>checks_ivl_ex_env (Statement 2)\<rbrakk>"
  unfolding checks_ivl_ex_reach_def checks_ivl_ex_env_def
  by (rule ivl_exec_prog_sound_collecting_at[OF checks_ivl_ex_solver_terminates checks_ivl_ex_statement2_reaches_exit])

lemma checks_ivl_ex_node_sound_3:
  "checks_ivl_ex_reach (Statement 3) \<le> \<lbrakk>checks_ivl_ex_env (Statement 3)\<rbrakk>"
  unfolding checks_ivl_ex_reach_def checks_ivl_ex_env_def
  by (rule ivl_exec_prog_sound_collecting_at[OF checks_ivl_ex_solver_terminates checks_ivl_ex_statement3_reaches_exit])

lemma checks_ivl_ex_node_sound_4:
  "checks_ivl_ex_reach (Statement 4) \<le> \<lbrakk>checks_ivl_ex_env (Statement 4)\<rbrakk>"
  unfolding checks_ivl_ex_reach_def checks_ivl_ex_env_def
  by (rule ivl_exec_prog_sound_collecting_at[OF checks_ivl_ex_solver_terminates checks_ivl_ex_statement4_reaches_exit])

text \<open>Executable classification at each check's own node --- the guard
  \<open>0 < x \<and> x < 10\<close> narrows \<open>x\<close> to \<open>[1,9]\<close> at \<open>Statement 2\<close>, so \<open>x < 11\<close> is
  proved and \<open>x < 0\<close> is refuted outright; \<open>x = 5\<close> stays unknown since \<open>x\<close>
  ranges over the whole \<open>[1,9]\<close> interval, not just \<open>5\<close>.\<close>
lemma checks_ivl_ex_classify_2:
  "interval_classify_check (Less (V ''x'') (N 11)) (checks_ivl_ex_env (Statement 2)) = Check_Proved"
  unfolding checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_classify_3:
  "interval_classify_check (Less (V ''x'') (N 0)) (checks_ivl_ex_env (Statement 3)) = Check_Refuted"
  unfolding checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_classify_4:
  "interval_classify_check (Eq (V ''x'') (N 5)) (checks_ivl_ex_env (Statement 4)) = Check_Unknown"
  unfolding checks_ivl_ex_env_def by eval

text \<open>The precision comparison: Sign only ever tracks the sign of \<open>x\<close>, so
  after \<open>0 < x\<close> its best abstraction is \<open>SPos\<close> --- \<open>x < 10\<close> narrows nothing
  further in that lattice, and \<open>SPos\<close> alone cannot prove \<open>x < 11\<close> (a
  \<open>SPos\<close> value like \<open>1000000\<close> is not \<open>< 11\<close>). Interval proves it outright
  because it tracks the upper bound \<open>9\<close> directly, not merely the sign.\<close>
lemma checks_ivl_ex_precision_over_sign:
  "sign_classify_check (Less (V ''x'') (N 11)) ((\<lambda>_. STop)(''x'' := SPos)) = Check_Unknown"
  by eval

text \<open>The payoff: the proved check's condition genuinely holds at every
  reaching store, and the refuted check's condition genuinely fails at every
  reaching store --- both derived from \<^const>\<open>interval_classify_check\<close> plus
  node-local collecting soundness, with no store forwarded between check
  nodes. The unknown check gets no such corollary, by design.\<close>

corollary checks_ivl_ex_first_check_holds:
  assumes "t \<in> checks_ivl_ex_reach (Statement 2)"
  shows "bval (Less (V ''x'') (N 11)) t"
proof -
  have "t \<in> \<lbrakk>checks_ivl_ex_env (Statement 2)\<rbrakk>" using checks_ivl_ex_node_sound_2 assms by blast
  then show ?thesis using interval_classify_check_proved[OF checks_ivl_ex_classify_2] by blast
qed

corollary checks_ivl_ex_second_check_refuted:
  assumes "t \<in> checks_ivl_ex_reach (Statement 3)"
  shows "\<not> bval (Less (V ''x'') (N 0)) t"
proof -
  have "t \<in> \<lbrakk>checks_ivl_ex_env (Statement 3)\<rbrakk>" using checks_ivl_ex_node_sound_3 assms by blast
  then show ?thesis using interval_classify_check_refuted[OF checks_ivl_ex_classify_3] by blast
qed

text \<open>The generic \<^const>\<open>checks_proven\<close>/\<^theory>\<open>Voblint_Core.Checks\<close> bridge,
  exercised on exactly the checks that are actually true: the compiler's own
  \<^const>\<open>checks\<close> table names all three, but a blanket \<open>checks_proven\<close> over the
  whole table would be a false statement here, since the second check is a
  genuine bug (refuted, not merely unproven). Restricting to the singleton
  \<open>{(Statement 2, Less (V ''x'') (N 11))}\<close> keeps the bridge theorem
  meaningful.\<close>

lemma checks_ivl_ex_proven_check_discharged:
  "interval_checks_proven {(Statement 2, Less (V ''x'') (N 11))} checks_ivl_ex_env"
proof (rule interval_checks_provenI)
  fix v :: pp and cnd :: bexp
  assume mem: "(v, cnd) \<in> {(Statement 2, Less (V ''x'') (N 11))}"
  then have v_eq: "v = Statement 2" and cnd_eq: "cnd = Less (V ''x'') (N 11)" by auto
  show "interval_check_true cnd (checks_ivl_ex_env v)"
    unfolding v_eq cnd_eq checks_ivl_ex_env_def by eval
qed

lemma checks_ivl_ex_proven_check_checks_proven:
  "checks_proven {(Statement 2, Less (V ''x'') (N 11))} checks_ivl_ex_reach"
proof (rule interval_checks_proven_sound)
  fix v :: pp and cnd :: bexp
  assume "(v, cnd) \<in> {(Statement 2, Less (V ''x'') (N 11))}"
  then show "checks_ivl_ex_reach v \<le> \<lbrakk>checks_ivl_ex_env v\<rbrakk>"
    using checks_ivl_ex_node_sound_2 by auto
next
  show "interval_checks_proven {(Statement 2, Less (V ''x'') (N 11))} checks_ivl_ex_env"
    by (rule checks_ivl_ex_proven_check_discharged)
qed

text \<open>Non-vacuity: \<open>checks_ivl_ex_reach\<close> is not merely vacuously true because
  no store ever reaches these nodes. The all-zero store, admissible as an
  initial \<^const>\<open>cinit_stores\<close> witness, runs the compiled prefix, picks
  \<open>x := 5\<close> at the \<open>random()\<close> step (satisfying the guard \<open>0 < x \<and> x < 10\<close>),
  and reaches the guarded branch holding all three checks.\<close>
lemma checks_ivl_ex_reach2_nonempty: "checks_ivl_ex_reach (Statement 2) \<noteq> {}"
proof -
  have zero_init: "(\<lambda>_. 0) \<in> cinit_stores is_global" unfolding cinit_stores_def by simp
  have s0: "(\<lambda>_. 0) \<in> checks_ivl_ex_reach (FunctionEntry ''main'')"
  proof -
    have "(\<lambda>_. 0) \<in> ltr_collect is_global (prog_cfg ''main'' checks_ivl_ex_program) (cinit_stores is_global)
            (cfg_entry (prog_cfg ''main'' checks_ivl_ex_program))"
      by (rule ltr_collect_init[OF zero_init])
    then show ?thesis unfolding checks_ivl_ex_reach_def checks_ivl_ex_entry_eval .
  qed
  have e0: "(FunctionEntry ''main'', EA_Nop, Statement 0) \<in> intra (prog_cfg ''main'' checks_ivl_ex_program)"
    by (simp add: checks_ivl_ex_intra_eval)
  have s1: "(\<lambda>_. 0) \<in> checks_ivl_ex_reach (Statement 0)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" is_global "prog_cfg ''main'' checks_ivl_ex_program"
        "cinit_stores is_global" "FunctionEntry ''main''" EA_Nop "Statement 0"]
    using s0 e0 unfolding checks_ivl_ex_reach_def by simp
  have e1: "(Statement 0, EA_Random ''x'', Statement 1) \<in> intra (prog_cfg ''main'' checks_ivl_ex_program)"
    by (simp add: checks_ivl_ex_intra_eval)
  have s2: "(\<lambda>_. 0)(''x'' := 5) \<in> checks_ivl_ex_reach (Statement 1)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" is_global "prog_cfg ''main'' checks_ivl_ex_program"
        "cinit_stores is_global" "Statement 0" "EA_Random ''x''" "Statement 1"
        "(\<lambda>_. 0)(''x'' := 5)"]
    using s1 e1 unfolding checks_ivl_ex_reach_def by force
  have e2: "(Statement 1, EA_Assume (And (Less (N 0) (V ''x'')) (Less (V ''x'') (N 10))), Statement 2)
              \<in> intra (prog_cfg ''main'' checks_ivl_ex_program)"
    by (simp add: checks_ivl_ex_intra_eval)
  have "(\<lambda>_. 0)(''x'' := 5) \<in> checks_ivl_ex_reach (Statement 2)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)(''x'' := 5)" is_global "prog_cfg ''main'' checks_ivl_ex_program"
        "cinit_stores is_global" "Statement 1" "EA_Assume (And (Less (N 0) (V ''x'')) (Less (V ''x'') (N 10)))"
        "Statement 2" "(\<lambda>_. 0)(''x'' := 5)"]
    using s2 e2 unfolding checks_ivl_ex_reach_def by simp
  then show ?thesis by blast
qed

subsection \<open>CFG rendering, checks colored by executable classification\<close>

text \<open>
  The compiled CFG is rendered through the same generic
  \<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close> pipeline every other example uses,
  through the same \<^const>\<open>check_result_annotation\<close> status-to-style mapping
  \<open>Example_Checks_Store_Only\<close> (Sign) uses --- shared there, not redefined
  here, confirming the mapping is analysis-independent: no Interval-specific
  rendering code was needed. The color is \<^const>\<open>interval_classify_check\<close>
  applied to the computed \<^const>\<open>checks_ivl_ex_env\<close> at each check's own node.
\<close>

definition checks_ivl_ex_check_at :: "pp \<Rightarrow> bexp option" where
  "checks_ivl_ex_check_at v =
     (if v = Statement 2 then Some (Less (V ''x'') (N 11))
      else if v = Statement 3 then Some (Less (V ''x'') (N 0))
      else if v = Statement 4 then Some (Eq (V ''x'') (N 5))
      else None)"

definition checks_ivl_ex_node_annotation :: "pp \<Rightarrow> graphviz_node_annotation option" where
  "checks_ivl_ex_node_annotation v =
     (case checks_ivl_ex_check_at v of
        Some cnd \<Rightarrow> Some (check_result_annotation (interval_classify_check cnd (checks_ivl_ex_env v)) cnd)
      | None \<Rightarrow>
          if v = FunctionResult ''main'' then
            Some (Node_Annotation ''''
              ''shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray'')
          else None)"

text \<open>Validation that the generic renderer's hook actually carries all three
  computed classifications, not merely that this file's check table intends
  them to.\<close>

lemma checks_ivl_ex_annotation_proved:
  "checks_ivl_ex_node_annotation (Statement 2) =
     Some (check_result_annotation Check_Proved (Less (V ''x'') (N 11)))"
  unfolding checks_ivl_ex_node_annotation_def checks_ivl_ex_check_at_def checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_annotation_refuted:
  "checks_ivl_ex_node_annotation (Statement 3) =
     Some (check_result_annotation Check_Refuted (Less (V ''x'') (N 0)))"
  unfolding checks_ivl_ex_node_annotation_def checks_ivl_ex_check_at_def checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_annotation_unknown:
  "checks_ivl_ex_node_annotation (Statement 4) =
     Some (check_result_annotation Check_Unknown (Eq (V ''x'') (N 5)))"
  unfolding checks_ivl_ex_node_annotation_def checks_ivl_ex_check_at_def checks_ivl_ex_env_def by eval

definition checks_ivl_ex_dot_lit :: String.literal where
  "checks_ivl_ex_dot_lit =
     raw_cfg_dot_lit (prog_table checks_ivl_ex_program) (prog_procs checks_ivl_ex_program)
       ''main'' (prog_main checks_ivl_ex_program) checks_ivl_ex_node_annotation"

ML_val \<open>
  writeln (@{code checks_ivl_ex_dot_lit})
\<close>

subsection \<open>Fully annotated CFG: computed Interval value at every node\<close>

text \<open>
  \<^const>\<open>ivl_annotated_dot_prog_lit\<close> renders the same compiled CFG with every
  node labelled by its own computed \<^const>\<open>ivl_exec_prog_at\<close> value --- the
  full per-node abstract environment, not only the three check nodes above.
  \<open>x\<close> shows \<^term>\<open>ivl_top\<close> before \<open>random()\<close> runs, then \<open>[1,9]\<close> on the
  guarded branch and its unconstrained complement on the \<open>else\<close> branch,
  visibly rejoining at \<open>Statement 6\<close>.
\<close>

definition checks_ivl_ex_mnm :: pname where
  "checks_ivl_ex_mnm = ''main''"

ML_val \<open>
  writeln (@{code ivl_annotated_dot_prog_lit} @{code checks_ivl_ex_mnm} @{code checks_ivl_ex_program})
\<close>

end
