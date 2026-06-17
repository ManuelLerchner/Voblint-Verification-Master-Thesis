theory Sign_Exec_Sound
  imports Sign_Exec Sign_Side_IP_Soundness
          "Voblint_CFG.CFG_Collect_Trace_IP" "TD.TD_side_upd_rule"
          "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Executable sign analysis: the computed result and its certified soundness\<close>

text \<open>
  High-level vocabulary for the executable analyzer, so example statements read
  at the level of intent rather than solver plumbing:

    \<^item> \<open>sign_exec_raw \<Pi> ps main\<close>  -- the raw solver solution (\<open>pp + unit => sign st\<close>),
      code-generating, the thing @{command value} / \<open>eval\<close> evaluates;
    \<^item> \<open>sign_exec \<Pi> ps main\<close>      -- the analyzer's computed abstract state at the
      program exit (a \<open>sign abs_state\<close>), read back through \<open>fun_of_st\<close>;
    \<^item> \<open>sign_exec_terminates \<Pi> ps main\<close> -- the single assumption: the vendored
      solver terminates on this program.

  \<open>sign_exec_sound_collecting\<close> / \<open>sign_exec_sound_trace\<close> are the program-parametric
  soundness theorems; concrete examples only fix a program and instantiate them.
\<close>

definition sign_exec_eqs ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp, unit, sign st) eqsT" where
  "sign_exec_eqs \<Pi> ps main = side_cfg_T_ip_st_prog \<Pi> ps main sign_tf_st bot top_sign_st"

definition sign_exec_raw ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp + unit \<Rightarrow> sign st)" where
  "sign_exec_raw \<Pi> ps main =
     snd (TD_side_always_join_Interp_solve (sign_exec_eqs \<Pi> ps main)
            (cfg_exit (compile_prog \<Pi> ps main)))"

definition sign_exec ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> sign abs_state" where
  "sign_exec \<Pi> ps main =
     side_env (fun_of_st \<circ> sign_exec_raw \<Pi> ps main) (cfg_exit (compile_prog \<Pi> ps main))"

definition sign_exec_terminates ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> bool" where
  "sign_exec_terminates \<Pi> ps main =
     TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign st)
        (sign_exec_eqs \<Pi> ps main) (cfg_exit (compile_prog \<Pi> ps main))"

text \<open>
  Discharging termination by execution.  When the vendored side solver's
  executable @{const TD_side_always_join_Interp_solve_c} returns a result on a
  concrete program, that program lies in the solver's domain, so
  @{const sign_exec_terminates} holds.  The bridge is the solver's
  @{thm TD_side_always_join_Interp.term_equivalence}
  (\<open>solve_dom x \<longleftrightarrow> solve_c_dom x\<close>): the option-valued @{const TD_side_always_join_Interp_solve_c}
  code-generates, so examples discharge the premise by @{method eval}, turning
  the soundness assumption into a proved fact.
\<close>

lemma sign_exec_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (sign_exec_eqs \<Pi> ps main)
             (cfg_exit (compile_prog \<Pi> ps main)) \<noteq> None"
  shows "sign_exec_terminates \<Pi> ps main"
  unfolding sign_exec_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by (simp add: not_None_eq)

text \<open>
  Soundness at the state level: from any input, every store reaching the exit
  under the interprocedural collecting semantics is over-approximated by the
  computed result.  The seed is top (\<open>top_sign_st\<close>), whose concretization is the
  whole store space, so the statement is non-vacuous.
\<close>

theorem sign_exec_sound_collecting:
  assumes solves: "sign_exec_terminates \<Pi> ps main"
  shows "cfg_collect_ip (compile_prog \<Pi> ps main) UNIV (cfg_exit (compile_prog \<Pi> ps main))
         \<le> sign_domain.gamma_state (sign_exec \<Pi> ps main)"
proof -
  define g where "g = compile_prog \<Pi> ps main"
  define sol where "sol = TD_side_always_join_Interp_solve (sign_exec_eqs \<Pi> ps main) (cfg_exit g)"
  define \<sigma> :: "pp + unit \<Rightarrow> sign abs_state" where "\<sigma> = fun_of_st \<circ> snd sol"
  have fin: "finite (edges g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)" unfolding g_def using compile_prog_finite by simp
  have dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign st)
               (sign_exec_eqs \<Pi> ps main) (cfg_exit g)"
    using solves unfolding sign_exec_terminates_def g_def by simp
  have pp0: "part_post_solution (sign_exec_eqs \<Pi> ps main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_always_join_Interp.partial_post_solution[OF dom]
    by (metis sol_def prod.collapse)
  have pp_st: "part_post_solution (side_cfg_T_ip_st g sign_tf_st bot top_sign_st)
                 (cfg_exit g) (snd sol) (fst sol)"
    using side_cfg_T_ip_st_prog_part_post'[OF pp0[unfolded sign_exec_eqs_def]]
    by (simp add: g_def)
  have pp_abs: "part_post_solution (side_cfg_T_ip g sign_tf (\<squnion>) bot (\<lambda>_. STop))
                  (cfg_exit g) \<sigma> (fst sol)"
    using part_post_solution_st_to_abs[OF sign_tf_st_commute pp_st]
    by (simp add: \<sigma>_def fun_of_st_bot fun_of_st_top_sign_st bot_fun_def)
  have reach: "ip_reaches g (cfg_entry g) (cfg_exit g)"
    by (simp add: g_def compile_prog_entry_ip_reaches_exit)
  have entry_in: "cfg_entry g \<in> fst sol"
    by (rule side_ip_cone_in_vars[OF pp_abs fin finC reach])
  have entry_le: "(\<lambda>_. STop) \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_ip[OF pp_abs entry_in])
  have entry_cov: "UNIV \<le> sign_domain.gamma_state (side_env \<sigma> (cfg_entry g))"
    using sign_domain.gamma_state_mono[OF entry_le]
    by (simp add: sign_domain.gamma_state_def)
  have "cfg_collect_ip g UNIV (cfg_exit g)
        \<le> sign_domain.gamma_state (side_env \<sigma> (cfg_exit g))"
    using sound_transfer.side_collect_sound_ip_exit_pruned
            [OF sign_sound_tf.sound_transfer_axioms pp_abs fin finC entry_cov] .
  then show ?thesis
    by (simp add: g_def \<sigma>_def sol_def sign_exec_def sign_exec_raw_def)
qed

text \<open>
  Soundness against the underlying interprocedural trace semantics: for any
  reaching trace, the value of every variable at the end of the trace is
  over-approximated.  This is the projection (\<open>alpha_last\<close>) of the trace
  collecting semantics composed with the state-level bound.
\<close>

theorem sign_exec_sound_trace:
  assumes solves: "sign_exec_terminates \<Pi> ps main"
  assumes tr: "tr \<in> cfg_collect_trace_ip (compile_prog \<Pi> ps main) UNIV
                       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "last tr \<in> sign_domain.gamma_state (sign_exec \<Pi> ps main)"
proof -
  from tr have "last tr \<in> alpha_last (cfg_collect_trace_ip (compile_prog \<Pi> ps main) UNIV
                                        (cfg_exit (compile_prog \<Pi> ps main)))"
    by (auto simp: alpha_last_def)
  moreover have "alpha_last (cfg_collect_trace_ip (compile_prog \<Pi> ps main) UNIV
                              (cfg_exit (compile_prog \<Pi> ps main)))
                 \<le> sign_domain.gamma_state (sign_exec \<Pi> ps main)"
    using alpha_last_cfg_collect_trace_ip_le sign_exec_sound_collecting[OF solves]
    by (rule subset_trans)
  ultimately show ?thesis by blast
qed

section \<open>Whole-program convenience layer\<close>

text \<open>
  An @{type imp_prog} written with the \<open>\<lbrakk> \<dots> \<rbrakk>\<close> bracket already bundles the
  procedure table, procedure-name list, and main command.  The wrappers below
  feed those three projections to the analyzer in one step, so example
  statements name the program once instead of repeating the triple.
\<close>

definition prog_cfg :: "imp_prog \<Rightarrow> cfg" where
  "prog_cfg p = compile_prog (prog_table p) (prog_procs p) (prog_main p)"

definition sign_exec_prog :: "imp_prog \<Rightarrow> sign abs_state" where
  "sign_exec_prog p = sign_exec (prog_table p) (prog_procs p) (prog_main p)"

definition sign_terminates_prog :: "imp_prog \<Rightarrow> bool" where
  "sign_terminates_prog p = sign_exec_terminates (prog_table p) (prog_procs p) (prog_main p)"

lemma sign_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (sign_exec_eqs (prog_table p) (prog_procs p) (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) (prog_main p))) \<noteq> None"
  shows "sign_terminates_prog p"
  unfolding sign_terminates_prog_def
  using assms by (rule sign_exec_terminates_via_solve_c)

corollary sign_exec_prog_sound_collecting:
  assumes "sign_terminates_prog p"
  shows "cfg_collect_ip (prog_cfg p) UNIV (cfg_exit (prog_cfg p))
           \<le> sign_domain.gamma_state (sign_exec_prog p)"
  using assms unfolding sign_terminates_prog_def prog_cfg_def sign_exec_prog_def
  by (rule sign_exec_sound_collecting)

corollary sign_exec_prog_sound_trace:
  assumes "sign_terminates_prog p"
      and "tr \<in> cfg_collect_trace_ip (prog_cfg p) UNIV (cfg_exit (prog_cfg p))"
  shows "last tr \<in> sign_domain.gamma_state (sign_exec_prog p)"
  using assms unfolding sign_terminates_prog_def prog_cfg_def sign_exec_prog_def
  by (rule sign_exec_sound_trace)

end
