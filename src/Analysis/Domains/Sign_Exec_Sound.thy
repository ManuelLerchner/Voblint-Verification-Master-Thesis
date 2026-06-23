theory Sign_Exec_Sound
  imports Sign_Exec Sign_Side_Soundness
          "Voblint_CFG.CFG_Collect_Trace" "TD.TD_side_upd_rule"
          "Voblint_IMP2.IMP2_Notation"
          Analysis_GraphViz
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
  "sign_exec_eqs \<Pi> ps main =
     side_cfg_T_st (compile_prog \<Pi> ps main) sign_tf_st bot cinit_sign_st"

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
  using assms by simp

text \<open>
  Soundness at the state level: starting from any C-faithful initial store
  (globals zero, locals arbitrary), every store reaching the exit under the
  interprocedural collecting semantics is over-approximated by the computed
  result.  Switching the seed from \<open>top_sign_st\<close> to \<open>cinit_sign_st\<close> (globals
  at \<open>SZero\<close>) lets the richer lattice give tighter global bounds, e.g.\
  \<open>Gresult = SNonNeg\<close> instead of \<open>STop\<close>.
\<close>

theorem sign_exec_sound_collecting:
  assumes solves: "sign_exec_terminates \<Pi> ps main"
  shows "cfg_collect (compile_prog \<Pi> ps main) cinit_stores (cfg_exit (compile_prog \<Pi> ps main))
         \<le> \<lbrakk>sign_exec \<Pi> ps main\<rbrakk>"
proof -
  define g :: cfg where "g = compile_prog \<Pi> ps main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> sign st)" where
    "sol = TD_side_always_join_Interp_solve (sign_exec_eqs \<Pi> ps main) (cfg_exit g)"
  define \<sigma> :: "pp + unit \<Rightarrow> sign abs_state" where "\<sigma> = fun_of_st \<circ> snd sol"
  have fin: "finite (edges g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)" unfolding g_def using compile_prog_finite by simp
  have dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign st)
               (sign_exec_eqs \<Pi> ps main) (cfg_exit g)"
    using solves unfolding sign_exec_terminates_def g_def by simp
  have pp0: "part_post_solution (sign_exec_eqs \<Pi> ps main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_always_join_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_st g sign_tf_st bot cinit_sign_st)
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0 by (simp add: sign_exec_eqs_def g_def)
  interpret se: sound_effectful_transfer sign_etf
    by (rule sign_sound_etf)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff g sign_etf bot
                     (\<lambda>x. if is_global x then SZero else STop) ())
                  (cfg_exit g) \<sigma> (fst sol)"
    using part_post_solution_st_to_abs_eff[OF sign_tf_st_commute pp_st]
    unfolding sign_etf_def
    by (simp add: \<sigma>_def fun_of_st_cinit_sign_st bot_fun_def)
  have ed: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf sign_etf b z)"
    unfolding sign_etf_def by (rule dep_aux_apply_etf_from_tf_src)
  have cd1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine sign_etf c2 e2)"
    unfolding sign_etf_def by (rule dep_aux_etf_combine_from_tf_call)
  have cd2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine sign_etf c2 e2)"
    unfolding sign_etf_def by (rule dep_aux_etf_combine_from_tf_exit)
  have es: "\<And>a u. static_deps (apply_etf sign_etf a u)"
    unfolding sign_etf_def by (rule static_deps_apply_etf_from_tf)
  have cs: "\<And>cc ex. static_deps (etf_combine sign_etf cc ex)"
    unfolding sign_etf_def by (rule static_deps_etf_combine_from_tf)
  have reach: "cfg_reaches g (cfg_entry g) (cfg_exit g)"
    by (simp add: g_def compile_prog_entry_cfg_reaches_exit)
  have entry_in: "cfg_entry g \<in> fst sol"
    by (rule side_cone_in_vars_eff[OF pp_eff fin finC ed cd1 cd2 es cs reach])
  have entry_le: "(\<lambda>x. if is_global x then SZero else STop) \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores \<subseteq> \<lbrakk>\<lambda>x. if is_global x then SZero else STop\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_cov: "cinit_stores \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using seed_cov gamma_state_mono[OF entry_le] by (rule subset_trans)
  have "cfg_collect g cinit_stores (cfg_exit g)
        \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
    by (rule side_collect_sound_exit_pruned_eff
          [OF sign_sound_etf pp_eff fin finC entry_cov ed cd1 cd2 es cs])
  then show ?thesis
    by (simp add: g_def \<sigma>_def sol_def sign_exec_def sign_exec_raw_def)
qed

text \<open>
  Soundness against the underlying interprocedural trace semantics: for any
  C-faithful reaching trace, the value of every variable at the end of the
  trace is over-approximated.
\<close>

theorem sign_exec_sound_trace:
  assumes solves: "sign_exec_terminates \<Pi> ps main"
  assumes tr: "tr \<in> cfg_collect_trace (compile_prog \<Pi> ps main) cinit_stores
                       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "last tr \<in> \<lbrakk>sign_exec \<Pi> ps main\<rbrakk>"
proof -
  from tr have "last tr \<in> alpha_last (cfg_collect_trace (compile_prog \<Pi> ps main) cinit_stores
                                        (cfg_exit (compile_prog \<Pi> ps main)))"
    by (auto simp: alpha_last_def)
  moreover have "alpha_last (cfg_collect_trace (compile_prog \<Pi> ps main) cinit_stores
                              (cfg_exit (compile_prog \<Pi> ps main)))
                 \<le> \<lbrakk>sign_exec \<Pi> ps main\<rbrakk>"
    using alpha_last_cfg_collect_trace_le sign_exec_sound_collecting[OF solves]
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
  shows "cfg_collect (prog_cfg p) cinit_stores (cfg_exit (prog_cfg p))
           \<le> \<lbrakk>sign_exec_prog p\<rbrakk>"
  using assms unfolding sign_terminates_prog_def prog_cfg_def sign_exec_prog_def
  by (rule sign_exec_sound_collecting)

corollary sign_exec_prog_sound_trace:
  assumes "sign_terminates_prog p"
      and "tr \<in> cfg_collect_trace (prog_cfg p) cinit_stores (cfg_exit (prog_cfg p))"
  shows "last tr \<in> \<lbrakk>sign_exec_prog p\<rbrakk>"
  using assms unfolding sign_terminates_prog_def prog_cfg_def sign_exec_prog_def
  by (rule sign_exec_sound_trace)

section \<open>Visualisation convenience\<close>

text \<open>
  One-command annotated CFG rendering for the sign domain.

  @{text "sign_annotated_dot_lit"} composes @{const sign_exec_raw} with
  @{const annotated_dot_of_prog_lit}: it compiles the program, runs the
  solver, collects assigned variables, and emits an annotated Graphviz
  DOT string as a native ML @{text "string"} (via @{const String.implode}).

  Typical example-file use -- no @{text "char list"} decoder needed:

  @{text [display] "ML_val \<open>
    writeln (@{code sign_annotated_dot_prog_lit} @{code my_prog})
  \<close>"}
\<close>

definition sign_annotated_dot_lit ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> String.literal" where
  "sign_annotated_dot_lit \<Pi> ps main =
     annotated_dot_of_prog_lit \<Pi> ps main (sign_exec_raw \<Pi> ps main)"

definition sign_annotated_dot_prog_lit :: "imp_prog \<Rightarrow> String.literal" where
  "sign_annotated_dot_prog_lit p =
     sign_annotated_dot_lit (prog_table p) (prog_procs p) (prog_main p)"

end
