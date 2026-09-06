theory Parity_Exec_Sound
  imports
    Parity_Sound
    Parity_Exec
    "Voblint_Exec.Result_Normalization"
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.Routed_Context_Unit"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

section \<open>Native D/G runtime API: an arbitrary VIMP program\<close>

text \<open>
  What a caller runs when it has an \<^typ>\<open>imp_prog\<close> and wants an answer: the equation
  system that program generates at the context-insensitive route, the solver call that
  computes a solution for it, the termination side condition that call carries, and the
  result table the solution reads back into.

  Nothing here is a theorem about Parity.  The specification and its soundness are
  \<^theory>\<open>Voblint_Analysis_Parity.Parity_Sound\<close>'s, and the collecting-soundness half that
  turns a computed solution into a statement about source runs stays downstream, in the
  \<open>ownership_split_dg_exec_analysis\<close> locale a CLI entry point interprets.  This theory only
  \<^emph>\<open>computes\<close>, which is why it can sit below every context policy: the call-string and
  entry-state routes in \<open>Parity_Analyses\<close> build their own
  equation systems the same way, from the same \<^const>\<open>pctx_spec\<close>.

  Parity's lattice is finite, like Sign's, so \<open>pctx_sol\<close> names the always-join
  update rule and no widening is needed.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition pctx_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs gs empty_pred Pi ps =
     routed_node_rhs_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
       (routed_call_tree (pctx_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
       (routed_entry_seed_tree Activation_Seed)
       (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot"

definition pctx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (pctx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition pctx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "pctx_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
       (pctx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma pctx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (pctx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "pctx_terminates gs empty_pred Pi ps"
  unfolding pctx_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

lemma pctx_vars_finite:
  assumes "pctx_terminates gs empty_pred Pi ps"
  shows "finite (fst (pctx_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.finite_stabl_solve[
      OF assms[unfolded pctx_terminates_def]]
  unfolding pctx_sol_def TD_side_always_join_Interp_solve_def
  by simp

section \<open>Solved-result table\<close>

text \<open>
  The whole-program convenience layer, reading the raw executable solve through the same
  \<^const>\<open>canonicalize_lift\<close>/\<^const>\<open>normalize_point\<close> boundary every other domain's result
  table already uses. Nothing here is Parity-specific beyond the domain name: these are
  the thin monomorphic aliases the public API needs, not a second result construction.
\<close>

definition pctx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs_prog gs p =
     pctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog gs p =
     TD_side_always_join_Interp_solve (pctx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition pctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (pctx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition pctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "pctx_terminates_prog gs p =
     pctx_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma pctx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (pctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "pctx_terminates_prog gs p"
  unfolding pctx_terminates_prog_def
  using assms by (rule pctx_terminates_via_solve_c)

definition analyse_parity_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_for gs p =
     Analysis_Result
       (fst (pctx_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pctx_sol_prog gs p) (Inl (v, ctx))))))"

text \<open>\<^const>\<open>ctx_solved_for\<close> at this domain's solve, with \<^const>\<open>Analysis_Global\<close> and
  \<^const>\<open>Activation_Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_entry_seed_tree\<close>
  already takes them.\<close>

definition analyse_parity_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, parity abs_state) analysis_result
          \<times> (String.literal \<times> parity abs_state lifted) list" where
  "analyse_parity_ctx_solved_for = ctx_solved_for pctx_sol_prog (unit_seed_global_keys (Analysis_Global ()) Activation_Seed)"

lemma fst_analyse_parity_ctx_solved_for:
  "fst (analyse_parity_ctx_solved_for gs p) = analyse_parity_ctx_result_for gs p"
  by (simp add: analyse_parity_ctx_solved_for_def fst_ctx_solved_for
      analyse_parity_ctx_result_for_def Let_def)

declare analyse_parity_ctx_result_for_def [code del]

lemma analyse_parity_ctx_result_for_code [code]:
  "analyse_parity_ctx_result_for gs p =
     (let sol = pctx_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_ctx_result_for_def Let_def by (rule refl)

definition analyse_parity_ctx_result :: "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result p =
     analyse_parity_ctx_result_for (declared_global p) p"

text \<open>Per-origin sibling, reading \<^const>\<open>pctx_sol_prog_per_origin\<close>.\<close>

definition analyse_parity_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_per_origin_for gs p =
     Analysis_Result
       (fst (pctx_sol_prog_per_origin gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pctx_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_parity_ctx_result_per_origin_for_def [code del]

lemma analyse_parity_ctx_result_per_origin_for_code [code]:
  "analyse_parity_ctx_result_per_origin_for gs p =
     (let sol = pctx_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_parity_ctx_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_per_origin p =
     analyse_parity_ctx_result_per_origin_for (declared_global p) p"

end
