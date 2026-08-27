theory Example_Interval_DG_Ctx_Collect
  imports
    Example_Interval_DG_Ctx_Flagship
    "Voblint_Analysis.Interval_Point_Digest"
begin

section \<open>Activation-indexed collecting soundness for the routed interval solution\<close>

text \<open>
  \<^const>\<open>twice_program\<close> as a concrete instance of the production entry-state soundness
  theorem \<open>entry_state_activation_collect_sound\<close>: the seven hypotheses that theorem
  carries --- source well-formedness, solver termination, exactness of the executable
  bottom predicate, and four coverage facts about the solved system (the compiled
  entry, intra-edge closure, the routed callee entry, and the call continuation) ---
  are discharged here for \<open>twice\<close>, so the abstract statement becomes an unconditional
  fact about this program.

  What the instance witnesses is separation: the two call sites route to two distinct
  contexts \<^const>\<open>ctx_call1\<close> / \<^const>\<open>ctx_call2\<close>, and the collecting semantics is
  bounded at each of them independently.
\<close>

subsection \<open>The solved-system coverage facts\<close>

text \<open>The four coverage hypotheses are properties of the \<^emph>\<open>solved\<close> system --- which
  keys the executable solver actually covers, given its own seed and routing
  behavior --- so each is checked by evaluation against the terminated solve.\<close>

lemma twice_entry_covered: "(cfg_entry twice_cfg, []) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_is_bot_pred_def twice_cfg_def by eval

text \<open>\<^bold>\<open>Forward closure along intra edges.\<close>  Every \<^const>\<open>intra\<close> successor of a solved
  node stays solved \<^emph>\<open>at the same context\<close>.  This is not a generic solver invariant ---
  it holds because every \<open>twice\<close> node reaches the exit, so the exit query's backward
  cone materialises the whole intra-context chain.  It is a decidable closed check over
  the finite solved domain and the finite edge set (\<^bold>\<open>all\<close> solved contexts, not just the
  two observed by \<open>eval\<close>).\<close>
lemma twice_fwd_closed_all:
  "\<forall>(u, c) \<in> fst twice_ctx_sol. \<forall>(u', a, v) \<in> intra twice_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_is_bot_pred_def twice_cfg_def by eval

lemma twice_ctx_fwd_ok:
  assumes "(u, ctx) \<in> fst twice_ctx_sol" and "(u, a, v) \<in> intra twice_cfg"
  shows "(v, ctx) \<in> fst twice_ctx_sol"
  using twice_fwd_closed_all assms by fastforce

text \<open>Both call sites are reached only under the root context: \<open>main\<close> is the root
  activation, and nothing routes back into it.\<close>
lemma twice_call_callers_only_root:
  "\<forall>(p, ctx) \<in> fst twice_ctx_sol.
     (p = Statement 2 \<or> p = Statement 3) \<longrightarrow> ctx = []"
  unfolding twice_ctx_sol_def twice_is_bot_pred_def by eval

lemma twice_covered_cont3: "(Statement 3, []) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_is_bot_pred_def by eval

lemma twice_covered_cont4: "(Statement 4, []) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_is_bot_pred_def by eval

lemma twice_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst twice_ctx_sol"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg"
  shows "(cont, c1) \<in> fst twice_ctx_sol"
  using assms twice_calls_shape twice_call_callers_only_root twice_covered_cont3 twice_covered_cont4
  by fastforce

text \<open>The routed callee entry the abstract side selects is the executable context the
  flagship computes: the abstract route reads the caller's solved state through the same
  readback the transport uses, so \<open>entry_state_route_commute\<close> turns it back into the
  executable route \<^const>\<open>ctx_call1\<close> / \<^const>\<open>ctx_call2\<close> are defined by.\<close>

lemma twice_enter_local_eq_entered:
  "enter_local (ectx_abs_spec twice_gs) pars args
      (map_lift (fun_of_resolved_st_q_for twice_gs) d) g
   = map_lift (fun_of_resolved_st_q_for twice_gs)
       (transfer_lift twice_is_bot_pred (ivl_enter_st_for twice_gs pars args) d)"
  using entry_state_entered_commute[OF twice_exact, of d "CallEdge None pars args"]
  by (simp add: entry_state_entered_def entered_state_abs_def ectx_abs_spec_def
                dgs_enter_base_for_lifted)

lemma twice_route_abs_at_call1:
  "entry_state_route_abs_gen twice_gs (Statement 2) []
     (enter_local (ectx_abs_spec twice_gs) [(STR ''p'')]
        (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3])
        (locals (entry_state_sigma_abs_exec twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
           (Inl (Statement 2, []))))
        (globs (entry_state_sigma_abs_exec twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
           (Inr Global))))
     (CallEdge (compile_dst (prog_tyenv twice_program) (Some (STR ''x''))) [(STR ''p'')]
         (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3]))
   = ctx_call1"
  unfolding entry_state_route_abs_gen_def entry_state_sigma_abs_exec_def ctx_call1_def
    twice_ctx_sol_def o_apply fun_of_dg_st_gen_simps
  by (simp add: twice_enter_local_eq_entered entry_state_entered_def
                entry_state_route_commute[OF twice_exact])

lemma twice_route_abs_at_call2:
  "entry_state_route_abs_gen twice_gs (Statement 3) []
     (enter_local (ectx_abs_spec twice_gs) [(STR ''p'')]
        (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10])
        (locals (entry_state_sigma_abs_exec twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
           (Inl (Statement 3, []))))
        (globs (entry_state_sigma_abs_exec twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
           (Inr Global))))
     (CallEdge (compile_dst (prog_tyenv twice_program) (Some (STR ''y''))) [(STR ''p'')]
         (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10]))
   = ctx_call2"
  unfolding entry_state_route_abs_gen_def entry_state_sigma_abs_exec_def ctx_call2_def
    twice_ctx_sol_def o_apply fun_of_dg_st_gen_simps
  by (simp add: twice_enter_local_eq_entered entry_state_entered_def
                entry_state_route_commute[OF twice_exact])

lemma twice_call_fwd_ok:
  assumes cov: "(u, ctx) \<in> fst twice_ctx_sol"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg"
  shows "(FunctionEntry p,
            entry_state_route_abs_gen twice_gs u ctx
              (enter_local (ectx_abs_spec twice_gs) pars args
                 (locals (entry_state_sigma_abs_exec twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
                    (Inl (u, ctx))))
                 (globs (entry_state_sigma_abs_exec twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
                    (Inr Global))))
              (CallEdge dst pars args))
         \<in> fst twice_ctx_sol"
proof -
  from ce twice_calls_shape consider
      (c1) "u = Statement 2" "dst = compile_dst (prog_tyenv twice_program) (Some (STR ''x''))" "pars = [(STR ''p'')]"
           "args = compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3]"
           "p = (STR ''twice'')"
    | (c2) "u = Statement 3" "dst = compile_dst (prog_tyenv twice_program) (Some (STR ''y''))" "pars = [(STR ''p'')]"
           "args = compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10]"
           "p = (STR ''twice'')"
    by fastforce
  thus ?thesis
  proof cases
    case c1
    have root: "ctx = []" using cov c1 twice_call_callers_only_root by fastforce
    show ?thesis
      unfolding c1 root twice_route_abs_at_call1 by (rule callee_covered_call1)
  next
    case c2
    have root: "ctx = []" using cov c2 twice_call_callers_only_root by fastforce
    show ?thesis
      unfolding c2 root twice_route_abs_at_call2 by (rule callee_covered_call2)
  qed
qed

subsection \<open>The production soundness theorem, instantiated\<close>

text \<open>The seven hypotheses \<open>entry_state_activation_collect_sound\<close> carries, discharged for
  \<^const>\<open>twice_program\<close>.  Every fact the production context states about this program ---
  the theorem itself, and the context-local definitions it is phrased in --- is
  conditional on exactly this bundle, so citing it once here makes each of them
  unconditional below.\<close>

lemmas twice_entry_state_hyps =
  twice_wf twice_ctx_terminates twice_exact
  twice_entry_covered[unfolded twice_ctx_sol_def twice_cfg_def]
  twice_ctx_fwd_ok[unfolded twice_ctx_sol_def twice_cfg_def]
  twice_call_fwd_ok[unfolded twice_ctx_sol_def twice_cfg_def]
  twice_comb_fwd_ok[unfolded twice_ctx_sol_def twice_cfg_def]

theorem twice_activation_collect_sound:
  "activation_collect (prog_tyenv twice_program) twice_gs
     (admiss_exact (entry_state_context twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main))
     [] (compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main) (cinit_stores twice_gs) v ctx
   \<subseteq> gamma_state_lift
       (entry_state_sg twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main (Inl (v, ctx)))"
  by (rule entry_state_activation_collect_sound[OF twice_entry_state_hyps])

subsection \<open>The context each call site selects\<close>

text \<open>\<^const>\<open>entry_state_context\<close> discards its concrete-store argument and recomputes the
  routed value from the caller's own solved abstract state, so at each call site it is
  the constant the flagship computed.\<close>

lemma twice_call_site_action1:
  "call_action_at_call_site (compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main) (Statement 2)
     = CallEdge (compile_dst (prog_tyenv twice_program) (Some (STR ''x''))) [(STR ''p'')]
         (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3])"
proof (rule call_action_at_call_site_eq
    [OF twice_finC[unfolded twice_cfg_def] compile_prog_calls_source_unique])
  show "(Statement 2, CallEdge (compile_dst (prog_tyenv twice_program) (Some (STR ''x''))) [(STR ''p'')]
         (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3]),
          FunctionEntry (STR ''twice''), Statement 3)
          \<in> calls (compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main)"
    by eval
qed

lemma twice_call_site_action2:
  "call_action_at_call_site (compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main) (Statement 3)
     = CallEdge (compile_dst (prog_tyenv twice_program) (Some (STR ''y''))) [(STR ''p'')]
         (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10])"
proof (rule call_action_at_call_site_eq
    [OF twice_finC[unfolded twice_cfg_def] compile_prog_calls_source_unique])
  show "(Statement 3, CallEdge (compile_dst (prog_tyenv twice_program) (Some (STR ''y''))) [(STR ''p'')]
         (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10]),
          FunctionEntry (STR ''twice''), Statement 4)
          \<in> calls (compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main)"
    by eval
qed

lemma twice_context_at_call1:
  "entry_state_context twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
     (Statement 2) [] s = ctx_call1"
  by (simp add: entry_state_context_def[OF twice_entry_state_hyps]
                entry_state_sigma_abs_def[OF twice_entry_state_hyps]
                twice_call_site_action1 twice_route_abs_at_call1[simplified])

lemma twice_context_at_call2:
  "entry_state_context twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
     (Statement 3) [] s = ctx_call2"
  by (simp add: entry_state_context_def[OF twice_entry_state_hyps]
                entry_state_sigma_abs_def[OF twice_entry_state_hyps]
                twice_call_site_action2 twice_route_abs_at_call2[simplified])

subsection \<open>The concrete store-decoding context, and its agreement with the analysis\<close>

definition ivl_context :: "cfg_node \<Rightarrow> ivl list \<Rightarrow> store \<Rightarrow> ivl list" where
  "ivl_context = formals_context_sem twice_cfg ivl_decode"

text \<open>\<^const>\<open>ivl_context\<close> is the \<^emph>\<open>semantic\<close> reading of the same partial-tabulation policy
  (\<^cite>\<open>SeidlEtAl2026\<close> Example 8): it decodes the concrete entered store's formals
  through \<^const>\<open>ivl_decode\<close>, looking its formals up from the call site via
  \<^const>\<open>formals_at_call_site\<close>.  \<^const>\<open>entry_state_context\<close> instead ignores the store and
  recomputes the routed value from the caller's solved abstract state.  The two are
  distinct functions; for \<open>twice\<close>'s two constant-argument calls they agree, which is
  exactly why this program's abstract contexts are the exact point abstractions of the
  values actually entered.\<close>

text \<open>The formals of each call site, computed directly from \<^const>\<open>twice_cfg\<close> via
  \<^const>\<open>formals_at_call_site\<close> rather than assumed.\<close>
lemma twice_formals_at_call_site2: "formals_at_call_site twice_cfg (Statement 2) = [(STR ''p'')]"
  unfolding formals_at_call_site_def by eval

lemma twice_formals_at_call_site3: "formals_at_call_site twice_cfg (Statement 3) = [(STR ''p'')]"
  unfolding formals_at_call_site_def by eval

text \<open>The two call sites' elaborated actuals: each constant argument is bound at the
  formal's declared kind, so the compiled edge carries a typed literal rather than the
  source \<^term>\<open>VIMP_Syntax.N\<close> node.\<close>

lemma twice_actuals_call1:
  "compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3] = [TN I32 3]"
  by eval

lemma twice_actuals_call2:
  "compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10] = [TN I32 10]"
  by eval

lemma enter_route_exact_call1:
  assumes "u = Statement 2"
    and "s' = call_enter twice_gs (CallEdge dst [(STR ''p'')] (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3])) s"
  shows "ivl_context u ctx s' = ctx_call1"
proof -
  from assms(2) have "s' = (enter_state twice_gs s)((STR ''p'') := 3)"
    by (simp add: call_enter_CallEdge bind_formals_def twice_actuals_call1 ik_bounds_pins)
  thus ?thesis
    unfolding assms(1) ivl_context_def formals_context_sem_def
    by (simp add: twice_formals_at_call_site2 formals_context_def ivl_decode_def ctx_call1_val)
qed

lemma enter_route_exact_call2:
  assumes "u = Statement 3"
    and "s' = call_enter twice_gs (CallEdge dst [(STR ''p'')] (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10])) s"
  shows "ivl_context u ctx s' = ctx_call2"
proof -
  from assms(2) have "s' = (enter_state twice_gs s)((STR ''p'') := 10)"
    by (simp add: call_enter_CallEdge bind_formals_def twice_actuals_call2 ik_bounds_pins)
  thus ?thesis
    unfolding assms(1) ivl_context_def formals_context_sem_def
    by (simp add: twice_formals_at_call_site3 formals_context_def ivl_decode_def ctx_call2_val)
qed

theorem ivl_context_eq_entry_state_context_call1:
  assumes "s' = call_enter twice_gs (CallEdge dst [(STR ''p'')] (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3])) s"
  shows "ivl_context (Statement 2) [] s'
           = entry_state_context twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
               (Statement 2) [] s'"
  using enter_route_exact_call1[OF refl assms] by (simp add: twice_context_at_call1)

theorem ivl_context_eq_entry_state_context_call2:
  assumes "s' = call_enter twice_gs (CallEdge dst [(STR ''p'')] (compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10])) s"
  shows "ivl_context (Statement 3) [] s'
           = entry_state_context twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main
               (Statement 3) [] s'"
  using enter_route_exact_call2[OF refl assms] by (simp add: twice_context_at_call2)

subsection \<open>Shared-state regression facts\<close>

text \<open>The local unknown carries the whole abstract state, so a variable that is shared
  across activations is read at the very same slot as a formal.  A name that
  \<^const>\<open>twice_program\<close> never declares --- \<open>Gx\<close> --- therefore reads identically in both
  callee contexts: no name-based \<open>is_global\<close> convention gives it a separate,
  context-indexed slot.\<close>
lemma global_slot_shared:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call1)))) (STR ''Gx'')
     = twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call2)))) (STR ''Gx'')"
  unfolding twice_ctx_sol_def twice_is_bot_pred_def ctx_call1_def ctx_call2_def by eval

text \<open>The solver-global carrier stays inert: every field of the Base-style specification
  threads its incoming \<open>g\<close> through unchanged, so the shared \<^const>\<open>Global\<close> unknown is
  never used to reconstruct program state.\<close>
lemma twice_ctx_global_slot_inert:
  "globs (snd twice_ctx_sol (Inr Global)) = Bot"
  unfolding twice_ctx_sol_def twice_is_bot_pred_def by eval

end

