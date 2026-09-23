theory Example_Interval_DG_EntryState_Collect
  imports
    Example_Interval_DG_EntryState_Ctx
begin

section \<open>Activation-indexed collecting soundness: one context covers every __voblint_nondet_int() draw\<close>

text \<open>
  \<^const>\<open>rc_program\<close> is the concrete instance of the production entry-state
  soundness theorem \<open>entry_state_activation_collect_sound\<close> of Interval's entry-state
  registration \<open>interval_es_rule\<close> at \<^const>\<open>Globals_Warrow\<close>: the hypotheses
  that theorem carries -- solver termination and four coverage facts about the solved
  system (the compiled entry, intra-edge closure, the routed callee entry, and the
  call continuation) -- are all discharged here for \<open>rc_program\<close>, so the abstract
  statement becomes an unconditional fact about this program.

  What the instance witnesses is coverage rather than per-value precision. The one
  call's argument is drawn from \<open>__voblint_nondet_int()\<close>, so the call site is reached by
  infinitely many concrete stores that share a single caller-local abstract value
  \<open>Top\<close>. The production context relation \<^const>\<open>routed_dg_analysis.admitted_contexts\<close>
  admits its concrete-store argument and recomputes the routed value from the caller's
  own solved abstract state, so every one of those draws enters under the very same
  admissible context \<^const>\<open>ctx_call\<close>.
\<close>

subsection \<open>The solved-system coverage facts\<close>

text \<open>The four coverage hypotheses are properties of the \<^emph>\<open>solved\<close> system -- which
  keys the executable solver actually covers, given its own seed and routing
  behavior -- so each is checked by evaluation against the terminated solve.\<close>

lemma rc_entry_covered:
  "(cfg_entry (compile_prog rc_pi rc_procs), [])
     \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
  by eval

lemma rc_fwd_closed_all:
  "\<forall>(u, c) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program).
     \<forall>(u', a, v) \<in> intra (compile_prog rc_pi rc_procs).
       u = u' \<longrightarrow> (v, c) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
  by eval

lemma rc_fwd_ok:
  assumes "(u, ctx) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
    and "(u, a, v) \<in> intra (compile_prog rc_pi rc_procs)"
  shows "(v, ctx) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
  using rc_fwd_closed_all assms by fastforce

text \<open>The one call site is reached only under the root context: \<open>main\<close> is the root
  activation, and nothing routes back into it.\<close>

lemma rc_call_caller_only_root:
  "\<forall>(p, ctx) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program).
     p = Statement 3 \<longrightarrow> ctx = []"
  by eval

lemma rc_covered_cont:
  "(Statement 4, []) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
  by eval

lemma rc_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog rc_pi rc_procs)"
  shows "(cont, c1) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
  using assms rc_calls_shape[unfolded rc_cfg_def] rc_call_caller_only_root rc_covered_cont
  by fastforce

text \<open>The routed callee entry the solved system selects is the executable
  \<^const>\<open>ctx_call\<close>: the route reads the caller's solved state from the solver's own
  table, which is exactly how \<^const>\<open>ctx_call\<close> is defined.\<close>

lemma rc_route_at_call:
  "exec_formals_route rc_gs (Statement 3) []
     (transfer_lift rc_empty_pred
        (ivl_enter_st_for rc_gs
           (call_info_of (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')])
             (STR ''p'')))
        (locals (snd (interval_es_rule.solution Globals_Warrow rc_gs rc_program)
                   (Inl (Statement 3, [])))))
     (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')])
   = ctx_call"
  unfolding rc_empty_pred_def ctx_call_def interval_es_rule.ctx_succ_def
    interval_es_rule.sol_env_def
  by (rule refl)

lemma rc_call_fwd_ok:
  assumes cov: "(u, ctx) \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont)
               \<in> calls (compile_prog rc_pi rc_procs)"
  shows "(FunctionEntry p,
            exec_formals_route rc_gs u ctx
              (transfer_lift rc_empty_pred
                 (ivl_enter_st_for rc_gs (call_info_of (CallEdge dst pars args) p))
                 (locals (snd (interval_es_rule.solution Globals_Warrow rc_gs rc_program)
                            (Inl (u, ctx)))))
              (CallEdge dst pars args))
         \<in> fst (interval_es_rule.solution Globals_Warrow rc_gs rc_program)"
proof -
  from ce rc_calls_shape[unfolded rc_cfg_def] have shape:
    "u = Statement 3" "dst = Some (STR ''y'')" "pars = [(STR ''a'')]" "args = [V (STR ''x'')]"
    "p = (STR ''p'')"
    by fastforce+
  have root: "ctx = []" using cov shape rc_call_caller_only_root by fastforce
  show ?thesis
    unfolding shape root rc_route_at_call
    using callee_covered_call unfolding rc_ctx_sol_def .
qed

subsection \<open>The production soundness theorem, instantiated\<close>

text \<open>The hypotheses \<open>entry_state_activation_collect_sound\<close> carries, discharged
  for \<^const>\<open>rc_program\<close>.  Every fact the production context states about this
  program -- the theorem itself, and the context-local definitions it is phrased in
  -- is conditional on exactly this bundle, so citing it once here makes each of
  them unconditional below.\<close>

lemma rc_cfg_alt: "prog_cfg rc_program = compile_prog rc_pi rc_procs"
  by (simp add: prog_cfg_def rc_pi_def rc_procs_def)

lemmas rc_routed_hyps =
  rc_ctx_terminates
  rc_fwd_ok[folded interval_es_rule.sol_vars_def rc_cfg_alt]
  rc_call_fwd_ok[unfolded rc_empty_pred_def,
    folded interval_es_rule.sol_vars_def interval_es_rule.sol_env_def rc_cfg_alt]
  rc_comb_fwd_ok[folded interval_es_rule.sol_vars_def rc_cfg_alt]

lemmas rc_entry_state_hyps =
  rc_routed_hyps rc_entry_covered[folded interval_es_rule.sol_vars_def rc_cfg_alt]

theorem rc_activation_collect_sound:
  "activation_collect rc_gs
     (interval_es_rule.admitted_contexts Globals_Warrow rc_gs rc_program)
     [] (compile_prog rc_pi rc_procs) (cinit_stores rc_gs) v ctx
   \<subseteq> \<lbrakk>map_lift (fun_of_resolved_st_q_for rc_gs)
       (interval_es_rule.reader Globals_Warrow rc_gs rc_program (Inl (v, ctx)))\<rbrakk>\<^sub>\<bottom>"
  unfolding rc_cfg_alt[symmetric]
  by (rule interval_es_rule.entry_state_activation_collect_sound[OF rc_entry_state_hyps])

subsection \<open>Acceptance witness: one context covers every \<open>__voblint_nondet_int()\<close> draw\<close>

text \<open>\<^const>\<open>routed_dg_analysis.admitted_contexts\<close> admits a routed context relationally
  rather than computing one from the concrete store, so at the one call site it admits
  exactly the constant \<^const>\<open>ctx_call\<close> --- no matter which
  \<open>__voblint_nondet_int()\<close> outcome produced the store it is handed.\<close>

lemma rc_call_site_action:
  "call_action_at_call_site (compile_prog rc_pi rc_procs) (Statement 3)
     = CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]"
proof (rule call_action_at_call_site_eq
    [OF rc_finC[unfolded rc_cfg_def] compile_prog_calls_source_unique])
  show "(Statement 3, CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')],
          FunctionEntry (STR ''p''), Statement 4)
          \<in> calls (compile_prog rc_pi rc_procs)"
    by eval
qed

lemma rc_context_at_call:
  assumes sin: "s \<in> interval_gamma rc_gs
                  (locals (snd (interval_es_rule.solution Globals_Warrow rc_gs rc_program)
                     (Inl (Statement 3, []))))
                  (globs (snd (interval_es_rule.solution Globals_Warrow rc_gs rc_program)
                     (Inr (Analysis_Global ()))))"
  shows "interval_es_rule.admitted_contexts Globals_Warrow rc_gs rc_program
           (Statement 3) []
           (call_info_of (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) (STR ''p''))
           s (call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s)
           ctx_call"
proof -
  let ?ci = "call_info_of (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) (STR ''p'')"
  let ?d = "locals (snd (interval_es_rule.solution Globals_Warrow rc_gs rc_program)
              (Inl (Statement 3, [])))"
  let ?entry = "transfer_lift rc_empty_pred (ivl_enter_st_for rc_gs ?ci) ?d"
  let ?g = "globs (snd (interval_es_rule.solution Globals_Warrow rc_gs rc_program)
              (Inr (Analysis_Global ())))"
  have cov: "entry_pairs_cover (\<lambda>d'. interval_gamma rc_gs d' ?g)
      s (call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s)
      [(?d, ?entry)]"
    using interval_entry_cover_exec[OF rc_exact sin, where ci = ?ci] by simp
  have ecov: "call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s
                \<in> interval_gamma rc_gs ?entry ?g"
    using cov unfolding entry_pairs_cover_def by simp
  have base: "interval_es_rule.admitted_contexts Globals_Warrow rc_gs rc_program
      (Statement 3) [] ?ci s
      (call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s)
      (exec_formals_route rc_gs (Statement 3) [] ?entry
         (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]))"
    unfolding rc_empty_pred_def interval_es_rule.sol_env_def[symmetric]
    by (rule interval_es_rule.admitted_contextsI_call)
       (use sin ecov in
          \<open>simp_all add: interval_gamma_def rc_empty_pred_def interval_es_rule.sol_env_def\<close>)
  thus ?thesis
    by (simp add: rc_route_at_call)
qed

text \<open>The crux corollary: for \<^emph>\<open>every\<close> concrete store \<open>s\<close> that reaches the call site
  --- in particular every store obtained by any \<open>__voblint_nondet_int()\<close> outcome, since
  \<open>x\<close>'s solved interval there is \<open>Top\<close> --- the callee entry lands at the
  \<^emph>\<open>same, fixed\<close> context \<^const>\<open>ctx_call\<close>.  The conclusion's context component is
  that literal constant, not an expression mentioning \<open>s\<close>: this is one context covering
  infinitely many concrete entries, not a family of contexts indexed by which
  argument occurred.\<close>

corollary rc_entry_state_coverage:
  assumes sm: "s \<in> \<lbrakk>map_lift (fun_of_resolved_st_q_for rc_gs)
    (interval_es_rule.reader Globals_Warrow rc_gs rc_program (Inl (Statement 3, [])))\<rbrakk>\<^sub>\<bottom>"
  shows "call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s
           \<in> \<lbrakk>map_lift (fun_of_resolved_st_q_for rc_gs)
                (interval_es_rule.reader Globals_Warrow rc_gs rc_program
                  (Inl (FunctionEntry (STR ''p''), ctx_call)))\<rbrakk>\<^sub>\<bottom>"
proof -
  have ce: "(Statement 3, CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')],
              FunctionEntry (STR ''p''), Statement 4)
              \<in> calls (compile_prog rc_pi rc_procs)"
    by eval
  have covd: "(Statement 3, []) \<in> fst rc_ctx_sol"
    unfolding rc_ctx_sol_def by eval
  have sin: "s \<in> interval_gamma rc_gs (locals (snd rc_ctx_sol (Inl (Statement 3, []))))
               (globs (snd rc_ctx_sol (Inr (Analysis_Global ()))))"
    using sm covd
    unfolding interval_gamma_def interval_es_rule.reader_def
      interval_es_rule.sol_vars_def interval_es_rule.sol_env_def rc_ctx_sol_def[symmetric]
    by simp
  show ?thesis
    using interval_es_rule.entry_state_routed_context_call[OF rc_routed_hyps
          ce[folded rc_cfg_alt] sm[unfolded interval_es_rule.reader_def]
          rc_context_at_call[OF sin[unfolded rc_ctx_sol_def]]]
    by (simp add: interval_es_rule.reader_def)
qed

text \<open>Unfolding \<^const>\<open>activation_collect\<close> at \<^const>\<open>ctx_call\<close> makes the
  \<^const>\<open>trace_context\<close> side of the same fact syntactically manifest: every concrete
  callee-entry trace this set counts --- one per \<open>__voblint_nondet_int()\<close> outcome that
  actually occurs --- is one whose \<^const>\<open>trace_context\<close> admits the single context
  \<^const>\<open>ctx_call\<close>. The admitted-context relation is a relation rather than a
  function, so this is membership, not an equation.
  \<open>rc_activation_collect_sound\<close> then bounds this whole set, every context alike.\<close>

corollary rc_activation_ctx_key:
  "activation_collect rc_gs
     (interval_es_rule.admitted_contexts Globals_Warrow rc_gs rc_program)
     [] (compile_prog rc_pi rc_procs) (cinit_stores rc_gs)
     (FunctionEntry (STR ''p'')) ctx_call
   = {sink_store t | t.
        t \<in> \<T>\<^bsub>rc_gs,compile_prog rc_pi rc_procs,cinit_stores rc_gs\<^esub>
        \<and> sink_node t = FunctionEntry (STR ''p'')
        \<and> trace_context rc_gs (interval_es_rule.admitted_contexts Globals_Warrow rc_gs rc_program)
            [] (compile_prog rc_pi rc_procs) t ctx_call}"
  unfolding activation_collect_def by (rule refl)

end
