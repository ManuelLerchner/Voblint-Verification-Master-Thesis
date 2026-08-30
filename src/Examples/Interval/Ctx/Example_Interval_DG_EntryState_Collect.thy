theory Example_Interval_DG_EntryState_Collect
  imports
    Example_Interval_DG_EntryState_Ctx
begin

section \<open>Activation-indexed collecting soundness: one context covers every __voblint_nondet_int() draw\<close>

text \<open>
  \<^const>\<open>rc_program\<close> is the concrete instance of the production entry-state
  soundness theorem \<open>entry_state_activation_collect_sound\<close>: the seven hypotheses
  that theorem carries -- source well-formedness, solver termination, exactness of
  the executable bottom predicate, and four coverage facts about the solved
  system (the compiled entry, intra-edge closure, the routed callee entry, and the
  call continuation) -- are all discharged here for \<open>rc_program\<close>, so the abstract
  statement becomes an unconditional fact about this program.

  What the instance witnesses is coverage rather than per-value precision. The one
  call's argument is drawn from \<open>__voblint_nondet_int()\<close>, so the call site is reached by
  infinitely many concrete stores that share a single caller-local abstract value
  \<open>Top\<close>. The production context function \<^const>\<open>entry_state_context\<close> ignores its
  concrete-store argument and recomputes the routed value from the caller's own
  solved abstract state, so every one of those draws enters under the very same
  admissible context \<^const>\<open>ctx_call\<close>.
\<close>

subsection \<open>The solved-system coverage facts\<close>

text \<open>The four coverage hypotheses are properties of the \<^emph>\<open>solved\<close> system -- which
  keys the executable solver actually covers, given its own seed and routing
  behavior -- so each is checked by evaluation against the terminated solve.\<close>

lemma rc_entry_covered:
  "(cfg_entry (compile_prog rc_pi rc_procs), [])
     \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
  unfolding rc_is_bot_pred_def by eval

lemma rc_fwd_closed_all:
  "\<forall>(u, c) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs).
     \<forall>(u', a, v) \<in> intra (compile_prog rc_pi rc_procs).
       u = u' \<longrightarrow> (v, c) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
  unfolding rc_is_bot_pred_def by eval

lemma rc_fwd_ok:
  assumes "(u, ctx) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
    and "(u, a, v) \<in> intra (compile_prog rc_pi rc_procs)"
  shows "(v, ctx) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
  using rc_fwd_closed_all assms by fastforce

text \<open>The one call site is reached only under the root context: \<open>main\<close> is the root
  activation, and nothing routes back into it.\<close>

lemma rc_call_caller_only_root:
  "\<forall>(p, ctx) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs).
     p = Statement 3 \<longrightarrow> ctx = []"
  unfolding rc_is_bot_pred_def by eval

lemma rc_covered_cont:
  "(Statement 4, []) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
  unfolding rc_is_bot_pred_def by eval

lemma rc_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog rc_pi rc_procs)"
  shows "(cont, c1) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
  using assms rc_calls_shape[unfolded rc_cfg_def] rc_call_caller_only_root rc_covered_cont
  by fastforce

text \<open>The routed callee entry the solved system selects is the executable
  \<^const>\<open>ctx_call\<close>: the route reads the caller's solved state from the solver's own
  table, which is exactly how \<^const>\<open>ctx_call\<close> is defined.\<close>

lemma rc_route_at_call:
  "entry_state_route_gen rc_gs rc_is_bot_pred (Statement 3) []
     (enter_local (ectx_spec rc_gs rc_is_bot_pred)
        (call_info_of (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')])
          (STR ''p''))
        (locals (snd (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs) (Inl (Statement 3, []))))
        (globs (snd (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs) (Inr Global))))
     (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')])
   = ctx_call"
  unfolding rc_is_bot_pred_def ctx_call_def rc_ctx_sol_def entry_state_route_gen_def
  by (simp add: enter_local_ectx_spec_eq_entry_state_entered)

lemma rc_call_fwd_ok:
  assumes cov: "(u, ctx) \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont)
               \<in> calls (compile_prog rc_pi rc_procs)"
  shows "(FunctionEntry p,
            entry_state_route_gen rc_gs rc_is_bot_pred u ctx
              (enter_local (ectx_spec rc_gs rc_is_bot_pred)
                 (call_info_of (CallEdge dst pars args) p)
                 (locals (snd (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs) (Inl (u, ctx))))
                 (globs (snd (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs) (Inr Global))))
              (CallEdge dst pars args))
         \<in> fst (entry_state_sol rc_gs rc_is_bot_pred rc_pi rc_procs)"
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

text \<open>The seven hypotheses \<open>entry_state_activation_collect_sound\<close> carries, discharged
  for \<^const>\<open>rc_program\<close>.  Every fact the production context states about this
  program -- the theorem itself, and the context-local definitions it is phrased in
  -- is conditional on exactly this bundle, so citing it once here makes each of
  them unconditional below.\<close>

lemmas rc_entry_state_hyps =
  rc_ctx_terminates rc_exact rc_entry_covered rc_fwd_ok rc_call_fwd_ok rc_comb_fwd_ok

theorem rc_activation_collect_sound:
  "activation_collect rc_gs
     (entry_state_context rc_gs rc_is_bot_pred rc_pi rc_procs)
     [] (compile_prog rc_pi rc_procs) (cinit_stores rc_gs) v ctx
   \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for rc_gs)
       (entry_state_sg_st rc_gs rc_is_bot_pred rc_pi rc_procs (Inl (v, ctx))))"
  by (rule entry_state_activation_collect_sound[OF rc_entry_state_hyps])

subsection \<open>Acceptance witness: one context covers every \<open>__voblint_nondet_int()\<close> draw\<close>

text \<open>\<^const>\<open>entry_state_context\<close> discards its concrete-store argument, so at the one
  call site it is the constant \<^const>\<open>ctx_call\<close> --- no matter which \<open>__voblint_nondet_int()\<close>
  outcome produced the store it is handed.\<close>

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
  "entry_state_context rc_gs rc_is_bot_pred rc_pi rc_procs
     (Statement 3) [] s = ctx_call"
  by (simp add: entry_state_context_def[OF rc_entry_state_hyps]
        rc_call_site_action rc_ctx_sol_def ctx_call_def Let_def
        enter_local_ectx_spec_eq_entry_state_entered entry_state_route_gen_def)

text \<open>The crux corollary: for \<^emph>\<open>every\<close> concrete store \<open>s\<close> that reaches the call site
  --- in particular every store obtained by any \<open>__voblint_nondet_int()\<close> outcome, since \<open>x\<close>'s
  solved interval there is \<open>Top\<close> --- the callee entry lands at the \<^emph>\<open>same, fixed\<close>
  context \<^const>\<open>ctx_call\<close>.  The conclusion's context component is that literal
  constant, not an expression mentioning \<open>s\<close>: this is one context covering
  infinitely many concrete entries, not a family of contexts indexed by which
  argument occurred.\<close>

corollary rc_entry_state_coverage:
  assumes sm: "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for rc_gs)
    (entry_state_sg_st rc_gs rc_is_bot_pred rc_pi rc_procs (Inl (Statement 3, []))))"
  shows "call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for rc_gs)
                (entry_state_sg_st rc_gs rc_is_bot_pred rc_pi rc_procs
                  (Inl (FunctionEntry (STR ''p''), ctx_call))))"
proof -
  have ce: "(Statement 3, CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')],
              FunctionEntry (STR ''p''), Statement 4)
              \<in> calls (compile_prog rc_pi rc_procs)"
    by eval
  show ?thesis
    using entry_state_sg_seed[OF rc_entry_state_hyps ce sm]
    by (simp add: rc_context_at_call)
qed

text \<open>Unfolding \<^const>\<open>activation_collect\<close> at \<^const>\<open>ctx_call\<close> makes the \<^const>\<open>key\<close>
  side of the same fact syntactically manifest: every concrete callee-entry trace this
  set counts --- one per \<open>__voblint_nondet_int()\<close> outcome that actually occurs --- is one whose
  \<^const>\<open>key\<close> equals the single context \<^const>\<open>ctx_call\<close>.
  \<open>rc_activation_collect_sound\<close> then bounds this whole set, every context alike.\<close>

corollary rc_activation_ctx_key:
  "activation_collect rc_gs
     (entry_state_context rc_gs rc_is_bot_pred rc_pi rc_procs)
     [] (compile_prog rc_pi rc_procs) (cinit_stores rc_gs)
     (FunctionEntry (STR ''p'')) ctx_call
   = {sink_store t | t.
        t \<in> valid_ltr rc_gs (compile_prog rc_pi rc_procs) (cinit_stores rc_gs)
        \<and> sink_node t = FunctionEntry (STR ''p'')
        \<and> key (entry_state_context rc_gs rc_is_bot_pred rc_pi rc_procs)
            [] t = ctx_call}"
  unfolding activation_collect_def by (rule refl)

end

