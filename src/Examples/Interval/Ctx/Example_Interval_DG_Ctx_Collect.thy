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
  unfolding twice_ctx_sol_def twice_empty_pred_def twice_cfg_def by eval

text \<open>\<^bold>\<open>Forward closure along intra edges.\<close>  Every \<^const>\<open>intra\<close> successor of a solved
  node stays solved \<^emph>\<open>at the same context\<close>.  This is not a generic solver invariant ---
  it holds because every \<open>twice\<close> node reaches the exit, so the exit query's backward
  cone materialises the whole intra-context chain.  It is a decidable closed check over
  the finite solved domain and the finite edge set (\<^bold>\<open>all\<close> solved contexts, not just the
  two observed by \<open>eval\<close>).\<close>
lemma twice_fwd_closed_all:
  "\<forall>(u, c) \<in> fst twice_ctx_sol. \<forall>(u', a, v) \<in> intra twice_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_empty_pred_def twice_cfg_def by eval

lemma twice_ctx_fwd_ok:
  assumes "(u, ctx) \<in> fst twice_ctx_sol" and "(u, a, v) \<in> intra twice_cfg"
  shows "(v, ctx) \<in> fst twice_ctx_sol"
  using twice_fwd_closed_all assms by fastforce

text \<open>Both call sites are reached only under the root context: \<open>main\<close> is the root
  activation, and nothing routes back into it.\<close>
lemma twice_call_callers_only_root:
  "\<forall>(p, ctx) \<in> fst twice_ctx_sol.
     (p = Statement 2 \<or> p = Statement 3) \<longrightarrow> ctx = []"
  unfolding twice_ctx_sol_def twice_empty_pred_def by eval

lemma twice_covered_cont3: "(Statement 3, []) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_empty_pred_def by eval

lemma twice_covered_cont4: "(Statement 4, []) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_empty_pred_def by eval

lemma twice_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst twice_ctx_sol"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg"
  shows "(cont, c1) \<in> fst twice_ctx_sol"
  using assms twice_calls_shape twice_call_callers_only_root twice_covered_cont3 twice_covered_cont4
  by fastforce

text \<open>The routed callee entry the solved system selects is the executable context the
  flagship computes: the route reads the caller's solved state from the solver's own
  table, which is exactly how \<^const>\<open>ctx_call1\<close> / \<^const>\<open>ctx_call2\<close> are defined.\<close>

lemma twice_route_at_call1:
  "entry_state_route_gen twice_gs twice_empty_pred (Statement 2) []
     (transfer_lift twice_empty_pred
        (ivl_enter_st_for twice_gs
           (call_info_of (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3])
             (STR ''twice'')))
        (locals (snd twice_ctx_sol (Inl (Statement 2, [])))))
     (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3])
   = ctx_call1"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call1_def entry_state_route_gen_def
  by (simp add: enter_st_interval_eq_entry_state_entered)

lemma twice_route_at_call2:
  "entry_state_route_gen twice_gs twice_empty_pred (Statement 3) []
     (transfer_lift twice_empty_pred
        (ivl_enter_st_for twice_gs
           (call_info_of (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10])
             (STR ''twice'')))
        (locals (snd twice_ctx_sol (Inl (Statement 3, [])))))
     (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10])
   = ctx_call2"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call2_def entry_state_route_gen_def
  by (simp add: enter_st_interval_eq_entry_state_entered)

lemma twice_call_fwd_ok:
  assumes cov: "(u, ctx) \<in> fst twice_ctx_sol"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg"
  shows "(FunctionEntry p,
            entry_state_route_gen twice_gs twice_empty_pred u ctx
              (transfer_lift twice_empty_pred
                 (ivl_enter_st_for twice_gs (call_info_of (CallEdge dst pars args) p))
                 (locals (snd twice_ctx_sol (Inl (u, ctx)))))
              (CallEdge dst pars args))
         \<in> fst twice_ctx_sol"
proof -
  from ce twice_calls_shape consider
      (c1) "u = Statement 2" "dst = Some (STR ''x'')" "pars = [(STR ''p'')]"
           "args = [VIMP_Syntax.N 3]" "p = (STR ''twice'')"
    | (c2) "u = Statement 3" "dst = Some (STR ''y'')" "pars = [(STR ''p'')]"
           "args = [VIMP_Syntax.N 10]" "p = (STR ''twice'')"
    by fastforce
  thus ?thesis
  proof cases
    case c1
    have root: "ctx = []" using cov c1 twice_call_callers_only_root by fastforce
    show ?thesis
      unfolding c1 root twice_route_at_call1 by (rule callee_covered_call1)
  next
    case c2
    have root: "ctx = []" using cov c2 twice_call_callers_only_root by fastforce
    show ?thesis
      unfolding c2 root twice_route_at_call2 by (rule callee_covered_call2)
  qed
qed

subsection \<open>The production soundness theorem, instantiated\<close>

text \<open>The six hypotheses \<open>entry_state_activation_collect_sound\<close> carries, discharged for
  \<^const>\<open>twice_program\<close>.  Every fact the production context states about this program ---
  the theorem itself, and the context-local definitions it is phrased in --- is
  conditional on exactly this bundle, so citing it once here makes each of them
  unconditional below.\<close>

lemmas twice_entry_state_hyps =
  twice_ctx_terminates twice_exact
  twice_entry_covered[unfolded twice_ctx_sol_def twice_cfg_def]
  twice_ctx_fwd_ok[unfolded twice_ctx_sol_def twice_cfg_def]
  twice_call_fwd_ok[unfolded twice_ctx_sol_def twice_cfg_def]
  twice_comb_fwd_ok[unfolded twice_ctx_sol_def twice_cfg_def]

theorem twice_activation_collect_sound:
  "activation_collect twice_gs
     (entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs)
     [] (compile_prog twice_pi twice_procs) (cinit_stores twice_gs) v ctx
   \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for twice_gs)
       (entry_state_sg_st twice_gs twice_empty_pred twice_pi twice_procs (Inl (v, ctx))))"
  by (rule entry_state_activation_collect_sound[OF twice_entry_state_hyps])

subsection \<open>The context each call site selects\<close>

text \<open>\<^const>\<open>entry_state_context_rel\<close> admits a routed context relationally rather than
  computing one from the concrete store, so at each call site it admits exactly the
  constant the flagship computed.\<close>


lemma twice_call_site_action1:
  "call_action_at_call_site (compile_prog twice_pi twice_procs) (Statement 2)
     = CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]"
proof (rule call_action_at_call_site_eq
    [OF twice_finC[unfolded twice_cfg_def] compile_prog_calls_source_unique])
  show "(Statement 2, CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3],
          FunctionEntry (STR ''twice''), Statement 3)
          \<in> calls (compile_prog twice_pi twice_procs)"
    by eval
qed

lemma twice_call_site_action2:
  "call_action_at_call_site (compile_prog twice_pi twice_procs) (Statement 3)
     = CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]"
proof (rule call_action_at_call_site_eq
    [OF twice_finC[unfolded twice_cfg_def] compile_prog_calls_source_unique])
  show "(Statement 3, CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10],
          FunctionEntry (STR ''twice''), Statement 4)
          \<in> calls (compile_prog twice_pi twice_procs)"
    by eval
qed

text \<open>\<^const>\<open>entry_state_context_rel\<close> is a relation, not a function: it admits a context
  rather than picking one, so the honest replacement for the old equation is membership at
  \<^const>\<open>ctx_call1\<close>/\<^const>\<open>ctx_call2\<close> under any store the call site actually covers.\<close>

lemma twice_context_at_call1:
  assumes sin: "s \<in> interval_gamma twice_gs (locals (snd twice_ctx_sol (Inl (Statement 2, []))))
                  (globs (snd twice_ctx_sol (Inr (Analysis_Global ()))))"
  shows "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs
           (Statement 2) [] (call_info_of (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) (STR ''twice''))
           s (call_enter twice_gs (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) s) ctx_call1"
proof -
  let ?ci = "call_info_of (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) (STR ''twice'')"
  let ?d = "locals (snd twice_ctx_sol (Inl (Statement 2, [])))"
  let ?entry = "transfer_lift twice_empty_pred (ivl_enter_st_for twice_gs ?ci) ?d"
  have cov: "entry_pairs_cover
      (\<lambda>d'. interval_gamma twice_gs d' (globs (snd twice_ctx_sol (Inr (Analysis_Global ())))))
      s (call_enter twice_gs (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) s)
      [(?d, ?entry)]"
    using interval_entry_cover_exec[OF twice_exact sin, where ci = ?ci] by simp
  have ecov: "call_enter twice_gs (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) s
                \<in> interval_gamma twice_gs ?entry (globs (snd twice_ctx_sol (Inr (Analysis_Global ()))))"
    using cov unfolding entry_pairs_cover_def by simp
  have base: "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs
      (Statement 2) [] ?ci s
      (call_enter twice_gs (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) s)
      (entry_state_route_gen twice_gs twice_empty_pred (Statement 2) [] ?entry
         (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]))"
    unfolding twice_ctx_sol_def[symmetric] routed_entry_context_rel_def
    using sin ecov by auto
  thus ?thesis by (simp add: twice_route_at_call1)
qed

lemma twice_context_at_call2:
  assumes sin: "s \<in> interval_gamma twice_gs (locals (snd twice_ctx_sol (Inl (Statement 3, []))))
                  (globs (snd twice_ctx_sol (Inr (Analysis_Global ()))))"
  shows "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs
           (Statement 3) [] (call_info_of (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) (STR ''twice''))
           s (call_enter twice_gs (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) s) ctx_call2"
proof -
  let ?ci = "call_info_of (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) (STR ''twice'')"
  let ?d = "locals (snd twice_ctx_sol (Inl (Statement 3, [])))"
  let ?entry = "transfer_lift twice_empty_pred (ivl_enter_st_for twice_gs ?ci) ?d"
  have cov: "entry_pairs_cover
      (\<lambda>d'. interval_gamma twice_gs d' (globs (snd twice_ctx_sol (Inr (Analysis_Global ())))))
      s (call_enter twice_gs (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) s)
      [(?d, ?entry)]"
    using interval_entry_cover_exec[OF twice_exact sin, where ci = ?ci] by simp
  have ecov: "call_enter twice_gs (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) s
                \<in> interval_gamma twice_gs ?entry (globs (snd twice_ctx_sol (Inr (Analysis_Global ()))))"
    using cov unfolding entry_pairs_cover_def by simp
  have base: "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs
      (Statement 3) [] ?ci s
      (call_enter twice_gs (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) s)
      (entry_state_route_gen twice_gs twice_empty_pred (Statement 3) [] ?entry
         (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]))"
    unfolding twice_ctx_sol_def[symmetric] routed_entry_context_rel_def
    using sin ecov by auto
  thus ?thesis by (simp add: twice_route_at_call2)
qed



subsection \<open>The concrete store-decoding context, and its agreement with the analysis\<close>

definition ivl_context :: "cfg_node \<Rightarrow> ivl list \<Rightarrow> store \<Rightarrow> ivl list" where
  "ivl_context = formals_context_sem twice_cfg ivl_decode"

text \<open>\<^const>\<open>ivl_context\<close> is the \<^emph>\<open>semantic\<close> reading of the same partial-tabulation policy
  (\<^cite>\<open>SeidlEtAl2026\<close> Example 8): it decodes the concrete entered store's formals
  through \<^const>\<open>ivl_decode\<close>, looking its formals up from the call site via
  \<^const>\<open>formals_at_call_site\<close>.  \<^const>\<open>entry_state_context_rel\<close> instead ignores the store and
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

lemma enter_route_exact_call1:
  assumes "u = Statement 2"
    and "s' = call_enter twice_gs (CallEdge dst [(STR ''p'')] [VIMP_Syntax.N 3]) s"
  shows "ivl_context u ctx s' = ctx_call1"
proof -
  from assms(2) have "s' = (enter_state twice_gs s)((STR ''p'') := 3)"
    by (simp add: call_enter_CallEdge)
  thus ?thesis
    unfolding assms(1) ivl_context_def formals_context_sem_def
    by (simp add: twice_formals_at_call_site2 formals_context_def ivl_decode_def ctx_call1_val)
qed

lemma enter_route_exact_call2:
  assumes "u = Statement 3"
    and "s' = call_enter twice_gs (CallEdge dst [(STR ''p'')] [VIMP_Syntax.N 10]) s"
  shows "ivl_context u ctx s' = ctx_call2"
proof -
  from assms(2) have "s' = (enter_state twice_gs s)((STR ''p'') := 10)"
    by (simp add: call_enter_CallEdge)
  thus ?thesis
    unfolding assms(1) ivl_context_def formals_context_sem_def
    by (simp add: twice_formals_at_call_site3 formals_context_def ivl_decode_def ctx_call2_val)
qed

text \<open>The semantic store-decode and the routed relation agree: the value \<^const>\<open>ivl_context\<close>
  computes from the concrete entered store is itself an admitted context, at each call
  site's own edge (the relation, unlike the retired function, genuinely depends on which
  edge produced the entry, so this no longer generalizes over an arbitrary \<open>dst\<close>).\<close>

theorem ivl_context_is_entry_state_context_call1:
  assumes cov: "s \<in> interval_gamma twice_gs (locals (snd twice_ctx_sol (Inl (Statement 2, []))))
                  (globs (snd twice_ctx_sol (Inr (Analysis_Global ()))))"
    and es: "s' = call_enter twice_gs (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) s"
  shows "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs
           (Statement 2) [] (call_info_of (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]) (STR ''twice''))
           s s' (ivl_context (Statement 2) [] s')"
proof -
  have "ivl_context (Statement 2) [] s' = ctx_call1"
    by (rule enter_route_exact_call1[OF refl es])
  thus ?thesis using twice_context_at_call1[OF cov] es by simp
qed

theorem ivl_context_is_entry_state_context_call2:
  assumes cov: "s \<in> interval_gamma twice_gs (locals (snd twice_ctx_sol (Inl (Statement 3, []))))
                  (globs (snd twice_ctx_sol (Inr (Analysis_Global ()))))"
    and es: "s' = call_enter twice_gs (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) s"
  shows "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs
           (Statement 3) [] (call_info_of (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]) (STR ''twice''))
           s s' (ivl_context (Statement 3) [] s')"
proof -
  have "ivl_context (Statement 3) [] s' = ctx_call2"
    by (rule enter_route_exact_call2[OF refl es])
  thus ?thesis using twice_context_at_call2[OF cov] es by simp
qed


subsection \<open>Shared-state regression facts\<close>

text \<open>The local unknown carries the whole abstract state, so a variable that is shared
  across activations is read at the very same slot as a formal.  A name that
  \<^const>\<open>twice_program\<close> never declares --- \<open>Gx\<close> --- therefore reads identically in both
  callee contexts: no name-based \<open>is_global\<close> convention gives it a separate,
  context-indexed slot.\<close>
lemma global_slot_shared:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call1)))) (STR ''Gx'')
     = twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call2)))) (STR ''Gx'')"
  unfolding ctx_call1_val ctx_call2_val twice_ctx_sol_def twice_empty_pred_def by eval

text \<open>The solver-global carrier stays inert: every field of the Base-style specification
  threads its incoming \<open>g\<close> through unchanged, so the shared \<^const>\<open>Global\<close> unknown is
  never used to reconstruct program state.\<close>
lemma twice_ctx_global_slot_inert:
  "globs (snd twice_ctx_sol (Inr (Analysis_Global ()))) = Bot"
  unfolding twice_ctx_sol_def twice_empty_pred_def by eval

end

