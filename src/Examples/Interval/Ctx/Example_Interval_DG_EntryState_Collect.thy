theory Example_Interval_DG_EntryState_Collect
  imports
    Example_Interval_DG_EntryState_Sound
    "Voblint_Analysis.Interval_Point_Digest"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.DG_Ctx_Activation"
begin

section \<open>Activation-indexed collecting soundness: one context covers every __voblint_nondet_int() draw\<close>

text \<open>
  The connecting theorem between the routed executable post-solution and the
  semantic activation-indexed collecting semantics, instantiating the generic
  \<open>activation_collect_sound\<close> exactly as
  a companion "twice" example does for a program with literal call arguments.  The
  difference is \<open>rc_context\<close>: instead of decoding the concrete entered store (as
  \<open>ivl_context\<close> does for \<open>twice\<close>'s literal-argument calls), \<open>rc_context\<close> ignores its
  store argument and always returns the caller's already-solved routed value.  That
  single design choice is what turns the per-value exact-context story into the
  one-context coverage story: every concrete \<open>__voblint_nondet_int()\<close> outcome enters under the
  very same admissible context \<open>ctx_call\<close>, because \<open>rc_context\<close> never looks at which
  outcome it was.
\<close>

subsection \<open>The semantic solution projection\<close>

definition rc_ctx_sg :: "pp \<times> ivl list + gk \<Rightarrow> ivl abs_state" where
  "rc_ctx_sg k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst rc_ctx_sol
           then combine_env_abs rc_gs
                 (locals ((fun_of_dg_st_for rc_gs \<circ> snd rc_ctx_sol) (Inl (v, ctx))))
                  (globs ((fun_of_dg_st_for rc_gs \<circ> snd rc_ctx_sol) (Inr Global)))
           else bot)
      | Inr _ \<Rightarrow> bot)"

abbreviation sigma_abs :: "pp \<times> ivl list + gk \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "sigma_abs \<equiv> fun_of_dg_st_for rc_gs \<circ> snd rc_ctx_sol"

abbreviation gen_abs :: "(pp \<times> ivl list, gk, (ivl abs_state, ivl abs_state) dg_state) eqsT" where
  "gen_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_abs_gen
       (routed_cmb Sabs Global Seed) (routed_extra Seed Global) rc_cfg Sabs
       (fun_of_exec_dg_st_for rc_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for rc_gs cinit_ivl_st)
       (fun_of_exec_dg_st_for rc_gs (restrict_global_resolved_q cinit_ivl_st))"

subsection \<open>The entry-state context route: ignores the concrete store\<close>

text \<open>The trace-semantic context function for the one call in \<open>rc_program\<close>.  Unlike
  \<open>formals_context\<close> (which decodes the concrete store \<open>s\<close> through a domain's point
  abstraction), \<open>rc_context\<close> discards \<open>s\<close> entirely and recomputes the routed value
  from the caller's own solved abstract state --- the same value \<open>route_abs_gen\<close>
  already selected when the executable solver ran.  This is \<open>admiss_exact\<close>'s
  functional shape, specialized so that coverage of infinitely many concrete stores
  comes from the caller's own value being \<open>Top\<close>, not from \<open>rc_context\<close> being
  genuinely multi-valued.\<close>
definition rc_context :: "cfg_node \<Rightarrow> ivl list \<Rightarrow> store \<Rightarrow> ivl list" where
  "rc_context u ctx s =
     route_abs (locals (sigma_abs (Inl (u, ctx))))
       (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')])"

lemma pp_eq_bound:
  "(v, ctx) \<in> fst rc_ctx_sol \<Longrightarrow> eq gen_abs (v, ctx) sigma_abs \<le> sigma_abs (Inl (v, ctx))"
  using rc_ctx_pp_abs by simp

lemma rc_ctx_sg_covered:
  "(v, ctx) \<in> fst rc_ctx_sol
   \<Longrightarrow> rc_ctx_sg (Inl (v, ctx))
       = combine_env_abs rc_gs (locals (sigma_abs (Inl (v, ctx)))) (globs (sigma_abs (Inr Global)))"
  by (simp add: rc_ctx_sg_def)

lemma rc_ctx_sg_uncovered_empty:
  "(v, ctx) \<notin> fst rc_ctx_sol \<Longrightarrow> \<lbrakk>rc_ctx_sg (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: rc_ctx_sg_def gamma_state_bot)

subsection \<open>ENTRY_G: the initial stores lie in the seeded entry slot\<close>

lemma entry_locals_ge_s0d:
  assumes cov: "(cfg_entry rc_cfg, []) \<in> fst rc_ctx_sol"
  shows "fun_of_exec_dg_st_for rc_gs cinit_ivl_st \<le> locals (sigma_abs (Inl (cfg_entry rc_cfg, [])))"
proof -
  have "fun_of_exec_dg_st_for rc_gs cinit_ivl_st \<le> locals (eq gen_abs (cfg_entry rc_cfg, []) sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_abs (Inl (cfg_entry rc_cfg, [])))"
    using pp_eq_bound[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma entry_covered: "(cfg_entry rc_cfg, []) \<in> fst rc_ctx_sol"
  unfolding rc_ctx_sol_def rc_ctx_eqs_def by eval

lemma cinit_le_cinit_ivl_st: "cinit_stores rc_gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for rc_gs cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)

subsection \<open>Solved-domain closure facts\<close>

lemma rc_fwd_closed_all:
  "\<forall>(u, c)\<in>fst rc_ctx_sol. \<forall>(u', a, v)\<in>intra rc_cfg. u = u' \<longrightarrow> (v, c) \<in> fst rc_ctx_sol"
  unfolding rc_ctx_sol_def rc_ctx_eqs_def by eval

lemma rc_fwd_closed:
  assumes "(u, ctx) \<in> fst rc_ctx_sol" and "(u, a, v) \<in> intra rc_cfg"
  shows "(v, ctx) \<in> fst rc_ctx_sol"
  using rc_fwd_closed_all assms by fastforce

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation rc_dg: dg_ctx_activation Sabs rc_gs rc_cfg Global route_abs_gen
    "routed_cmb Sabs Global Seed" "routed_extra Seed Global"
    "fun_of_exec_dg_st_for rc_gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for rc_gs cinit_ivl_st"
    "fun_of_exec_dg_st_for rc_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_abs "fst rc_ctx_sol" "(cfg_exit rc_cfg, [])" rc_ctx_sg
proof unfold_locales
  show "finite (intra rc_cfg)" by (rule rc_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_abs_gen
             (routed_cmb Sabs Global Seed) (routed_extra Seed Global) rc_cfg Sabs
             (fun_of_exec_dg_st_for rc_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for rc_gs cinit_ivl_st)
             (fun_of_exec_dg_st_for rc_gs (restrict_global_resolved_q cinit_ivl_st)))
          (cfg_exit rc_cfg, []) sigma_abs (fst rc_ctx_sol)"
    by (rule rc_ctx_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst rc_ctx_sol"
  thus "rc_ctx_sg (Inl (v, ctx))
          = combine_env_abs rc_gs (locals (sigma_abs (Inl (v, ctx)))) (globs (sigma_abs (Inr Global)))"
    by (rule rc_ctx_sg_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst rc_ctx_sol"
  thus "\<lbrakk>rc_ctx_sg (Inl (v, ctx))\<rbrakk> = {}"
    by (rule rc_ctx_sg_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst rc_ctx_sol" "(u, a, v) \<in> intra rc_cfg"
  thus "(v, ctx) \<in> fst rc_ctx_sol" by (rule rc_fwd_closed)
qed

subsection \<open>The one call is covered only under the root context\<close>

lemma call_caller_only_bot:
  "\<forall>(p, ctx)\<in>fst rc_ctx_sol. p = Statement 3 \<longrightarrow> ctx = []"
  unfolding rc_ctx_sol_def rc_ctx_eqs_def by eval

lemma covered_cont: "(Statement 4, []) \<in> fst rc_ctx_sol"
  unfolding rc_ctx_sol_def rc_ctx_eqs_def by eval

lemma callee_exit_covered_call: "(FunctionResult (STR ''p''), ctx_call) \<in> fst rc_ctx_sol"
  unfolding rc_ctx_sol_def rc_ctx_eqs_def ctx_call_def by eval

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

text \<open>The routed interval solution also interprets \<^locale>\<open>routed_context\<close>.
  \<open>route_enterc_agree\<close> is trivial here --- unlike \<open>twice\<close>'s, which needs
  \<open>enter_route_exact\<close> read back through \<open>route_commute\<close> at each literal argument
  --- because \<open>rc_context\<close> is \<^emph>\<open>defined\<close> to recompute exactly the routed value
  \<open>route_abs_gen\<close> already produces, so both sides of the agreement are the same
  term up to \<open>route_commute_gen\<close> and the single call site's shape, closing by
  \<open>simp\<close> without touching the concrete store \<open>s\<close> at all.\<close>

interpretation rc_routed: routed_context Sabs rc_gs rc_cfg Global route_abs_gen
    "fun_of_exec_dg_st_for rc_gs (bot::ivl exec_dg_st)"
    "fun_of_exec_dg_st_for rc_gs cinit_ivl_st"
    "fun_of_exec_dg_st_for rc_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_abs "fst rc_ctx_sol" "(cfg_exit rc_cfg, [])" rc_ctx_sg
    Seed rc_context
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule rc_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  note ce = RouteAgree(2)
  from ce rc_calls_shape have shape:
    "u = Statement 3" "dst = Some (STR ''y'')" "pars = [(STR ''a'')]" "args = [V (STR ''x'')]"
    "p = (STR ''p'')"
    by fastforce+
  show ?case unfolding shape rc_context_def route_abs_gen_def by simp
next
  case (CallFwd u ctx dst pars args p cont)
  note covU = CallFwd(1) and ce = CallFwd(2)
  from ce rc_calls_shape have shape:
    "u = Statement 3" "dst = Some (STR ''y'')" "pars = [(STR ''a'')]" "args = [V (STR ''x'')]"
    "p = (STR ''p'')"
    by fastforce+
  have ctxb: "ctx = []" using covU shape call_caller_only_bot by fastforce
  have "route_abs_gen u ctx (locals (sigma_abs (Inl (u, ctx)))) (CallEdge dst pars args) = ctx_call"
    unfolding shape ctxb ctx_call_def
    by (simp add: route_commute_gen[symmetric] route_ivl_gen_def)
  thus ?case using shape by (simp add: callee_covered_call)
next
  case (CombFwd cl c1 dst pars args p cont)
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl call_caller_only_bot covered_cont rc_calls_shape by fastforce
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce rc_calls_unique_site unfolding call_enter_store_def by fastforce
qed

lemma rc_ctx_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls rc_cfg"
    and "s \<in> \<lbrakk>rc_ctx_sg (Inl (u, ctx))\<rbrakk>"
  shows "call_enter rc_gs (CallEdge dst xs es) s
           \<in> \<lbrakk>rc_ctx_sg (Inl (FunctionEntry p,
                 rc_context u ctx (call_enter rc_gs (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule rc_routed.routed_context_call[OF assms])

lemma rc_ctx_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls rc_cfg"
    and "s \<in> \<lbrakk>rc_ctx_sg (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>rc_ctx_sg (Inl (FunctionResult p, rc_context cl c1 es))\<rbrakk>"
    and "call_enter_store rc_gs rc_cfg cl s es"
  shows "combine_collect rc_gs dst s t \<in> \<lbrakk>rc_ctx_sg (Inl (v, c1))\<rbrakk>"
  by (rule rc_routed.routed_context_comb[OF assms])

subsection \<open>Activation-indexed collecting soundness\<close>

theorem rc_activation_collect_sound:
  "activation_collect rc_gs (admiss_exact rc_context) [] rc_cfg (cinit_stores rc_gs) v ctx
     \<subseteq> \<lbrakk>rc_ctx_sg (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = rc_ctx_sg and admiss = "admiss_exact rc_context"
        and startcontext = "[]"
        and S = "cinit_stores rc_gs" and g = rc_cfg and gs = rc_gs])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores rc_gs"
  hence "s \<in> \<lbrakk>fun_of_exec_dg_st_for rc_gs cinit_ivl_st\<rbrakk>" using cinit_le_cinit_ivl_st by blast
  also have "\<lbrakk>fun_of_exec_dg_st_for rc_gs cinit_ivl_st\<rbrakk>
        = gamma_unit rc_gs (fun_of_exec_dg_st_for rc_gs cinit_ivl_st)
            (fun_of_exec_dg_st_for rc_gs (restrict_global_resolved_q cinit_ivl_st))"
    unfolding gamma_unit_def fun_of_exec_dg_st_for_def
    by (rule arg_cong[where f = gamma_state], rule ext)
       (simp add: combine_env_abs_def restrict_global_for_def)
  also have "\<dots> \<subseteq> gamma_unit rc_gs (locals (sigma_abs (Inl (cfg_entry rc_cfg, []))))
                   (globs (sigma_abs (Inr Global)))"
    by (rule gamma_unit_mono[OF entry_locals_ge_s0d[OF entry_covered]
          rc_dg.pp_entry_s0g_bound[OF entry_covered]])
  also have "\<dots> = \<lbrakk>rc_ctx_sg (Inl (cfg_entry rc_cfg, []))\<rbrakk>"
    unfolding rc_ctx_sg_covered[OF entry_covered] gamma_unit_def by (rule refl)
  finally show "s \<in> \<lbrakk>rc_ctx_sg (Inl (cfg_entry rc_cfg, []))\<rbrakk>" .
next
  \<comment> \<open>EDGE\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra rc_cfg
        \<Longrightarrow> s \<in> \<lbrakk>rc_ctx_sg (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>rc_ctx_sg (Inl (v, c))\<rbrakk>"
    by (rule rc_dg.dg_ctx_act_edge)
next
  \<comment> \<open>ADMISS_TOTAL\<close>
  show "\<And>u c s. \<exists>c'. admiss_exact rc_context u c s c'"
    by (simp add: admiss_exact_def)
next
  \<comment> \<open>CALL\<close>
  fix u dst pars args p cont c s c'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls rc_cfg"
    and sm: "s \<in> \<lbrakk>rc_ctx_sg (Inl (u, c))\<rbrakk>"
    and adm: "admiss_exact rc_context u c (call_enter rc_gs (CallEdge dst pars args) s) c'"
  show "call_enter rc_gs (CallEdge dst pars args) s \<in> \<lbrakk>rc_ctx_sg (Inl (FunctionEntry p, c'))\<rbrakk>"
    using adm rc_ctx_sg_seed[OF ce sm] by (simp add: admiss_exact_def)
next
  \<comment> \<open>COMB\<close>
  fix cl dst pars args p cont c1 c2 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls rc_cfg"
    and sm: "s \<in> \<lbrakk>rc_ctx_sg (Inl (cl, c1))\<rbrakk>"
    and adm: "admiss_exact rc_context cl c1 es c2"
    and tm: "t \<in> \<lbrakk>rc_ctx_sg (Inl (FunctionResult p, c2))\<rbrakk>"
    and ces: "call_enter_store rc_gs rc_cfg cl s es"
  show "combine_collect rc_gs dst s t \<in> \<lbrakk>rc_ctx_sg (Inl (cont, c1))\<rbrakk>"
    using adm tm rc_ctx_sg_comb[OF ce sm _ ces] by (simp add: admiss_exact_def)
qed

subsection \<open>Acceptance witness: one context covers every \<open>__voblint_nondet_int()\<close> draw\<close>

text \<open>The crux corollary: for \<^emph>\<open>every\<close> concrete store \<open>s\<close> that reaches the call site
  (in particular, every store obtained by any \<open>__voblint_nondet_int()\<close> outcome, since \<open>x\<close>'s solved
  interval there is \<open>Top\<close>), the callee entry lands at the \<^emph>\<open>same, fixed\<close> context
  \<open>ctx_call\<close>.  The conclusion's context component is the literal constant \<open>ctx_call\<close>,
  not an expression mentioning \<open>s\<close>: nothing here is a family of contexts indexed by
  which concrete argument occurred, in contrast to \<open>twice\<close>'s two exact contexts, one
  per literal call-site argument.\<close>
corollary entry_state_coverage:
  assumes sm: "s \<in> \<lbrakk>rc_ctx_sg (Inl (Statement 3, []))\<rbrakk>"
  shows "call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s
           \<in> \<lbrakk>rc_ctx_sg (Inl (FunctionEntry (STR ''p''), ctx_call))\<rbrakk>"
proof -
  have ce: "(Statement 3, CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')],
              FunctionEntry (STR ''p''), Statement 4) \<in> calls rc_cfg"
    unfolding rc_cfg_def by eval
  have "rc_context (Statement 3) [] (call_enter rc_gs (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]) s)
          = ctx_call"
    unfolding rc_context_def ctx_call_def by (simp add: fun_of_dg_st_for_simps route_commute)
  thus ?thesis using rc_ctx_sg_seed[OF ce sm] by simp
qed

text \<open>Unfolding \<^const>\<open>activation_collect\<close> at \<open>ctx_call\<close> makes the \<open>ctx_key\<close> side of
  the same fact syntactically manifest: every concrete callee-entry trace this set
  counts --- one per concrete \<open>__voblint_nondet_int()\<close> outcome that actually occurs --- is one
  whose \<open>ctx_key\<close> equals the single context \<open>ctx_call\<close>, not a family of contexts
  varying with the trace.  \<open>rc_activation_collect_sound\<close> then bounds this whole set,
  every context alike, in \<open>\<lbrakk>rc_ctx_sg (Inl (FunctionEntry (STR ''p''), ctx_call))\<rbrakk>\<close>.\<close>
corollary entry_state_activation_ctx_key:
  "activation_collect rc_gs (admiss_exact rc_context) [] rc_cfg (cinit_stores rc_gs)
     (FunctionEntry (STR ''p'')) ctx_call
   = {sink_store t | t. t \<in> valid_ltr rc_gs rc_cfg (cinit_stores rc_gs)
        \<and> sink_node t = FunctionEntry (STR ''p'') \<and> ctx_key (admiss_exact rc_context) [] t ctx_call}"
  unfolding activation_collect_def by (rule refl)

end
