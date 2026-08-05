theory Example_Interval_DG_Ctx_Collect
  imports
    Example_Interval_DG_Ctx_Sound
    "Voblint_Analysis.Interval_Point_Digest"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.DG_Ctx_Activation"
begin

section \<open>Activation-indexed collecting soundness for the routed interval solution\<close>

text \<open>
  The connecting theorem between the routed executable post-solution
  (\<open>twice_ctx_pp_abs\<close>) and the semantic activation-indexed collecting semantics.  It
  instantiates the generic \<open>activation_collect_sound\<close> and discharges its four obligations
  --- \<open>ENTRY_G\<close>, \<open>EDGE\<close>, \<open>SEED_G\<close>, \<open>COMB\<close> --- as separate lemmas.  Coverage is internalised
  in the guarded reader \<open>ivl_ctx_sg\<close> (uncovered unknowns denote \<open>{}\<close>), real globals are
  shared through the single \<open>Global\<close> slot, and the return combine reads the callee exit at
  the routed context (\<open>ivl_ctx_sg_comb\<close>).
\<close>

subsection \<open>The semantic context route and the abstract solution projection\<close>

text \<open>A call selects the point abstraction of the callee formal in the entered
  store. Returns resume the caller context, and the root uses @{const bot}.
  \<open>ivl_ctx_sg\<close> joins the routed local slot with the shared global slot expected by
  @{thm activation_collect_sound}.\<close>

definition ivl_enterc :: "cfg_node \<Rightarrow> ivl \<Rightarrow> store \<Rightarrow> ivl" where
  "ivl_enterc u ctx s = ivl_decode (s ''p'')"

text \<open>The reader is guarded by the \<^emph>\<open>solved domain\<close> \<open>fst twice_ctx_sol\<close>: the solver
  returns a partial solution, so an unknown outside \<open>vars\<close> is an artefact of the total
  implementation function and must denote no states.  A covered \<^const>\<open>Inl\<close> slot reads
  the transported local slot joined with its context's real-global slot; every other key
  (uncovered local, or any \<^const>\<open>Inr\<close> global key, which \<open>activation_collect_sound\<close> never
  consults) denotes \<open>\<bottom>\<close>.  Uncovered points thus have empty concretization by
  construction, with no appeal to solver leastness.\<close>
definition ivl_ctx_sg :: "pp \<times> ivl + gk \<Rightarrow> ivl abs_state" where
  "ivl_ctx_sg k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst twice_ctx_sol
           then locals ((fun_of_dg_st_for twice_gs \<circ> snd twice_ctx_sol) (Inl (v, ctx)))
                \<squnion> globs ((fun_of_dg_st_for twice_gs \<circ> snd twice_ctx_sol) (Inr Global))
           else bot)
      | Inr _ \<Rightarrow> bot)"

subsection \<open>Reusable post-solution elimination\<close>

text \<open>One name for the transported abstract solution and the abstract routed generator
  that \<open>twice_ctx_pp_abs\<close> is a post-solution of.  The two projections below --- the
  per-slot value bound (\<open>eq \<le> \<sigma>(Inl \<dots>)\<close>) and the side-effect bound
  (\<open>sides_of_rhs \<le> \<sigma>\<close>) --- are the single elimination of \<open>part_post_solution\<close> that
  \<open>EDGE\<close>, \<open>SEED_G\<close>, and \<open>COMB\<close> all read through; the post-solution is never unfolded
  again inside a semantic obligation.\<close>

abbreviation sigma_abs :: "pp \<times> ivl + gk \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "sigma_abs \<equiv> fun_of_dg_st_for twice_gs \<circ> snd twice_ctx_sol"

abbreviation gen_abs :: "(pp \<times> ivl, gk, (ivl abs_state, ivl abs_state) dg_state) eqsT" where
  "gen_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_abs_gen
       (routed_cmb Sabs Global) (routed_extra twice_cfg Sabs Seed Global) twice_cfg Sabs
       (fun_of_exec_dg_st_for twice_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
       (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st))"

lemma pp_eq_bound:
  "(v, ctx) \<in> fst twice_ctx_sol
     \<Longrightarrow> eq gen_abs (v, ctx) sigma_abs \<le> sigma_abs (Inl (v, ctx))"
  using twice_ctx_pp_abs by simp

text \<open>The two faces of the guarded reader: on the solved domain it is the transported
  local slot joined with its real-global slot; off it, \<open>\<bottom>\<close> (empty concretization).\<close>

lemma ivl_ctx_sg_covered:
  "(v, ctx) \<in> fst twice_ctx_sol
   \<Longrightarrow> ivl_ctx_sg (Inl (v, ctx))
       = locals (sigma_abs (Inl (v, ctx))) \<squnion> globs (sigma_abs (Inr Global))"
  by (simp add: ivl_ctx_sg_def)

lemma ivl_ctx_sg_uncovered_empty:
  "(v, ctx) \<notin> fst twice_ctx_sol \<Longrightarrow> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: ivl_ctx_sg_def gamma_state_bot)

subsection \<open>ENTRY_G: the initial stores lie in the seeded entry slot\<close>

text \<open>The accumulator fold only grows the start value.\<close>
lemma side_acc_dg_ge: "acc \<le> side_acc_dg acc \<tau> ts"
proof (induction ts arbitrary: acc)
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc \<squnion> locals (traverse_rhs t \<tau>)"]
    by (simp add: le_supI1)
qed simp

text \<open>The entry local slot dominates the initial abstract store \<open>s0d\<close>.\<close>
lemma entry_locals_ge_s0d:
  assumes cov: "(cfg_entry twice_cfg, bot) \<in> fst twice_ctx_sol"
  shows "fun_of_exec_dg_st_for twice_gs cinit_ivl_st \<le> locals (sigma_abs (Inl (cfg_entry twice_cfg, bot)))"
proof -
  have "fun_of_exec_dg_st_for twice_gs cinit_ivl_st \<le> locals (eq gen_abs (cfg_entry twice_cfg, bot) sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_abs (Inl (cfg_entry twice_cfg, bot)))"
    using pp_eq_bound[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma entry_covered: "(cfg_entry twice_cfg, bot) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def Spoly_def by eval

lemma cinit_le_cinit_ivl_st: "cinit_stores twice_gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for twice_gs cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)

text \<open>
  \<^bold>\<open>Regression: the callee entry stays absent at the root context.\<close>  \<^const>\<open>cfg_entry\<close>
  of \<open>twice_cfg\<close> is \<open>FunctionEntry ''main''\<close>, and \<open>main\<close>'s first statement is the call
  \<open>(Statement 2, CallEdge (Some ''x'') [''p''] [N 3], FunctionEntry ''twice'', Statement 3)\<close>.
  The polyvariant solver routes \<open>FunctionEntry ''twice''\<close> to the argument contexts
  \<open>[3,3]\<close> / \<open>[10,10]\<close> and leaves it unpopulated at \<open>bot\<close> --- \<open>p\<close> there is the bottom
  interval.  The activation-local semantics (\<^theory>\<open>Voblint_CFG.CFG_Local_Trace\<close>) creates a
  callee only through the \<open>call\<close> rule, whose entry store is \<^const>\<open>call_enter\<close> of the
  \<^const>\<open>CallEdge\<close> at the routed context \<open>enterc seedc s'\<close> (\<open>= [3,3]\<close>), \<^emph>\<open>not\<close>
  \<open>seedc = bot\<close>, so no obligation forces the callee under the root context.  These witnesses
  keep that invariant honest.\<close>

lemma callee_entry_bot_unpopulated:
  "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (FunctionEntry ''twice'', bot)))) ''p'' = \<bottom>"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def Spoly_def by eval

lemma main_first_stmt_is_call:
  "(Statement 2, CallEdge (Some ''x'') [''p''] [VIMP_Syntax.N 3],
    FunctionEntry ''twice'', Statement 3) \<in> calls twice_cfg"
  by eval

subsection \<open>Solved-domain closure facts\<close>

text \<open>\<^bold>\<open>Forward closure along intra edges.\<close>  Every \<^const>\<open>intra\<close> successor of a solved node
  stays solved \<^emph>\<open>at the same context\<close>.  No \<open>is_enter_action\<close> side condition is needed because
  \<^const>\<open>intra\<close> and call edges have distinct types.  This is not a generic solver
  invariant --- it holds because every \<open>twice\<close> node reaches the exit, so the exit query's
  backward cone materialises the whole intra-context chain.  It is a decidable closed check
  over the finite solved domain and the finite edge set (\<^bold>\<open>all\<close> solved contexts, not the two
  observed by \<open>eval\<close>).\<close>
lemma twice_fwd_closed_all:
  "\<forall>(u, c)\<in>fst twice_ctx_sol. \<forall>(u', a, v)\<in>intra twice_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval

lemma twice_fwd_closed:
  assumes "(u, ctx) \<in> fst twice_ctx_sol" and "(u, a, v) \<in> intra twice_cfg"
  shows "(v, ctx) \<in> fst twice_ctx_sol"
  using twice_fwd_closed_all assms by fastforce

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

text \<open>The routed interval solution is a \<^locale>\<open>dg_ctx_activation\<close> instance: the diagonal
  interval DG interpretation \<open>ivl_dg\<close> supplies \<^locale>\<open>sound_dg_spec\<close>, \<open>twice_ctx_pp_abs\<close> the
  post-solution, and the guarded reader / forward closure the remaining axioms.  \<open>EDGE\<close>
  and the combine transport are then read off as \<open>twice_dg.dg_ctx_act_edge\<close> /
  \<open>twice_dg.dg_ctx_act_comb_covered\<close> rather than re-proved by hand.\<close>

text \<open>\<open>ivl_dg_for\<close> (\<open>Example_Interval_DG_Ctx_Sound\<close>) already establishes
  \<^locale>\<open>sound_dg_spec\<close> \<open>Sabs gamma_unit twice_gs\<close>, so the obligations
  \<open>dg_ctx_activation\<close> inherits from it discharge automatically below.\<close>

interpretation twice_dg: dg_ctx_activation Sabs twice_gs twice_cfg Global route_abs_gen
    "routed_cmb Sabs Global" "routed_extra twice_cfg Sabs Seed Global"
    "fun_of_exec_dg_st_for twice_gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for twice_gs cinit_ivl_st"
    "fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_abs "fst twice_ctx_sol" "(cfg_exit twice_cfg, bot)" ivl_ctx_sg
proof unfold_locales
  show "finite (intra twice_cfg)" by (rule twice_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_abs_gen
             (routed_cmb Sabs Global) (routed_extra twice_cfg Sabs Seed Global) twice_cfg Sabs
             (fun_of_exec_dg_st_for twice_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
             (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st)))
          (cfg_exit twice_cfg, bot) sigma_abs (fst twice_ctx_sol)"
    by (rule twice_ctx_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst twice_ctx_sol"
  thus "ivl_ctx_sg (Inl (v, ctx))
          = locals (sigma_abs (Inl (v, ctx))) \<squnion> globs (sigma_abs (Inr Global))"
    by (rule ivl_ctx_sg_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst twice_ctx_sol"
  thus "\<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk> = {}"
    by (rule ivl_ctx_sg_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst twice_ctx_sol" "(u, a, v) \<in> intra twice_cfg"
  thus "(v, ctx) \<in> fst twice_ctx_sol" by (rule twice_fwd_closed)
qed

subsection \<open>Shared-global regression facts\<close>

text \<open>The reader combines context-sensitive locals with one shared global slot.
  The initial global value @{text 0} is therefore identical in the root and both callee
  contexts, without copying global state into context-indexed unknowns.\<close>

lemma global_init_present:
  "lookup_exec_dg_st (globs (snd twice_ctx_sol (Inr Global))) ''Gx'' = Ivl (Fin 0) (Fin 0)"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval

lemma global_slot_shared:
  "ivl_ctx_sg (Inl (FunctionEntry ''twice'', ctx_call1)) ''Gx''
     = ivl_ctx_sg (Inl (FunctionEntry ''twice'', ctx_call2)) ''Gx''"
proof -
  have "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (FunctionEntry ''twice'', ctx_call1)))) ''Gx''
      = twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (FunctionEntry ''twice'', ctx_call2)))) ''Gx''"
    unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval
  thus ?thesis
    unfolding ivl_ctx_sg_def
    by (simp add: callee_covered_call1 callee_covered_call2
      fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_def)
qed

subsection \<open>SEED_G: the routed callee entry (enter edges)\<close>

text \<open>Enter callers are covered only under the main context (\<open>bot\<close>): \<open>twice\<close>'s two calls
  both originate from \<open>main\<close>, the root activation.  Bounded, decidable over the finite
  solved domain.\<close>
lemma enter_callers_only_bot:
  "\<forall>(p, ctx)\<in>fst twice_ctx_sol.
     (p = Statement 2 \<or> p = Statement 3) \<longrightarrow> ctx = bot"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval

text \<open>\<^bold>\<open>enter_route_exact.\<close>  The context a call routes into is the point abstraction of the
  entered formal \<open>p\<close>: for the two constant-argument calls the entered value is \<open>3\<close> / \<open>10\<close>,
  so the routed context is exactly \<open>ctx_call1\<close> / \<open>ctx_call2\<close> --- the executable route agrees
  with the activation route \<^const>\<open>ivl_enterc\<close>.\<close>
lemma enter_route_exact_call1:
  assumes "s' = call_enter twice_gs (CallEdge dst [''p''] [VIMP_Syntax.N 3]) s"
  shows "ivl_enterc u ctx s' = ctx_call1"
proof -
  from assms have "s' = (enter_state twice_gs s)(''p'' := 3)"
    by (simp add: call_enter_CallEdge bind_formals_def)
  thus ?thesis by (simp add: ivl_enterc_def ivl_decode_def ctx_call1_val)
qed

lemma enter_route_exact_call2:
  assumes "s' = call_enter twice_gs (CallEdge dst [''p''] [VIMP_Syntax.N 10]) s"
  shows "ivl_enterc u ctx s' = ctx_call2"
proof -
  from assms have "s' = (enter_state twice_gs s)(''p'' := 10)"
    by (simp add: call_enter_CallEdge bind_formals_def)
  thus ?thesis by (simp add: ivl_enterc_def ivl_decode_def ctx_call2_val)
qed

text \<open>SEED_G and COMB both land as corollaries of the routed interpretation below
  (\<open>twice_routed.routed_context_call\<close> / \<open>routed_context_comb\<close>), once the coverage
  and route-agreement facts this section built are in scope.\<close>

subsection \<open>COMB: the routed return combine\<close>

lemma covered_ret5: "(Statement 3, bot) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval
lemma covered_ret7: "(Statement 4, bot) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval
lemma callee_exit_covered_call1: "(FunctionResult ''twice'', ctx_call1) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call1_def by eval
lemma callee_exit_covered_call2: "(FunctionResult ''twice'', ctx_call2) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call2_def by eval

text \<open>\<^bold>\<open>enter_route_exact for combine.\<close>  The callee context resumed at a return is the point
  abstraction of the entered formal linked to the caller by \<^const>\<open>call_enter_store\<close>.  The
  linked entered store is exactly the enter edge's \<^const>\<open>edge_step\<close> result, so this reuses
  \<open>enter_route_exact\<close>.\<close>
lemma comb_route_call1:
  assumes "call_enter_store twice_gs twice_cfg (Statement 2) s es"
  shows "ivl_enterc u c1 es = ctx_call1"
proof -
  have "es = call_enter twice_gs (CallEdge (Some ''x'') [''p''] [VIMP_Syntax.N 3]) s"
    using assms twice_calls_shape unfolding call_enter_store_def by fastforce
  thus ?thesis by (rule enter_route_exact_call1)
qed

lemma comb_route_call2:
  assumes "call_enter_store twice_gs twice_cfg (Statement 3) s es"
  shows "ivl_enterc u c1 es = ctx_call2"
proof -
  have "es = call_enter twice_gs (CallEdge (Some ''y'') [''p''] [VIMP_Syntax.N 10]) s"
    using assms twice_calls_shape unfolding call_enter_store_def by fastforce
  thus ?thesis by (rule enter_route_exact_call2)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

text \<open>The routed interval solution also interprets \<^locale>\<open>routed_context\<close>: beyond the
  \<^locale>\<open>dg_ctx_activation\<close> axioms above, \<open>finC\<close> is finiteness of \<open>calls twice_cfg\<close>;
  \<open>seed_key_ne_gk0\<close> is the \<open>Seed\<close>/\<open>Global\<close> constructor split; \<open>route_enterc_agree\<close> is
  \<open>enter_route_exact\<close> read back at the two covered call sites via \<open>route_commute\<close>;
  \<open>call_fwd\<close> and \<open>comb_fwd\<close> are the same coverage facts that \<open>ivl_ctx_sg_seed\<close> /
  \<open>ivl_ctx_sg_comb\<close> need by hand; and \<open>call_enter_store_agree\<close> is the unique-edge
  argument already used by \<open>comb_route_call1\<close> / \<open>comb_route_call2\<close>.  CALL and COMB then
  fall out as the locale's \<open>routed_context_call\<close> / \<open>routed_context_comb\<close>.\<close>

interpretation twice_routed: routed_context Sabs twice_gs twice_cfg Global route_abs_gen
    "fun_of_exec_dg_st_for twice_gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for twice_gs cinit_ivl_st"
    "fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_abs "fst twice_ctx_sol" "(cfg_exit twice_cfg, bot)" ivl_ctx_sg Seed ivl_enterc
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule twice_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  note covU = RouteAgree(1) and ce = RouteAgree(2) and sin = RouteAgree(3)
  from ce twice_calls_shape have
    "(u = Statement 2 \<and> pars = [''p''] \<and> args = [VIMP_Syntax.N 3] \<and> p = ''twice'') \<or>
     (u = Statement 3 \<and> pars = [''p''] \<and> args = [VIMP_Syntax.N 10] \<and> p = ''twice'')"
    by fastforce
  then consider
      (c1) "u = Statement 2" "pars = [''p'']" "args = [VIMP_Syntax.N 3]" "p = ''twice''"
    | (c2) "u = Statement 3" "pars = [''p'']" "args = [VIMP_Syntax.N 10]" "p = ''twice''"
    by blast
  thus ?case
  proof cases
    case c1
    have ctxb: "ctx = bot" using covU c1 enter_callers_only_bot by fastforce
    have "route_abs_gen u ctx (locals (sigma_abs (Inl (u, ctx)))) (CallEdge dst pars args)
             = route_ivl (locals (snd twice_ctx_sol (Inl (Statement 2, bot)))) (CallEdge dst pars args)"
      using c1 ctxb by (simp add: route_commute_gen[symmetric] route_ivl_gen_def)
    also have "\<dots> = ctx_call1" using c1 by (simp add: ctx_call1_def route_ivl_def entered_ivl_def)
    finally show ?thesis using c1 by (simp add: enter_route_exact_call1)
  next
    case c2
    have ctxb: "ctx = bot" using covU c2 enter_callers_only_bot by fastforce
    have "route_abs_gen u ctx (locals (sigma_abs (Inl (u, ctx)))) (CallEdge dst pars args)
             = route_ivl (locals (snd twice_ctx_sol (Inl (Statement 3, bot)))) (CallEdge dst pars args)"
      using c2 ctxb by (simp add: route_commute_gen[symmetric] route_ivl_gen_def)
    also have "\<dots> = ctx_call2" using c2 by (simp add: ctx_call2_def route_ivl_def entered_ivl_def)
    finally show ?thesis using c2 by (simp add: enter_route_exact_call2)
  qed
next
  case (CallFwd u ctx dst pars args p cont)
  note covU = CallFwd(1) and ce = CallFwd(2)
  from ce twice_calls_shape have
    "(u = Statement 2 \<and> pars = [''p''] \<and> args = [VIMP_Syntax.N 3] \<and> p = ''twice'') \<or>
     (u = Statement 3 \<and> pars = [''p''] \<and> args = [VIMP_Syntax.N 10] \<and> p = ''twice'')"
    by fastforce
  then consider
      (c1) "u = Statement 2" "pars = [''p'']" "args = [VIMP_Syntax.N 3]" "p = ''twice''"
    | (c2) "u = Statement 3" "pars = [''p'']" "args = [VIMP_Syntax.N 10]" "p = ''twice''"
    by blast
  thus ?case
  proof cases
    case c1
    have ctxb: "ctx = bot" using covU c1 enter_callers_only_bot by fastforce
    have "route_abs_gen u ctx (locals (sigma_abs (Inl (u, ctx)))) (CallEdge dst pars args) = ctx_call1"
      using c1 ctxb
      by (simp add: route_commute_gen[symmetric] route_ivl_gen_def
                     ctx_call1_def route_ivl_def entered_ivl_def)
    with c1 show ?thesis by (simp add: callee_covered_call1)
  next
    case c2
    have ctxb: "ctx = bot" using covU c2 enter_callers_only_bot by fastforce
    have "route_abs_gen u ctx (locals (sigma_abs (Inl (u, ctx)))) (CallEdge dst pars args) = ctx_call2"
      using c2 ctxb
      by (simp add: route_commute_gen[symmetric] route_ivl_gen_def
                     ctx_call2_def route_ivl_def entered_ivl_def)
    with c2 show ?thesis by (simp add: callee_covered_call2)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl enter_callers_only_bot covered_ret5 covered_ret7 twice_calls_shape
    by fastforce
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce twice_calls_unique_site unfolding call_enter_store_def by fastforce
qed

lemma ivl_ctx_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls twice_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, ctx))\<rbrakk>"
  shows "call_enter twice_gs (CallEdge dst xs es) s
           \<in> \<lbrakk>ivl_ctx_sg (Inl (FunctionEntry p,
                 ivl_enterc u ctx (call_enter twice_gs (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule twice_routed.routed_context_call[OF assms])

lemma ivl_ctx_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls twice_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>ivl_ctx_sg (Inl (FunctionResult p, ivl_enterc cl c1 es))\<rbrakk>"
    and "call_enter_store twice_gs twice_cfg cl s es"
  shows "combine_collect twice_gs dst s t \<in> \<lbrakk>ivl_ctx_sg (Inl (v, c1))\<rbrakk>"
  by (rule twice_routed.routed_context_comb[OF assms])

subsection \<open>Activation-indexed collecting soundness (obligation scaffold)\<close>

text \<open>Instantiating the generic \<open>activation_collect_sound\<close> at the routed interval
  solution.  Five semantic obligations remain, each a separate milestone; they are
  discharged from \<open>twice_ctx_pp_abs\<close> together with the interval \<^locale>\<open>sound_dg_spec\<close>
  step / combine soundness, route consistency, and the \<open>ivl_ctx_sg_seed\<close> enter seed.\<close>

theorem twice_activation_collect_sound:
  "activation_collect twice_gs ivl_enterc bot twice_cfg (cinit_stores twice_gs) v ctx
     \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = ivl_ctx_sg and enterc = ivl_enterc
        and seedc = bot and S = "cinit_stores twice_gs" and g = twice_cfg and gs = twice_gs])
  \<comment> \<open>ENTRY_G --- mirrors \<open>twice_sound0\<close>: cinit stores lie in the seeded entry slot.\<close>
  fix s assume "s \<in> cinit_stores twice_gs"
  hence "s \<in> \<lbrakk>fun_of_exec_dg_st_for twice_gs cinit_ivl_st\<rbrakk>" using cinit_le_cinit_ivl_st by blast
  also have "\<lbrakk>fun_of_exec_dg_st_for twice_gs cinit_ivl_st\<rbrakk> \<subseteq> \<lbrakk>locals (sigma_abs (Inl (cfg_entry twice_cfg, bot)))\<rbrakk>"
    by (rule gamma_state_mono[OF entry_locals_ge_s0d[OF entry_covered]])
  also have "\<dots> \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (cfg_entry twice_cfg, bot))\<rbrakk>"
    unfolding ivl_ctx_sg_covered[OF entry_covered] by (rule gamma_state_sup_ub1)
  finally show "s \<in> \<lbrakk>ivl_ctx_sg (Inl (cfg_entry twice_cfg, bot))\<rbrakk>" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg (Inl (v, c))\<rbrakk>"
    by (rule twice_dg.dg_ctx_act_edge)
next
  \<comment> \<open>CALL --- enter routed to \<open>ivl_decode\<close> of the entered formal: \<open>ivl_ctx_sg_seed\<close>
     (route consistency + seed publication).\<close>
  show "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter twice_gs (CallEdge dst pars args) s
             \<in> \<lbrakk>ivl_ctx_sg (Inl (FunctionEntry p,
                    ivl_enterc u c (call_enter twice_gs (CallEdge dst pars args) s)))\<rbrakk>"
    by (rule ivl_ctx_sg_seed)
next
  \<comment> \<open>COMB --- return combine at the caller context \<open>c1\<close>: the resumed activation keeps its
     context, so \<open>ivl_ctx_sg_comb\<close> already lands at \<open>c1\<close>.\<close>
  show "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (cl, c1))\<rbrakk>
        \<Longrightarrow> t \<in> \<lbrakk>ivl_ctx_sg (Inl (FunctionResult p, ivl_enterc cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store twice_gs twice_cfg cl s es
        \<Longrightarrow> combine_collect twice_gs dst s t \<in> \<lbrakk>ivl_ctx_sg (Inl (cont, c1))\<rbrakk>"
    by (rule ivl_ctx_sg_comb)
qed

end


