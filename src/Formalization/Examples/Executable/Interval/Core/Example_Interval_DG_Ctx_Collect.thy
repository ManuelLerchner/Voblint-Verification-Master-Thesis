theory Example_Interval_DG_Ctx_Collect
  imports
    Example_Interval_DG_Ctx_Sound
    "Voblint_Analysis.Interval_Point_Digest"
    "Voblint_Analysis.Seeded_Activation_Sound"
    "Voblint_Analysis.DG_Ctx_Activation"
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

text \<open>The concrete (semantic) context selection, forced Goblint-faithfully: a call
  enters the context that is the point abstraction of the callee formal in the
  \<^emph>\<open>entered\<close> store; the return resumes the caller context; the root context is \<open>bot\<close>.
  \<open>ivl_ctx_sg\<close> reads the routed solution's local slot joined with its real-global
  slot --- the single \<^typ>\<open>ivl abs_state\<close> that \<open>activation_collect_sound\<close> wants.\<close>

definition ivl_enterc :: "ivl \<Rightarrow> store \<Rightarrow> ivl" where
  "ivl_enterc ctx s = ivl_decode (s ''p'')"

definition ivl_combc :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_combc c1 c2 = c1"

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
           then locals ((fun_of_dg_st \<circ> snd twice_ctx_sol) (Inl (v, ctx)))
                \<squnion> globs ((fun_of_dg_st \<circ> snd twice_ctx_sol) (Inr Global))
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
  "sigma_abs \<equiv> fun_of_dg_st \<circ> snd twice_ctx_sol"

abbreviation gen_abs :: "(pp \<times> ivl, gk, (ivl abs_state, ivl abs_state) dg_state) eqsT" where
  "gen_abs \<equiv> side_cfg_T_eff_cmp_seed_dg non_enter_predecessor_list (\<lambda>_. Global)
       (cmb_abs twice_cfg) (extra_abs twice_cfg) twice_cfg Sabs
       (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st) (fun_of_st (restrict_global_st cinit_ivl_st))"

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
  shows "fun_of_st cinit_ivl_st \<le> locals (sigma_abs (Inl (cfg_entry twice_cfg, bot)))"
proof -
  have "fun_of_st cinit_ivl_st \<le> locals (eq gen_abs (cfg_entry twice_cfg, bot) sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_cmp_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_abs (Inl (cfg_entry twice_cfg, bot)))"
    using pp_eq_bound[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma entry_covered: "(cfg_entry twice_cfg, bot) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def Spoly_def by eval

lemma cinit_le_cinit_ivl_st: "cinit_stores \<subseteq> \<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_ivl_st)

text \<open>
  \<^bold>\<open>Regression: the callee entry stays absent at the root context.\<close>  \<^const>\<open>cfg_entry\<close>
  of \<open>twice_cfg\<close> is node \<open>4\<close> (\<open>main\<close>'s entry) whose first statement is a call
  \<open>(4, EA_Enter [''p''] [N 3], 0)\<close>.  The polyvariant solver routes node \<open>0\<close> to the
  argument contexts \<open>[3,3]\<close> / \<open>[10,10]\<close> and leaves \<open>(0, bot)\<close> unpopulated ---
  \<open>p\<close> there is the bottom interval.  The corrected activation semantics
  (\<^theory>\<open>Voblint_CFG.CFG_Collect_Activation\<close>) routes the \<open>proc_entry\<close> seed at a call
  from the CFG entry to \<open>enterc seedc s\<close> (\<open>= [3,3]\<close>), \<^emph>\<open>not\<close> \<open>seedc = bot\<close>, so no
  obligation forces the callee under the root context.  These witnesses keep that
  invariant honest: \<open>(0, bot)\<close> remains at \<open>\<bottom>\<close> and is never required.\<close>

lemma callee_entry_bot_unpopulated:
  "lookup_st (locals (snd twice_ctx_sol (Inl (0, bot)))) ''p'' = \<bottom>"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def Spoly_def by eval

lemma main_first_stmt_is_call:
  "(cfg_entry twice_cfg, EA_Enter [''p''] [IMP2_Syntax.N 3], 0) \<in> edges twice_cfg"
  using twice_entry twice_edges by simp

subsection \<open>Solved-domain closure facts\<close>

text \<open>\<^bold>\<open>Forward closure along non-enter edges.\<close>  Every non-\<^const>\<open>EA_Enter\<close> successor of
  a solved node stays solved \<^emph>\<open>at the same context\<close>.  This is not a generic solver
  invariant --- it holds because every \<open>twice\<close> node reaches the exit, so the exit query's
  backward cone materialises the whole intra-context chain.  It is a decidable closed check
  over the finite solved domain and the finite edge set (\<^bold>\<open>all\<close> solved contexts, not the two
  observed by \<open>eval\<close>).\<close>
lemma twice_fwd_closed_all:
  "\<forall>(u, c)\<in>fst twice_ctx_sol. \<forall>(u', a, v)\<in>edges twice_cfg.
      u = u' \<and> \<not> is_enter_action a \<longrightarrow> (v, c) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval

lemma twice_fwd_closed:
  assumes "(u, ctx) \<in> fst twice_ctx_sol" and "(u, a, v) \<in> edges twice_cfg"
    and "\<not> is_enter_action a"
  shows "(v, ctx) \<in> fst twice_ctx_sol"
  using twice_fwd_closed_all assms by fastforce

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

text \<open>The routed interval solution is a \<^locale>\<open>dg_ctx_activation\<close> instance: the diagonal
  interval DG interpretation \<open>ivl_dg\<close> supplies \<^locale>\<open>sound_dg_spec\<close>, \<open>twice_ctx_pp_abs\<close> the
  post-solution, and the guarded reader / forward closure the remaining axioms.  \<open>EDGE\<close>
  and the combine transport are then read off as \<open>twice_dg.dg_ctx_act_edge\<close> /
  \<open>twice_dg.dg_ctx_act_comb_covered\<close> rather than re-proved by hand.\<close>

interpretation twice_dg: dg_ctx_activation Sabs twice_cfg Global
    "cmb_abs twice_cfg" "extra_abs twice_cfg"
    "fun_of_st (bot::ivl st)" "fun_of_st cinit_ivl_st" "fun_of_st (restrict_global_st cinit_ivl_st)"
    sigma_abs "fst twice_ctx_sol" "(cfg_exit twice_cfg, bot)" ivl_ctx_sg
proof
  show "finite (edges twice_cfg)" by (rule twice_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_cmp_seed_dg non_enter_predecessor_list (\<lambda>_. Global)
             (cmb_abs twice_cfg) (extra_abs twice_cfg) twice_cfg Sabs
             (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st)
             (fun_of_st (restrict_global_st cinit_ivl_st)))
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
  assume "(u, ctx) \<in> fst twice_ctx_sol" "(u, a, v) \<in> edges twice_cfg" "\<not> is_enter_action a"
  thus "(v, ctx) \<in> fst twice_ctx_sol" by (rule twice_fwd_closed)
qed

subsection \<open>Shared-global regression facts\<close>

text \<open>
  \<^bold>\<open>Regression: real globals are shared, not context-indexed.\<close>  The reader combines
  context-sensitive locals \<open>\<sigma> (Inl (v, ctx))\<close> with the \<^emph>\<open>single\<close> shared global slot
  \<open>\<sigma> (Inr Global)\<close> --- the same slot for every context (\<open>gkey = (\<lambda>_. Global)\<close>),
  matching Goblint's flow-insensitive globals.  The initial global value \<open>0\<close> is present
  at \<open>Global\<close> and is read identically under the main context and both callee contexts,
  so the entered store's preserved globals are covered without copying global state into
  any callee context.\<close>

lemma global_init_present:
  "lookup_st (globs (snd twice_ctx_sol (Inr Global))) ''Gx'' = Ivl (Fin 0) (Fin 0)"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval

lemma global_slot_shared:
  "ivl_ctx_sg (Inl (0, ctx_call1)) ''Gx'' = ivl_ctx_sg (Inl (0, ctx_call2)) ''Gx''"
proof -
  have "lookup_st (locals (snd twice_ctx_sol (Inl (0, ctx_call1)))) ''Gx''
      = lookup_st (locals (snd twice_ctx_sol (Inl (0, ctx_call2)))) ''Gx''"
    unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval
  thus ?thesis
    unfolding ivl_ctx_sg_def
    by (simp add: callee_covered_call1 callee_covered_call2)
qed

subsection \<open>SEED_G: the routed callee entry (enter edges)\<close>

text \<open>Enter callers are covered only under the main context (\<open>bot\<close>): \<open>twice\<close>'s two calls
  both originate from \<open>main\<close>, the root activation.  Bounded, decidable over the finite
  solved domain.\<close>
lemma enter_callers_only_bot:
  "\<forall>(p, ctx)\<in>fst twice_ctx_sol. (p = 4 \<or> p = 6) \<longrightarrow> ctx = bot"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval

text \<open>\<^bold>\<open>The two executable enter bounds.\<close>  At each call site (context \<open>bot\<close>) the executable
  interval enter transfer's combined output (Answer local state joined with the Side
  global publication) is below the routed callee-entry local slot joined with the shared
  global slot.  A single decidable \<open>\<le>\<close> on concrete \<^typ>\<open>ivl st\<close> values per call.\<close>
lemma enter_st_bound_call1:
  "snd (dg_spec_step Spoly (EA_Enter [''p''] [IMP2_Syntax.N 3])
          (locals (snd twice_ctx_sol (Inl (4, bot)))) (globs (snd twice_ctx_sol (Inr Global))))
   \<squnion> fst (dg_spec_step Spoly (EA_Enter [''p''] [IMP2_Syntax.N 3])
          (locals (snd twice_ctx_sol (Inl (4, bot)))) (globs (snd twice_ctx_sol (Inr Global))))
   \<le> locals (snd twice_ctx_sol (Inl (0, ctx_call1))) \<squnion> globs (snd twice_ctx_sol (Inr Global))"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call1_def Spoly_def by eval

lemma enter_st_bound_call2:
  "snd (dg_spec_step Spoly (EA_Enter [''p''] [IMP2_Syntax.N 10])
          (locals (snd twice_ctx_sol (Inl (6, bot)))) (globs (snd twice_ctx_sol (Inr Global))))
   \<squnion> fst (dg_spec_step Spoly (EA_Enter [''p''] [IMP2_Syntax.N 10])
          (locals (snd twice_ctx_sol (Inl (6, bot)))) (globs (snd twice_ctx_sol (Inr Global))))
   \<le> locals (snd twice_ctx_sol (Inl (0, ctx_call2))) \<squnion> globs (snd twice_ctx_sol (Inr Global))"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call2_def Spoly_def by eval

text \<open>\<^bold>\<open>The enter membership reduction.\<close>  Given the covered caller / callee slots and the
  executable enter bound, the entered store lies in the routed callee reader.  Structure:
  \<open>ivl_dg.step_sound\<close> on the enter action lands \<open>s'\<close> in the abstract enter result;
  \<open>ivl_Hstep\<close> rewrites that result as the \<^const>\<open>fun_of_st\<close> image of the executable step;
  \<open>fun_of_st\<close> monotonicity lifts the executable \<open>\<le>\<close> to \<open>\<gamma>\<close>-inclusion.\<close>
lemma enter_membership:
  assumes covU: "(u, bot) \<in> fst twice_ctx_sol"
    and covV: "(0, ctx') \<in> fst twice_ctx_sol"
    and s: "s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, bot))\<rbrakk>"
    and st: "edge_step (EA_Enter xs es) s = Some s'"
    and bound:
      "snd (dg_spec_step Spoly (EA_Enter xs es)
              (locals (snd twice_ctx_sol (Inl (u, bot)))) (globs (snd twice_ctx_sol (Inr Global))))
       \<squnion> fst (dg_spec_step Spoly (EA_Enter xs es)
              (locals (snd twice_ctx_sol (Inl (u, bot)))) (globs (snd twice_ctx_sol (Inr Global))))
       \<le> locals (snd twice_ctx_sol (Inl (0, ctx'))) \<squnion> globs (snd twice_ctx_sol (Inr Global))"
  shows "s' \<in> \<lbrakk>ivl_ctx_sg (Inl (0, ctx'))\<rbrakk>"
proof -
  let ?D = "locals (snd twice_ctx_sol (Inl (u, bot)))"
  let ?G = "globs (snd twice_ctx_sol (Inr Global))"
  let ?L = "locals (snd twice_ctx_sol (Inl (0, ctx')))"
  let ?d = "fun_of_st ?D" and ?g = "fun_of_st ?G"
  have sin: "s \<in> gamma_unit ?d ?g"
    using s covU by (simp add: ivl_ctx_sg_covered gamma_unit_def)
  have "{s} \<subseteq> gamma_unit ?d ?g" using sin by simp
  hence "edge_collect (EA_Enter xs es) {s} \<subseteq> edge_collect (EA_Enter xs es) (gamma_unit ?d ?g)"
    by (rule edge_collect_mono)
  moreover have "s' \<in> edge_collect (EA_Enter xs es) {s}" using st by (simp add: edge_collect_single)
  ultimately have "s' \<in> edge_collect (EA_Enter xs es) (gamma_unit ?d ?g)" by blast
  also have "\<dots> \<subseteq> (case dg_spec_step Sabs (EA_Enter xs es) ?d ?g of (g', d') \<Rightarrow> gamma_unit d' g')"
    by (rule ivl_dg.step_sound)
  finally have "s' \<in> gamma_unit (snd (dg_spec_step Sabs (EA_Enter xs es) ?d ?g))
                                 (fst (dg_spec_step Sabs (EA_Enter xs es) ?d ?g))"
    by (simp add: case_prod_beta)
  \<comment> \<open>rewrite the abstract enter result as the fun_of_st image of the executable step\<close>
  also have "\<dots> = \<lbrakk>fun_of_st (snd (dg_spec_step Spoly (EA_Enter xs es) ?D ?G)
                        \<squnion> fst (dg_spec_step Spoly (EA_Enter xs es) ?D ?G))\<rbrakk>"
  proof -
    have "dg_spec_step Sabs (EA_Enter xs es) ?d ?g
        = map_prod fun_of_st fun_of_st (dg_spec_step Spoly (EA_Enter xs es) ?D ?G)"
      unfolding Spoly_def by (rule ivl_Hstep[symmetric])
    thus ?thesis by (simp add: gamma_unit_def fun_of_st_sup)
  qed
  finally have "s' \<in> \<lbrakk>fun_of_st (snd (dg_spec_step Spoly (EA_Enter xs es) ?D ?G)
                          \<squnion> fst (dg_spec_step Spoly (EA_Enter xs es) ?D ?G))\<rbrakk>" .
  also have "\<dots> \<subseteq> \<lbrakk>fun_of_st (?L \<squnion> ?G)\<rbrakk>"
    by (rule gamma_state_mono[OF fun_of_st_mono[OF bound]])
  also have "\<dots> = \<lbrakk>ivl_ctx_sg (Inl (0, ctx'))\<rbrakk>"
    using covV by (simp add: ivl_ctx_sg_covered)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>enter_route_exact.\<close>  The context a call routes into is the point abstraction of the
  entered formal \<open>p\<close>: for the two constant-argument calls the entered value is \<open>3\<close> / \<open>10\<close>,
  so the routed context is exactly \<open>ctx_call1\<close> / \<open>ctx_call2\<close> --- the executable route agrees
  with the activation route \<^const>\<open>ivl_enterc\<close>.\<close>
lemma enter_route_exact_call1:
  assumes "edge_step (EA_Enter [''p''] [IMP2_Syntax.N 3]) s = Some s'"
  shows "ivl_enterc ctx s' = ctx_call1"
proof -
  from assms have "s' = (enter_state s)(''p'' := 3)" by (simp add: bind_formals_def)
  thus ?thesis by (simp add: ivl_enterc_def ivl_decode_def ctx_call1_val)
qed

lemma enter_route_exact_call2:
  assumes "edge_step (EA_Enter [''p''] [IMP2_Syntax.N 10]) s = Some s'"
  shows "ivl_enterc ctx s' = ctx_call2"
proof -
  from assms have "s' = (enter_state s)(''p'' := 10)" by (simp add: bind_formals_def)
  thus ?thesis by (simp add: ivl_enterc_def ivl_decode_def ctx_call2_val)
qed

text \<open>\<^bold>\<open>SEED_G.\<close>  An \<^const>\<open>EA_Enter\<close> edge lands the entering store in the routed callee-entry
  reader.  Uncovered caller \<Rightarrow> empty premise; covered caller \<Rightarrow> the call originates from
  \<open>main\<close> (context \<open>bot\<close>), the routed context is \<open>ctx_call1\<close> / \<open>ctx_call2\<close>
  (\<open>enter_route_exact\<close>), and \<open>enter_membership\<close> discharges each from the executable enter
  bound.\<close>
lemma ivl_ctx_sg_seed:
  assumes e: "(u, EA_Enter xs es, v) \<in> edges twice_cfg"
    and s: "s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, ctx))\<rbrakk>"
    and st: "edge_step (EA_Enter xs es) s = Some s'"
  shows "s' \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ivl_enterc ctx s'))\<rbrakk>"
proof (cases "(u, ctx) \<in> fst twice_ctx_sol")
  case False
  hence "\<lbrakk>ivl_ctx_sg (Inl (u, ctx))\<rbrakk> = {}" by (rule ivl_ctx_sg_uncovered_empty)
  thus ?thesis using s by simp
next
  case True
  from e consider
      (c1) "u = 4" "xs = [''p'']" "es = [IMP2_Syntax.N 3]" "v = 0"
    | (c2) "u = 6" "xs = [''p'']" "es = [IMP2_Syntax.N 10]" "v = 0"
    unfolding twice_edges by auto
  thus ?thesis
  proof cases
    case c1
    have ctxb: "ctx = bot" using True enter_callers_only_bot c1 by fastforce
    have covU: "(4, bot) \<in> fst twice_ctx_sol" using True c1 ctxb by simp
    have "s' \<in> \<lbrakk>ivl_ctx_sg (Inl (0, ctx_call1))\<rbrakk>"
      by (rule enter_membership[OF covU callee_covered_call1 _ _ enter_st_bound_call1])
         (use s st c1 ctxb in simp_all)
    thus ?thesis using st c1 by (simp add: enter_route_exact_call1)
  next
    case c2
    have ctxb: "ctx = bot" using True enter_callers_only_bot c2 by fastforce
    have covU: "(6, bot) \<in> fst twice_ctx_sol" using True c2 ctxb by simp
    have "s' \<in> \<lbrakk>ivl_ctx_sg (Inl (0, ctx_call2))\<rbrakk>"
      by (rule enter_membership[OF covU callee_covered_call2 _ _ enter_st_bound_call2])
         (use s st c2 ctxb in simp_all)
    thus ?thesis using st c2 by (simp add: enter_route_exact_call2)
  qed
qed

subsection \<open>COMB: the routed return combine\<close>

text \<open>\<^bold>\<open>The combine membership reduction.\<close>  The return combine of a covered caller with the
  \<^emph>\<open>routed\<close> callee exit lands in the resumed caller reader --- the combine analogue of
  \<open>enter_membership\<close>.  \<open>ivl_dg.combine_sound\<close> lands the result in the abstract combine;
  \<open>ivl_Hcomb\<close> rewrites it as the \<^const>\<open>fun_of_st\<close> image of the executable combine; the
  executable \<open>\<le>\<close> lifts through \<open>fun_of_st\<close> monotonicity.  Both caller and callee exit read
  the \<^emph>\<open>same\<close> shared global slot, so \<open>combine_sound\<close> applies at one \<open>g\<close>.\<close>
lemma combine_membership:
  assumes covCl: "(cl, bot) \<in> fst twice_ctx_sol"
    and covEx: "(ex, cc) \<in> fst twice_ctx_sol"
    and covV: "(v, bot) \<in> fst twice_ctx_sol"
    and s: "s \<in> \<lbrakk>ivl_ctx_sg (Inl (cl, bot))\<rbrakk>"
    and t: "t \<in> \<lbrakk>ivl_ctx_sg (Inl (ex, cc))\<rbrakk>"
    and bound:
      "snd (dgs_combine Spoly dst
              (locals (snd twice_ctx_sol (Inl (cl, bot))))
              (locals (snd twice_ctx_sol (Inl (ex, cc))))
              (globs (snd twice_ctx_sol (Inr Global))))
       \<squnion> fst (dgs_combine Spoly dst
              (locals (snd twice_ctx_sol (Inl (cl, bot))))
              (locals (snd twice_ctx_sol (Inl (ex, cc))))
              (globs (snd twice_ctx_sol (Inr Global))))
       \<le> locals (snd twice_ctx_sol (Inl (v, bot))) \<squnion> globs (snd twice_ctx_sol (Inr Global))"
  shows "combine_collect dst s t \<in> \<lbrakk>ivl_ctx_sg (Inl (v, bot))\<rbrakk>"
proof -
  let ?Dc = "locals (snd twice_ctx_sol (Inl (cl, bot)))"
  let ?De = "locals (snd twice_ctx_sol (Inl (ex, cc)))"
  let ?G = "globs (snd twice_ctx_sol (Inr Global))"
  have comm: "dgs_combine Sabs dst (fun_of_st ?Dc) (fun_of_st ?De) (fun_of_st ?G)
      = map_prod fun_of_st fun_of_st (dgs_combine Spoly dst ?Dc ?De ?G)"
    unfolding Spoly_def by (rule ivl_Hcomb[symmetric])
  \<comment> \<open>The only interval-specific step: bridge the executable \<open>Spoly\<close> combine bound to the
     abstract \<open>Sabs\<close> bound the generic transport reads.\<close>
  have bound_abs:
    "snd (dgs_combine Sabs dst (locals (sigma_abs (Inl (cl, bot))))
            (locals (sigma_abs (Inl (ex, cc)))) (globs (sigma_abs (Inr Global))))
     \<squnion> fst (dgs_combine Sabs dst (locals (sigma_abs (Inl (cl, bot))))
            (locals (sigma_abs (Inl (ex, cc)))) (globs (sigma_abs (Inr Global))))
     \<le> locals (sigma_abs (Inl (v, bot))) \<squnion> globs (sigma_abs (Inr Global))"
  proof -
    have "snd (dgs_combine Sabs dst (locals (sigma_abs (Inl (cl, bot))))
              (locals (sigma_abs (Inl (ex, cc)))) (globs (sigma_abs (Inr Global))))
         \<squnion> fst (dgs_combine Sabs dst (locals (sigma_abs (Inl (cl, bot))))
              (locals (sigma_abs (Inl (ex, cc)))) (globs (sigma_abs (Inr Global))))
       = fun_of_st (snd (dgs_combine Spoly dst ?Dc ?De ?G)
                    \<squnion> fst (dgs_combine Spoly dst ?Dc ?De ?G))"
      by (simp add: comm fun_of_st_sup)
    also have "\<dots> \<le> fun_of_st (locals (snd twice_ctx_sol (Inl (v, bot))) \<squnion> ?G)"
      by (rule fun_of_st_mono[OF bound])
    also have "\<dots> = locals (sigma_abs (Inl (v, bot))) \<squnion> globs (sigma_abs (Inr Global))"
      by (simp add: fun_of_st_sup)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule twice_dg.dg_ctx_act_comb_covered[OF covCl covEx covV s t bound_abs])
qed

text \<open>\<^bold>\<open>The two executable combine bounds\<close> (context \<open>bot\<close> caller, routed callee exit),
  and the return-node coverage.\<close>
lemma combine_st_bound_call1:
  "snd (dgs_combine Spoly (Some ''x'')
          (locals (snd twice_ctx_sol (Inl (4, bot))))
          (locals (snd twice_ctx_sol (Inl (3, ctx_call1))))
          (globs (snd twice_ctx_sol (Inr Global))))
   \<squnion> fst (dgs_combine Spoly (Some ''x'')
          (locals (snd twice_ctx_sol (Inl (4, bot))))
          (locals (snd twice_ctx_sol (Inl (3, ctx_call1))))
          (globs (snd twice_ctx_sol (Inr Global))))
   \<le> locals (snd twice_ctx_sol (Inl (5, bot))) \<squnion> globs (snd twice_ctx_sol (Inr Global))"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call1_def Spoly_def by eval

lemma combine_st_bound_call2:
  "snd (dgs_combine Spoly (Some ''y'')
          (locals (snd twice_ctx_sol (Inl (6, bot))))
          (locals (snd twice_ctx_sol (Inl (3, ctx_call2))))
          (globs (snd twice_ctx_sol (Inr Global))))
   \<squnion> fst (dgs_combine Spoly (Some ''y'')
          (locals (snd twice_ctx_sol (Inl (6, bot))))
          (locals (snd twice_ctx_sol (Inl (3, ctx_call2))))
          (globs (snd twice_ctx_sol (Inr Global))))
   \<le> locals (snd twice_ctx_sol (Inl (7, bot))) \<squnion> globs (snd twice_ctx_sol (Inr Global))"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call2_def Spoly_def by eval

lemma covered_ret5: "(5, bot) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval
lemma covered_ret7: "(7, bot) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def by eval
lemma callee_exit_covered_call1: "(3, ctx_call1) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call1_def by eval
lemma callee_exit_covered_call2: "(3, ctx_call2) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_ctx_eqs_def ctx_call2_def by eval

text \<open>\<^bold>\<open>enter_route_exact for combine.\<close>  The callee context resumed at a return is the point
  abstraction of the entered formal linked to the caller by \<^const>\<open>call_enter_store\<close>.  The
  linked entered store is exactly the enter edge's \<^const>\<open>edge_step\<close> result, so this reuses
  \<open>enter_route_exact\<close>.\<close>
lemma comb_route_call1:
  assumes "call_enter_store twice_cfg 4 s es"
  shows "ivl_enterc c1 es = ctx_call1"
proof -
  have "edge_step (EA_Enter [''p''] [IMP2_Syntax.N 3]) s = Some es"
    using assms unfolding call_enter_store_def by (auto simp: twice_edges)
  thus ?thesis by (rule enter_route_exact_call1)
qed

lemma comb_route_call2:
  assumes "call_enter_store twice_cfg 6 s es"
  shows "ivl_enterc c1 es = ctx_call2"
proof -
  have "edge_step (EA_Enter [''p''] [IMP2_Syntax.N 10]) s = Some es"
    using assms unfolding call_enter_store_def by (auto simp: twice_edges)
  thus ?thesis by (rule enter_route_exact_call2)
qed

text \<open>\<^bold>\<open>COMB.\<close>  A return combine soundly resumes the caller reader.  Uncovered caller \<Rightarrow>
  empty premise; covered caller \<Rightarrow> the call site is \<open>main\<close> (context \<open>bot\<close>), the callee
  exit context is the routed \<open>ctx_call1\<close> / \<open>ctx_call2\<close> (\<open>comb_route\<close>, forced by
  \<^const>\<open>call_enter_store\<close>), and \<open>combine_membership\<close> discharges each from the executable
  combine bound.  The impossible pairing (return of call 1 with the callee at
  \<open>ctx_call2\<close>) is not a real activation return and is no longer a required case.\<close>
lemma ivl_ctx_sg_comb:
  assumes c: "(cl, ex, v, dst) \<in> combines twice_cfg"
    and s: "s \<in> \<lbrakk>ivl_ctx_sg (Inl (cl, c1))\<rbrakk>"
    and t: "t \<in> \<lbrakk>ivl_ctx_sg (Inl (ex, ivl_enterc c1 es))\<rbrakk>"
    and ces: "call_enter_store twice_cfg cl s es"
  shows "combine_collect dst s t \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ivl_combc c1 (ivl_enterc c1 es)))\<rbrakk>"
proof (cases "(cl, c1) \<in> fst twice_ctx_sol")
  case False
  hence "\<lbrakk>ivl_ctx_sg (Inl (cl, c1))\<rbrakk> = {}" by (rule ivl_ctx_sg_uncovered_empty)
  thus ?thesis using s by simp
next
  case True
  from c consider (c1) "cl = 4" "ex = 3" "v = 5" "dst = Some ''x''"
                | (c2) "cl = 6" "ex = 3" "v = 7" "dst = Some ''y''"
    unfolding twice_combines by auto
  thus ?thesis
  proof cases
    case c1
    have ctxb: "c1 = bot" using True enter_callers_only_bot c1 by fastforce
    have route: "ivl_enterc c1 es = ctx_call1" using ces c1 by (simp add: comb_route_call1)
    have covCl: "(4, bot) \<in> fst twice_ctx_sol" using True c1 ctxb by simp
    have "combine_collect (Some ''x'') s t \<in> \<lbrakk>ivl_ctx_sg (Inl (5, bot))\<rbrakk>"
      by (rule combine_membership[OF covCl callee_exit_covered_call1 covered_ret5 _ _ combine_st_bound_call1])
         (use s t c1 ctxb route in simp_all)
    thus ?thesis using c1 ctxb route by (simp add: ivl_combc_def)
  next
    case c2
    have ctxb: "c1 = bot" using True enter_callers_only_bot c2 by fastforce
    have route: "ivl_enterc c1 es = ctx_call2" using ces c2 by (simp add: comb_route_call2)
    have covCl: "(6, bot) \<in> fst twice_ctx_sol" using True c2 ctxb by simp
    have "combine_collect (Some ''y'') s t \<in> \<lbrakk>ivl_ctx_sg (Inl (7, bot))\<rbrakk>"
      by (rule combine_membership[OF covCl callee_exit_covered_call2 covered_ret7 _ _ combine_st_bound_call2])
         (use s t c2 ctxb route in simp_all)
    thus ?thesis using c2 ctxb route by (simp add: ivl_combc_def)
  qed
qed

subsection \<open>Activation-indexed collecting soundness (obligation scaffold)\<close>

text \<open>Instantiating the generic \<open>activation_collect_sound\<close> at the routed interval
  solution.  Five semantic obligations remain, each a separate milestone; they are
  discharged from \<open>twice_ctx_pp_abs\<close> together with the interval \<^locale>\<open>sound_dg_spec\<close>
  step / combine soundness, route consistency, and the \<^locale>\<open>point_digest\<close> seed.\<close>

theorem twice_ctx_collect_ctx_act_sound:
  "cfg_collect_ctx_act ivl_enterc ivl_combc bot twice_cfg cinit_stores v ctx
     \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = ivl_ctx_sg and enterc = ivl_enterc
        and combc = ivl_combc and seedc = bot and S = cinit_stores and g = twice_cfg])
  \<comment> \<open>ENTRY_G --- mirrors \<open>twice_sound0\<close>: cinit stores lie in the seeded entry slot.\<close>
  fix s assume "s \<in> cinit_stores"
  hence "s \<in> \<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>" using cinit_le_cinit_ivl_st by blast
  also have "\<lbrakk>fun_of_st cinit_ivl_st\<rbrakk> \<subseteq> \<lbrakk>locals (sigma_abs (Inl (cfg_entry twice_cfg, bot)))\<rbrakk>"
    by (rule gamma_state_mono[OF entry_locals_ge_s0d[OF entry_covered]])
  also have "\<dots> \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (cfg_entry twice_cfg, bot))\<rbrakk>"
    unfolding ivl_ctx_sg_covered[OF entry_covered] by (rule gamma_state_sup_ub1)
  finally show "s \<in> \<lbrakk>ivl_ctx_sg (Inl (cfg_entry twice_cfg, bot))\<rbrakk>" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> edges twice_cfg \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg (Inl (v, c))\<rbrakk>"
    by (rule twice_dg.dg_ctx_act_edge)
next
  \<comment> \<open>SEED_G --- enter routed to \<open>ivl_decode (s' ''p'')\<close>: point_digest + route consistency + seed pub.\<close>
  show "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ivl_enterc c s'))\<rbrakk>"
    by (rule ivl_ctx_sg_seed)
next
  \<comment> \<open>COMB --- return combine: combine_sound + the cmb bound from pp.\<close>
  show "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>ivl_ctx_sg (Inl (ex, ivl_enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store twice_cfg cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ivl_combc c1 (ivl_enterc c1 es)))\<rbrakk>"
    by (rule ivl_ctx_sg_comb)
qed

end
