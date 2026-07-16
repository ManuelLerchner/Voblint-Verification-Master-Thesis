theory Example_Interval_DG_Ctx_Collect
  imports
    Example_Interval_DG_Ctx_Sound
    "Voblint_Analysis.Interval_Point_Digest"
    "Voblint_Analysis.Seeded_Activation_Sound"
begin

section \<open>Activation-indexed collecting soundness for the routed interval solution\<close>

text \<open>
  WORK IN PROGRESS (not in any \<^verbatim>\<open>ROOT\<close>): the connecting theorem between the
  routed executable post-solution (\<open>twice_ctx_pp_abs\<close>) and the semantic
  activation-indexed collecting semantics.  It instantiates the generic
  \<open>activation_collect_sound\<close> and leaves its five obligations as separate milestones,
  each still \<^theory_text>\<open>sorry\<close>.  This theory is excluded from the batch build until the
  obligations are discharged.
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
                \<squnion> globs ((fun_of_dg_st \<circ> snd twice_ctx_sol) (Inr (GlobAt ctx)))
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
  "gen_abs \<equiv> side_cfg_T_eff_cmp_seed_dg non_enter_predecessor_list GlobAt
       (cmb_abs twice_cfg) (extra_abs twice_cfg) twice_cfg Sabs
       (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st) (fun_of_st (restrict_global_st cinit_ivl_st))"

lemma pp_eq_bound:
  "(v, ctx) \<in> fst twice_ctx_sol
     \<Longrightarrow> eq gen_abs (v, ctx) sigma_abs \<le> sigma_abs (Inl (v, ctx))"
  using twice_ctx_pp_abs by simp

lemma pp_sides_bound:
  "(v, ctx) \<in> fst twice_ctx_sol
     \<Longrightarrow> sides_of_rhs (gen_abs (v, ctx)) sigma_abs \<le> sigma_abs"
  using twice_ctx_pp_abs by simp

text \<open>The two faces of the guarded reader: on the solved domain it is the transported
  local slot joined with its real-global slot; off it, \<open>\<bottom>\<close> (empty concretization).\<close>

lemma ivl_ctx_sg_covered:
  "(v, ctx) \<in> fst twice_ctx_sol
   \<Longrightarrow> ivl_ctx_sg (Inl (v, ctx))
       = locals (sigma_abs (Inl (v, ctx))) \<squnion> globs (sigma_abs (Inr (GlobAt ctx)))"
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

subsection \<open>The routed intra edge bound (EDGE, covered branch)\<close>

text \<open>The routed intra edge tree denotes the interval \<^const>\<open>dg_spec_step\<close> read at the
  context-copied local slot \<open>(u, c)\<close> and the real-global slot \<open>GlobAt c\<close> --- the routed
  analogue of \<open>dg_edge_tree_local\<close> / \<open>dg_edge_tree_global\<close>.\<close>

lemma edge_tree_local_ctx:
  "locals (traverse_rhs
       (map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u))) sigma_abs)
   = snd (dg_spec_step Sabs a (locals (sigma_abs (Inl (u, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx)))))"
  unfolding apply_dg_spec_def
  by (subst traverse_intra_cmp) (simp add: traverse_dg_edge_tree)

lemma edge_tree_global_ctx:
  "globs (sides_of_rhs
       (map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u)))
       sigma_abs (Inr (GlobAt ctx)))
   = fst (dg_spec_step Sabs a (locals (sigma_abs (Inl (u, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx)))))"
proof -
  have step1:
    "sides_of_rhs (map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u)))
       sigma_abs (Inr (GlobAt ctx))
     = sides_of_rhs (apply_dg_spec Sabs a u)
         (\<lambda>z. sigma_abs (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. GlobAt ctx) z)) (Inr ())"
  proof -
    have "sides_of_rhs (map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u)))
            sigma_abs (Inr ((\<lambda>_. GlobAt ctx) ()))
        = sides_of_rhs (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u))
            (\<lambda>z. sigma_abs (map_sum id (\<lambda>_. GlobAt ctx) z)) (Inr ())"
      by (rule sides_map_gtree_unit)
    thus ?thesis by (simp add: sides_map_ltree_Inr sum.map_comp o_def)
  qed
  have "globs (sides_of_rhs (map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u)))
          sigma_abs (Inr (GlobAt ctx)))
      = globs (sides_of_rhs (apply_dg_spec Sabs a u)
          (\<lambda>z. sigma_abs (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. GlobAt ctx) z)) (Inr ()))"
    by (rule arg_cong[OF step1])
  also have "\<dots> = fst (dg_spec_step Sabs a (locals (sigma_abs (Inl (u, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx)))))"
    unfolding apply_dg_spec_def by (simp add: sides_dg_edge_tree_Inr)
  finally show ?thesis .
qed

text \<open>Abbreviations for the accumulator and summand list of \<open>gen_abs (v, ctx)\<close>.\<close>

abbreviation gen_acc0 :: "pp \<Rightarrow> ivl abs_state" where
  "gen_acc0 v \<equiv> (if v = cfg_entry twice_cfg
                 then fun_of_st (bot::ivl st) \<squnion> fun_of_st cinit_ivl_st
                 else fun_of_st (bot::ivl st))"

abbreviation gen_trees :: "pp \<Rightarrow> ivl \<Rightarrow> (pp \<times> ivl, gk, (ivl abs_state, ivl abs_state) dg_state) strategy_tree list" where
  "gen_trees v ctx \<equiv>
     map (\<lambda>(u, a). map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u)))
         (non_enter_predecessor_list twice_cfg v)
     @ map (\<lambda>(cc, ex, dst). cmb_abs twice_cfg ctx dst cc ex) (combine_predecessor_list twice_cfg v)
     @ extra_abs twice_cfg ctx v"

text \<open>The entry \<^const>\<open>Side\<close> wrapper only adds to the side effects, so the raw fold's sides
  are below \<open>gen_abs (v, ctx)\<close>'s at every key.\<close>
lemma sides_fold_le_gen_abs:
  "sides_of_rhs (side_rhs_fold_dg (gen_acc0 v) (gen_trees v ctx)) sigma_abs k
   \<le> sides_of_rhs (gen_abs (v, ctx)) sigma_abs k"
  unfolding side_cfg_T_eff_cmp_seed_dg_def Let_def
  by (cases "v = cfg_entry twice_cfg") (auto simp: Let_def intro: sup.cobounded1)

text \<open>\<^bold>\<open>edgeD.\<close>  The interval step's Answer at a covered non-enter edge is below the
  successor local slot --- read through \<open>edge_tree_local_ctx\<close> and \<open>pp_eq_bound\<close>.\<close>
lemma edge_bound_local:
  assumes cov_v: "(v, ctx) \<in> fst twice_ctx_sol"
    and e: "(u, a, v) \<in> edges twice_cfg" and ne: "\<not> is_enter_action a"
  shows "snd (dg_spec_step Sabs a (locals (sigma_abs (Inl (u, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx)))))
           \<le> locals (sigma_abs (Inl (v, ctx)))"
proof -
  let ?t = "map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u))"
  have pred: "(u, a) \<in> set (non_enter_predecessor_list twice_cfg v)"
    using e ne by (simp add: non_enter_predecessor_list_mem set_predecessor_list[OF twice_finE] predecessors_def)
  hence mem: "?t \<in> set (gen_trees v ctx)" by (force intro: rev_image_eqI)
  have "snd (dg_spec_step Sabs a (locals (sigma_abs (Inl (u, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx)))))
      = locals (traverse_rhs ?t sigma_abs)"
    by (simp add: edge_tree_local_ctx)
  also have "\<dots> \<le> side_acc_dg (gen_acc0 v) sigma_abs (gen_trees v ctx)"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq gen_abs (v, ctx) sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_cmp_seed_dg)
  also have "\<dots> \<le> locals (sigma_abs (Inl (v, ctx)))"
    using pp_eq_bound[OF cov_v] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>edgeG.\<close>  The interval step's Side at a covered non-enter edge is below the context's
  real-global slot --- read through \<open>edge_tree_global_ctx\<close>, \<open>sides_fold_le_gen_abs\<close>, and
  \<open>pp_sides_bound\<close>.\<close>
lemma edge_bound_global:
  assumes cov_v: "(v, ctx) \<in> fst twice_ctx_sol"
    and e: "(u, a, v) \<in> edges twice_cfg" and ne: "\<not> is_enter_action a"
  shows "fst (dg_spec_step Sabs a (locals (sigma_abs (Inl (u, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx)))))
           \<le> globs (sigma_abs (Inr (GlobAt ctx)))"
proof -
  let ?t = "map_gtree (\<lambda>_. GlobAt ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec Sabs a u))"
  have pred: "(u, a) \<in> set (non_enter_predecessor_list twice_cfg v)"
    using e ne by (simp add: non_enter_predecessor_list_mem set_predecessor_list[OF twice_finE] predecessors_def)
  hence mem: "?t \<in> set (gen_trees v ctx)" by (force intro: rev_image_eqI)
  have "fst (dg_spec_step Sabs a (locals (sigma_abs (Inl (u, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx)))))
      = globs (sides_of_rhs ?t sigma_abs (Inr (GlobAt ctx)))"
    by (simp add: edge_tree_global_ctx)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (gen_acc0 v) (gen_trees v ctx)) sigma_abs (Inr (GlobAt ctx)))"
    using sides_le_side_rhs_fold_dg[OF mem, where k = "Inr (GlobAt ctx)"]
    by (simp add: less_eq_dg_state_def)
  also have "\<dots> \<le> globs (sides_of_rhs (gen_abs (v, ctx)) sigma_abs (Inr (GlobAt ctx)))"
    using sides_fold_le_gen_abs[where k = "Inr (GlobAt ctx)"]
    by (simp add: less_eq_dg_state_def)
  also have "\<dots> \<le> globs (sigma_abs (Inr (GlobAt ctx)))"
    using pp_sides_bound[OF cov_v, THEN le_funD, of "Inr (GlobAt ctx)"]
    by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>EDGE.\<close>  A non-enter edge preserves the context and soundly transfers the
  guarded reader.  If the source is uncovered its abstraction is empty (vacuous); if it
  is covered, forward closure (\<open>twice_fwd_closed\<close>) covers the target, and the interval
  \<^const>\<open>dg_spec_step\<close> soundness (\<open>ivl_dg.step_sound\<close>) transports through the routed edge
  bounds \<open>edge_bound_local\<close> / \<open>edge_bound_global\<close>.\<close>
lemma ivl_ctx_sg_edge:
  assumes e: "(u, a, v) \<in> edges twice_cfg" and ne: "\<not> is_enter_action a"
    and sin: "s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, ctx))\<rbrakk>" and st: "edge_step a s = Some s'"
  shows "s' \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
proof (cases "(u, ctx) \<in> fst twice_ctx_sol")
  case False
  hence "\<lbrakk>ivl_ctx_sg (Inl (u, ctx))\<rbrakk> = {}" by (rule ivl_ctx_sg_uncovered_empty)
  thus ?thesis using sin by simp
next
  case True
  hence cov_v: "(v, ctx) \<in> fst twice_ctx_sol" using e ne by (rule twice_fwd_closed)
  let ?d = "locals (sigma_abs (Inl (u, ctx)))"
  let ?g = "globs (sigma_abs (Inr (GlobAt ctx)))"
  have sin': "s \<in> gamma_unit ?d ?g"
    using sin True by (simp add: ivl_ctx_sg_covered gamma_unit_def)
  have "{s} \<subseteq> gamma_unit ?d ?g" using sin' by simp
  hence "edge_collect a {s} \<subseteq> edge_collect a (gamma_unit ?d ?g)" by (rule edge_collect_mono)
  moreover have "s' \<in> edge_collect a {s}" using st by (simp add: edge_collect_single)
  ultimately have "s' \<in> edge_collect a (gamma_unit ?d ?g)" by blast
  also have "\<dots> \<subseteq> (case dg_spec_step Sabs a ?d ?g of (g', d') \<Rightarrow> gamma_unit d' g')"
    by (rule ivl_dg.step_sound)
  finally have "s' \<in> (case dg_spec_step Sabs a ?d ?g of (g', d') \<Rightarrow> gamma_unit d' g')" .
  hence "s' \<in> gamma_unit (snd (dg_spec_step Sabs a ?d ?g)) (fst (dg_spec_step Sabs a ?d ?g))"
    by (simp add: case_prod_beta)
  also have "\<dots> \<subseteq> gamma_unit (locals (sigma_abs (Inl (v, ctx)))) (globs (sigma_abs (Inr (GlobAt ctx))))"
    by (rule gamma_unit_mono[OF edge_bound_local[OF cov_v e ne] edge_bound_global[OF cov_v e ne]])
  also have "\<dots> = \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
    using cov_v by (simp add: ivl_ctx_sg_covered gamma_unit_def)
  finally show ?thesis .
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
  \<comment> \<open>EDGE --- non-enter, context preserved: step_sound + the intra D/G bound from pp.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> edges twice_cfg \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg (Inl (v, c))\<rbrakk>"
    by (rule ivl_ctx_sg_edge)
next
  \<comment> \<open>SEED_G --- enter routed to \<open>ivl_decode (s' ''p'')\<close>: point_digest + route consistency + seed pub.\<close>
  show "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ivl_enterc c s'))\<rbrakk>"
    sorry
next
  \<comment> \<open>COMB --- return combine: combine_sound + the cmb bound from pp.\<close>
  show "\<And>cl ex v dst c1 c2 s t. (cl, ex, v, dst) \<in> combines twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>ivl_ctx_sg (Inl (ex, c2))\<rbrakk>
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ivl_combc c1 c2))\<rbrakk>"
    sorry
qed

end
