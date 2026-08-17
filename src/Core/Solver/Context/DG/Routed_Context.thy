theory Routed_Context
  imports DG_Ctx_Activation Strategy_Tree_Combinators DG_Transfer_Combinators
    Strategy_Tree_Do "Voblint_CFG.CFG_Local_Trace"
begin

section \<open>One route, CALL and COMB discharged once\<close>

text \<open>
  \<^locale>\<open>dg_ctx_activation\<close> already discharges EDGE (\<open>dg_ctx_act_edge\<close>) generically off the
  post-solution, independent of \<open>route\<close>/\<open>cmb\<close>/\<open>extra\<close>: intra edges never route. Its COMB
  analogue (\<open>dg_ctx_act_comb_covered\<close>) is generic in the same sense but still takes the
  tree's contribution as an assumption (\<open>bound\<close>) rather than deriving it, because \<open>cmb\<close> is
  an unconstrained parameter: a context-sensitive analysis whose entry-seed publication and
  return combine are hand-written has to rederive that same routing argument itself. This
  theory fixes \<open>cmb\<close> and \<open>extra\<close> to one canonical shape, parametric only in a routing
  function \<open>route\<close> and a seed-key injection \<open>seed_key\<close>, and discharges CALL and COMB as
  theorems of that shape: a k-call-string or a partial-tabulation context becomes an
  interpretation of this locale, not a second proof development.
\<close>

subsection \<open>The canonical routed entry-seed publication and return combine\<close>

text \<open>The routing combine: read the caller under its own context, the callee exit under the
  context \<open>route\<close> selects from the caller's local value and the exact matched
  \<^typ>\<open>call_action\<close> (from \<^const>\<open>return_call_action_list\<close>, never re-derived from the call
  site's outgoing edges), and the one shared global slot \<open>gk0\<close>.\<close>
text \<open>Parameter order matches \<^locale>\<open>dg_ctx_activation\<close>'s \<open>cmb\<close> calling convention: the
  generator supplies \<open>route\<close> as \<open>cmb\<close>'s own first argument (\<open>cmb route c ca cc ex\<close> in
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>), so \<open>routed_cmb S gk0 seed_key\<close>, closing over the
  spec, the shared slot, and the seed-key injection, is the value that instantiates \<open>cmb\<close>.

  This tree owns the whole call lifecycle for one call action: it reads the caller once,
  routes the callee context once (\<open>ctx'\<close>), and shares that one \<open>ctx'\<close> between the entry-seed
  publication (formerly \<open>routed_extra\<close>'s job, at the call site's own equation) and the
  combine's callee-exit read (this equation's original job). Moving the seed publish here
  means \<open>routed_extra\<close> no longer needs to be invoked from the call site's own
  equation to activate the callee; the callee is activated as a side effect of whichever
  equation combines its result, discharging \<open>enter#\<close> exactly once per call action instead
  of once per hook.\<close>
definition routed_cmb ::
  "('d::bounded_semilattice_sup_bot, 'd) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'd) dg_state) strategy_tree"
where
  "routed_cmb S gk0 seed_key route ctx ca cc ex =
     with_call ca (\<lambda>dst fs as. do {
       caller_state \<leftarrow> read_local (cc, ctx);
       globals_state1 \<leftarrow> read_global gk0;
       let caller = locals caller_state;
       let globals1 = globs globals_state1;
       let ctx' = route cc ctx caller ca;
       let eg = enter_global S fs as caller globals1;
       publish_seed (seed_key (FunctionEntry (result_proc ex)) ctx')
         (enter_local S fs as caller globals1);
       callee_state \<leftarrow> read_local (ex, ctx');
       globals_state2 \<leftarrow> read_global gk0;
       let callee = locals callee_state;
       let globals2 = globs globals_state2;
       let cg = combine_global S dst caller callee globals2;
       publish_global gk0 (eg \<squnion> cg);
       answer_local (combine_local S dst caller callee globals2)
     })"

text \<open>
  Side-free analogue of \<open>routed_cmb\<close>, for folding several \<open>comb\<close>/\<open>intra\<close> contributions
  into one buffered generator equation (issue #121, keyed): instead of publishing \<open>gk0\<close>
  itself, it answers the unsplit \<open>(eg \<squnion> cg, combine_local ...)\<close> pair, matching
  \<^const>\<open>dg_edge_contribution_tree\<close>'s shape. A caller folds several such trees with
  \<^const>\<open>fold_rhs_trees\<close> and publishes \<open>gk0\<close> once, after every contribution has been
  read. The seed publication is unaffected: each call action's \<open>seed_key\<close> is distinct
  from every other call action's, so it never collides within one fold and stays a
  \<open>Side\<close> here exactly as in \<open>routed_cmb\<close>.
\<close>
definition routed_cmb_contribution ::
  "('d::bounded_semilattice_sup_bot, 'd) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'd) dg_state) strategy_tree"
where
  "routed_cmb_contribution S gk0 seed_key route ctx ca cc ex =
     with_call ca (\<lambda>dst fs as. do {
       caller_state \<leftarrow> read_local (cc, ctx);
       globals_state1 \<leftarrow> read_global gk0;
       let caller = locals caller_state;
       let globals1 = globs globals_state1;
       let ctx' = route cc ctx caller ca;
       let eg = enter_global S fs as caller globals1;
       publish_seed (seed_key (FunctionEntry (result_proc ex)) ctx')
         (enter_local S fs as caller globals1);
       callee_state \<leftarrow> read_local (ex, ctx');
       globals_state2 \<leftarrow> read_global gk0;
       let callee = locals callee_state;
       let globals2 = globs globals_state2;
       let cg = combine_global S dst caller callee globals2;
       answer (DG (combine_local S dst caller callee globals2) (eg \<squnion> cg))
     })"

text \<open>Per node \<open>v\<close>: if \<open>v\<close> is a callee entry, read back its own routed seed. The call-site
  entry-seed publication that used to live here moved into \<open>routed_cmb\<close>, which now owns
  the whole call lifecycle and shares one routed context between the seed publish and the
  combine's callee-exit read; this tree keeps only the half that cannot move, since a
  callee's own entry equation is the only place that can read its own seed slot back. \<open>route\<close>
  is kept as a parameter purely to match \<^locale>\<open>dg_ctx_activation\<close>'s \<open>extra\<close> calling
  convention (\<open>side_cfg_T_eff_keyed_seed_dg\<close> always supplies it); this tree no longer
  uses it.\<close>
definition routed_extra ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd::bounded_semilattice_sup_bot \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'd) dg_state) strategy_tree list"
where
  "routed_extra seed_key gk0 route ctx v =
     (case v of FunctionEntry _ \<Rightarrow>
        [do { seed_state \<leftarrow> read_global (seed_key v ctx); answer_local (globs seed_state) }]
       | _ \<Rightarrow> [])"

subsection \<open>Heterogeneous routing: the seed channel is 'D-typed, not 'G-typed\<close>

text \<open>
  \<^const>\<open>routed_cmb\<close>/\<^const>\<open>routed_extra\<close> above type \<open>S\<close> at \<open>('d, 'd) dg_spec\<close>: the
  seed publication (\<open>publish_seed\<close>, writing \<open>enter_local S fs as caller globals1\<close> --
  a \<open>'D\<close>-typed value, the callee's freshly entered local state) stores its payload in a
  \<^type>\<open>dg_state\<close>'s \<open>globs\<close> half, so it type-checks only when the analysis-global type
  \<open>'G\<close> already equals the domain-local type \<open>'D\<close>. A Base-style spec
  (\<open>base_dg_spec_for_lifted\<close>) is genuinely heterogeneous
  -- its whole local carrier already holds every VIMP variable, and its \<open>'G\<close> is a free,
  otherwise-unused type parameter every field threads through unchanged -- so forcing
  \<open>'G := 'D\<close> just to route it through \<open>routed_cmb\<close> would make \<open>gk0\<close> a dead
  accumulator: \<open>enter_global\<close>/\<open>combine_global\<close> (\<^const>\<open>dgs_enter\<close>/\<^const>\<open>dgs_combine\<close>'s
  \<open>fst\<close> half) are the identity on \<open>g\<close> for a Base-style spec, so no instantiation of
  \<open>'G\<close> ever lets \<open>gk0\<close> carry a genuine cross-context fact for it, and its own local
  answer (\<open>snd\<close>) never reads \<open>g\<close> either -- \<open>gk0\<close> is provably inert for such a spec,
  not merely unused by convention.

  \<open>routed_cmb_g\<close>/\<open>routed_extra_g\<close> keep \<open>'D\<close> and \<open>'G\<close> independent by moving the seed
  payload to the \<open>locals\<close> half of the \<^type>\<open>dg_state\<close> published at the seed key
  instead: a \<^type>\<open>dg_state\<close> already carries both fields at every key regardless of
  whether the key is reached through \<open>Inl\<close> (a \<open>(pp, 'c)\<close> local unknown) or \<open>Inr\<close> (a
  \<open>'k\<close> global unknown) -- \<open>locals\<close>/\<open>globs\<close> are call-site conventions, not something
  \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> themselves enforce. Since \<open>seed_key p ctx\<close> is always
  distinct from \<open>gk0\<close> (\<open>seed_key_ne_gk0\<close>) and no other equation ever publishes to a
  seed key, nothing else reads or writes that key's \<open>locals\<close> half, so the swap is free:
  the seed channel becomes genuinely \<open>'D\<close>-typed, and \<open>gk0\<close>'s own \<open>globs\<close>-typed
  publication (\<open>publish_global\<close>) is untouched, so \<open>'G\<close> can be instantiated
  independently of \<open>'D\<close> -- \<open>unit\<close> for a Base-style spec, honestly reflecting that no
  genuine global content exists.
\<close>

definition routed_cmb_g ::
  "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g S gk0 seed_key route ctx ca cc ex =
     with_call ca (\<lambda>dst fs as. do {
       caller_state \<leftarrow> read_local (cc, ctx);
       globals_state1 \<leftarrow> read_global gk0;
       let caller = locals caller_state;
       let globals1 = globs globals_state1;
       let ctx' = route cc ctx caller ca;
       let eg = enter_global S fs as caller globals1;
       depend_on (seed_key (FunctionEntry (result_proc ex)) ctx')
         (DG (enter_local S fs as caller globals1) bot) (answer (DG bot bot));
       callee_state \<leftarrow> read_local (ex, ctx');
       globals_state2 \<leftarrow> read_global gk0;
       let callee = locals callee_state;
       let globals2 = globs globals_state2;
       let cg = combine_global S dst caller callee globals2;
       publish_global gk0 (eg \<squnion> cg);
       answer_local (combine_local S dst caller callee globals2)
     })"

text \<open>Side-channel analogue of \<open>routed_extra\<close>: reads the seed back from its \<open>locals\<close>
  half, matching \<open>routed_cmb_g\<close>'s write.\<close>
definition routed_extra_g ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D::bounded_semilattice_sup_bot \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G::bounded_semilattice_sup_bot) dg_state) strategy_tree list"
where
  "routed_extra_g seed_key gk0 route ctx v =
     (case v of FunctionEntry _ \<Rightarrow>
        [do { seed_state \<leftarrow> read_global (seed_key v ctx); answer_local (locals seed_state) }]
       | _ \<Rightarrow> [])"

lemma routed_extra_g_free:
  "x \<in> set (routed_extra_g seed_key gk0 route ctx v) \<Longrightarrow> sides_of_rhs x tau z = bot"
  unfolding routed_extra_g_def by (cases v) (auto simp: bot_fun_def)

lemma routed_extra_g_local_only:
  "x \<in> set (routed_extra_g seed_key gk0 route ctx v) \<Longrightarrow> globs (traverse_rhs x tau) = bot"
  unfolding routed_extra_g_def by (cases v) auto

subsection \<open>Buffering correspondence hooks: routed_cmb / routed_cmb_contribution / routed_extra\<close>

text \<open>
  Purely syntactic facts about the tree shapes of \<^const>\<open>routed_cmb\<close>,
  \<^const>\<open>routed_cmb_contribution\<close>, and \<^const>\<open>routed_extra\<close> --- independent of any
  solved system, needed only to discharge
  \<^theory>\<open>Voblint_Core.DG_Framework\<close>'s \<open>side_cfg_T_eff_keyed_seed_dg_buffered_correspondence\<close>
  hypotheses when \<open>routed_cmb\<close>/\<open>routed_cmb_contribution\<close>/\<open>routed_extra\<close> instantiate its
  \<open>cmb\<close>/\<open>cmb_c\<close>/\<open>extra\<close> parameters. Stated standalone (not inside \<open>routed_context_base\<close>)
  since they need only \<open>seed_key\<close>'s freeness from \<open>gk0\<close>, not a solved-system
  interpretation.
\<close>

lemma routed_cmb_contribution_matches_local_standalone:
  "locals (traverse_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau)
     = locals (traverse_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau)"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def)

lemma routed_cmb_contribution_matches_global_standalone:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "globs (traverse_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau)
     = globs (sides_of_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau (Inr gk0))"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def ne[THEN not_sym])

lemma routed_cmb_side_pure:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "locals (sides_of_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau (Inr gk0)) = bot"
  unfolding routed_cmb_def
  by (cases ca) (simp add: Let_def ne)

lemma routed_cmb_contribution_free_at_key:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "sides_of_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau (Inr gk0) = bot"
  unfolding routed_cmb_contribution_def
  by (cases ca) (simp add: Let_def ne[THEN not_sym])

lemma routed_cmb_contribution_sides_off_key:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
    and z: "z \<noteq> Inr gk0"
  shows "sides_of_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau z
       = sides_of_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau z"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def ne z)

lemma routed_cmb_contribution_dep:
  "dep_aux tau (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex)
     = dep_aux tau (routed_cmb S gk0 seed_key route ctx ca cc ex)"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def)

lemma routed_extra_free:
  "x \<in> set (routed_extra seed_key gk0 route ctx v) \<Longrightarrow> sides_of_rhs x tau z = bot"
  unfolding routed_extra_def by (cases v) (auto simp: bot_fun_def)

lemma routed_extra_local_only:
  "x \<in> set (routed_extra seed_key gk0 route ctx v) \<Longrightarrow> globs (traverse_rhs x tau) = bot"
  unfolding routed_extra_def by (cases v) auto

subsection \<open>The locale\<close>

text \<open>Beyond \<^locale>\<open>dg_ctx_activation\<close>'s parameters: \<open>seed_key\<close> injects a routed
  \<open>(pp, 'c)\<close> pair into the global-key space; \<open>enterc\<close> is the trace-semantic context
  function keying the activation-local collecting semantics; and \<open>route_enterc_agree\<close> is
  the one agreement that cannot be discharged generically: at a real call edge, the
  equation-level \<open>route\<close>, evaluated on an abstract caller-local value, must agree with the
  semantic \<open>enterc\<close> on every concrete entered store the value concretizes to. Restricting
  the call action to an edge of \<open>g\<close> (rather than quantifying over every value of the
  \<open>call_action\<close> type) matches how CALL and COMB below only ever invoke this fact at a
  matched edge, and keeps the obligation provable for an abstract domain that is exact on
  edges actually present in the program without being exact everywhere. This is a
  per-instance proof obligation, not a locale theorem.\<close>

subsection \<open>A carrier-generic routed-context locale, staged ahead of routed_context's own migration (issue #123)\<close>

text \<open>
  Layer 4 (issue #123): as with \<^locale>\<open>dg_ctx_activation\<close>, \<open>routed_context\<close> hardcoded
  \<^const>\<open>gamma_unit\<close> and \<open>abs_state\<close> even though only \<open>route_enterc_agree\<close> names a
  concretization at all -- the other lemmas below compose \<^locale>\<open>dg_ctx_activation_base\<close>'s
  own inherited facts (\<open>enter_sound_fs\<close>, \<open>combine_sound_fs\<close>, \<open>gammaDG_mono\<close>, \<open>sg_cov\<close>) with
  routing bookkeeping that never fixes \<open>gammaDG\<close>'s or \<open>gammaM\<close>'s concrete choice.
  \<open>routed_context_base\<close> makes both free, matching \<open>dg_ctx_activation_base\<close>; \<open>routed_context\<close>
  below stays a thin specialization.
\<close>

locale routed_context_base =
  dg_ctx_activation_base S gammaDG gs g gk0 route
    "routed_cmb S gk0 seed_key" "routed_extra seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "('D::bounded_semilattice_sup_bot, 'D) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'D \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route ("context\<^sup>#")
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and gammaM :: "'M \<Rightarrow> store set" +
  fixes enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes finC[intro,simp]: "finite (calls g)"
    and seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and route_enterc_agree:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow>       s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)
            = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    and call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (FunctionEntry p, route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (cont, c1) \<in> vars"
    and call_enter_store_agree:
    "\<And>cl s es dst pars args p cont.
       call_enter_store gs g cl s es
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> es = call_enter gs (CallEdge dst pars args) s"
begin

lemma le_dg_state_localsD: "d \<le> d' \<Longrightarrow> locals d \<le> locals d'"
  by (simp add: less_eq_dg_state_def)

lemma le_dg_state_globsD: "d \<le> d' \<Longrightarrow> globs d \<le> globs d'"
  by (simp add: less_eq_dg_state_def)

subsection \<open>CALL: the routed callee entry\<close>

lemma routed_seed_read_bound:
  assumes covV: "(FunctionEntry p, ctx') \<in> vars"
  shows "globs (sigma (Inr (seed_key (FunctionEntry p) ctx')))
           \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
proof -
  let ?t = "QueryG (seed_key (FunctionEntry p) ctx') (\<lambda>s. Answer (DG (globs s) bot))"
  have mem: "?t \<in> set (trees (FunctionEntry p) ctx')"
    by (simp add: routed_extra_def)
  have "globs (sigma (Inr (seed_key (FunctionEntry p) ctx')))
      = locals (traverse_rhs ?t sigma)"
    by simp
  also have "\<dots> \<le> side_acc_dg (acc0 (FunctionEntry p)) sigma (trees (FunctionEntry p) ctx')"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (FunctionEntry p, ctx') sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
    using pp_eq_bound[OF covV] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma routed_seed_publish_bound_local:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, ctx) \<in> vars"
    and covV: "(FunctionEntry p,
                 route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)) \<in> vars"
  shows "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (FunctionEntry p,
               route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))))"
proof -
  let ?ctx' = "route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)"
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals d) (globs gv)))
                (QueryL (FunctionResult p, route u ctx (locals d) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals d) (globs gv)
                                        \<squnion> combine_global S dst (locals d) (locals dex) (globs gv2)))
                      (Answer (DG (combine_local S dst (locals d) (locals dex) (globs gv2)) bot)))))))"
  have ret: "(u, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont ctx)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have snd_bound:
    "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
       \<le> globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
  proof -
    have "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
        = globs (sides_of_rhs ?t sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (simp add: seed_key_ne_gk0)
    also have "\<dots> \<le> globs (sides_of_rhs
        (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
    also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
    also have "\<dots> \<le> globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr (seed_key (FunctionEntry p) ?ctx')"]
      by (rule le_dg_state_globsD)
    finally show ?thesis .
  qed
  have seed_le: "globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))
      \<le> locals (sigma (Inl (FunctionEntry p, ?ctx')))"
    by (rule routed_seed_read_bound[OF covV])
  show ?thesis using order_trans[OF snd_bound seed_le] .
qed

lemma routed_seed_publish_bound_global:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, ctx) \<in> vars"
  shows "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
           \<le> globs (sigma (Inr gk0))"
proof -
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals d) (globs gv)))
                (QueryL (FunctionResult p, route u ctx (locals d) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals d) (globs gv)
                                        \<squnion> combine_global S dst (locals d) (locals dex) (globs gv2)))
                      (Answer (DG (combine_local S dst (locals d) (locals dex) (globs gv2)) bot)))))))"
  have ret: "(u, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont ctx)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
      \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: seed_key_ne_gk0 seed_key_ne_gk0[symmetric] sup_dg_state_def bot_dg_state_def
             intro: le_supI1)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr gk0"]
    by (rule le_dg_state_globsD)
  finally show ?thesis .
qed

lemma routed_cmb_contribution_matches_local:
  "locals (traverse_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau)
     = locals (traverse_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau)"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def)

lemma routed_cmb_contribution_matches_global:
  "globs (traverse_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau)
     = globs (sides_of_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau (Inr gk0))"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def bot_dg_state_def sup_dg_state_def
    seed_key_ne_gk0 seed_key_ne_gk0[symmetric])

theorem routed_context_call:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaM (sg (Inl (u, ctx)))"
  shows "call_enter gs (CallEdge dst pars args) s
           \<in> gammaM (sg (Inl (FunctionEntry p,
                 enterc u ctx (call_enter gs (CallEdge dst pars args) s))))"
proof (cases "(u, ctx) \<in> vars")
  case False
  hence "gammaM (sg (Inl (u, ctx))) = {}" by (rule sg_uncovered_empty)
  thus ?thesis using sin by simp
next
  case True
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ctx' = "route u ctx ?d (CallEdge dst pars args)"
  have covV: "(FunctionEntry p, ?ctx') \<in> vars"
    using call_fwd[OF True ce] .
  have covV_cont: "(cont, ctx) \<in> vars"
    using comb_fwd[OF True ce] .
  have sin': "s \<in> gammaDG ?d ?g"
    using sin True by (simp add: sg_cov)
  have route_agree: "?ctx' = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    using route_enterc_agree[OF True ce sin'] .
  have "call_enter gs (CallEdge dst pars args) s
      \<in> gammaDG (snd (dgs_enter S pars args ?d ?g)) (fst (dgs_enter S pars args ?d ?g))"
    using enter_sound_fs[OF sin'] .
  also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (FunctionEntry p, ?ctx')))) ?g"
    by (rule gammaDG_mono[OF routed_seed_publish_bound_local[OF ce covV_cont covV]
          routed_seed_publish_bound_global[OF ce covV_cont]])
  also have "\<dots> = gammaM (sg (Inl (FunctionEntry p, ?ctx')))"
    using covV by (simp add: sg_cov)
  finally show ?thesis using route_agree by simp
qed

subsection \<open>COMB: the routed return combine\<close>

lemma routed_comb_bound_local:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "snd (dgs_combine S dst (locals (sigma (Inl (cl, c1))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (cont, c1)))"
proof -
  let ?ex_ctx = "route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)"
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryG gk0 (\<lambda>gv1.
              Side (seed_key (FunctionEntry p) (route cl c1 (locals dcl) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals dcl) (globs gv1)))
                (QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals dcl) (globs gv1)
                                        \<squnion> fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))))
                      (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))) bot)))))))"
  have ret: "(cl, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont c1)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have "snd (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (FunctionResult p, ?ex_ctx))))
           (globs (sigma (Inr gk0))))
      = locals (traverse_rhs ?t sigma)"
    by simp
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont c1)"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (cont, c1) sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (cont, c1)))"
    using pp_eq_bound[OF covV_cont] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma routed_comb_bound_global:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "fst (dgs_combine S dst (locals (sigma (Inl (cl, c1))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> globs (sigma (Inr gk0))"
proof -
  let ?ex_ctx = "route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)"
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryG gk0 (\<lambda>gv1.
              Side (seed_key (FunctionEntry p) (route cl c1 (locals dcl) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals dcl) (globs gv1)))
                (QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals dcl) (globs gv1)
                                        \<squnion> fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))))
                      (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))) bot)))))))"
  have ret: "(cl, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont c1)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have "fst (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (FunctionResult p, ?ex_ctx))))
           (globs (sigma (Inr gk0))))
      \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: seed_key_ne_gk0 seed_key_ne_gk0[symmetric] sup_dg_state_def bot_dg_state_def
        intro: le_supI2)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont c1)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, c1)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr gk0"]
    by (rule le_dg_state_globsD)
  finally show ?thesis .
qed

theorem routed_context_comb:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and s: "s \<in> gammaM (sg (Inl (cl, c1)))"
    and t: "t \<in> gammaM (sg (Inl (FunctionResult p, enterc cl c1 es)))"
    and ces: "call_enter_store gs g cl s es"
  shows "combine_collect gs dst s t \<in> gammaM (sg (Inl (cont, c1)))"
proof (cases "(cl, c1) \<in> vars")
  case False
  hence "gammaM (sg (Inl (cl, c1))) = {}" by (rule sg_uncovered_empty)
  thus ?thesis using s by simp
next
  case True
  let ?d = "locals (sigma (Inl (cl, c1)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ex_ctx = "route cl c1 ?d (CallEdge dst pars args)"
  have sin: "s \<in> gammaDG ?d ?g"
    using s True by (simp add: sg_cov)
  have es_eq: "es = call_enter gs (CallEdge dst pars args) s"
    using call_enter_store_agree ces ce by blast
  have route_agree: "?ex_ctx = enterc cl c1 es"
    using route_enterc_agree[OF True ce sin] es_eq by simp
  show ?thesis
  proof (cases "(FunctionResult p, ?ex_ctx) \<in> vars")
    case False
    hence "gammaM (sg (Inl (FunctionResult p, ?ex_ctx))) = {}" by (rule sg_uncovered_empty)
    with route_agree have "gammaM (sg (Inl (FunctionResult p, enterc cl c1 es))) = {}" by simp
    with t show ?thesis by simp
  next
    case True
    have covV_cont: "(cont, c1) \<in> vars"
      using comb_fwd[OF \<open>(cl, c1) \<in> vars\<close> ce] .
    have tin: "t \<in> gammaDG (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g"
      using t route_agree True by (simp add: sg_cov)
    have "combine_collect gs dst s t
        \<in> gammaDG (snd (dgs_combine S dst ?d (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))
             (fst (dgs_combine S dst ?d (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))"
      using combine_sound_fs[OF sin tin] .
    also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (cont, c1)))) ?g"
      by (rule gammaDG_mono[OF routed_comb_bound_local[OF ce covV_cont]
            routed_comb_bound_global[OF ce covV_cont]])
    also have "\<dots> = gammaM (sg (Inl (cont, c1)))"
      using covV_cont by (simp add: sg_cov)
    finally show ?thesis .
  qed
qed

end

subsection \<open>A heterogeneous routed-context locale: D and G independently typed\<close>

text \<open>
  \<open>routed_context_base_hetero\<close> is \<open>routed_context_base\<close> built from \<open>routed_cmb_g\<close>/
  \<open>routed_extra_g\<close> instead of \<open>routed_cmb\<close>/\<open>routed_extra\<close>, so \<open>S\<close>'s own \<open>'D\<close>/\<open>'G\<close>
  stay as independent as \<^locale>\<open>dg_ctx_activation_base\<close> already keeps them -- no
  \<open>'D = 'G\<close> constraint is threaded in by this locale's \<open>for\<close> clause the way
  \<open>routed_context_base\<close>'s was. \<^locale>\<open>dg_ctx_activation_base\<close> itself needs no change:
  every fact it supplies (\<open>pp_eq_bound\<close>, \<open>pp_sides_bound\<close>, \<open>sides_fold_le_Gen\<close>,
  \<open>edge_bound_local\<close>/\<open>_global\<close>, \<open>dg_ctx_act_edge\<close>, \<open>dg_ctx_act_comb_covered\<close>) is
  already generic in \<open>cmb\<close>/\<open>extra\<close>, so instantiating it at \<open>routed_cmb_g\<close>/
  \<open>routed_extra_g\<close> reuses those proofs unchanged; only the seed-specific reasoning
  below (which \<open>dg_ctx_activation_base\<close> never had, since seeding is
  \<open>routed_cmb\<close>/\<open>routed_cmb_g\<close>'s own addition) is redone here for the swapped
  \<open>locals\<close>/\<open>globs\<close> convention.
\<close>

locale routed_context_base_hetero =
  dg_ctx_activation_base S gammaDG gs g gk0 route
    "routed_cmb_g S gk0 seed_key" "routed_extra_g seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route ("context\<^sup>#")
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and gammaM :: "'M \<Rightarrow> store set" +
  fixes enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes finC[intro,simp]: "finite (calls g)"
    and seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and route_enterc_agree:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow>       s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)
            = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    and call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (FunctionEntry p, route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (cont, c1) \<in> vars"
    and call_enter_store_agree:
    "\<And>cl s es dst pars args p cont.
       call_enter_store gs g cl s es
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> es = call_enter gs (CallEdge dst pars args) s"
begin

lemma le_dg_state_localsD: "d \<le> d' \<Longrightarrow> locals d \<le> locals d'"
  by (simp add: less_eq_dg_state_def)

lemma le_dg_state_globsD: "d \<le> d' \<Longrightarrow> globs d \<le> globs d'"
  by (simp add: less_eq_dg_state_def)

subsection \<open>CALL: the routed callee entry\<close>

lemma routed_seed_read_bound:
  assumes covV: "(FunctionEntry p, ctx') \<in> vars"
  shows "locals (sigma (Inr (seed_key (FunctionEntry p) ctx')))
           \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
proof -
  let ?t = "QueryG (seed_key (FunctionEntry p) ctx') (\<lambda>s. Answer (DG (locals s) bot))"
  have mem: "?t \<in> set (trees (FunctionEntry p) ctx')"
    by (simp add: routed_extra_g_def)
  have "locals (sigma (Inr (seed_key (FunctionEntry p) ctx')))
      = locals (traverse_rhs ?t sigma)"
    by simp
  also have "\<dots> \<le> side_acc_dg (acc0 (FunctionEntry p)) sigma (trees (FunctionEntry p) ctx')"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (FunctionEntry p, ctx') sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
    using pp_eq_bound[OF covV] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma routed_seed_publish_bound_local:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, ctx) \<in> vars"
    and covV: "(FunctionEntry p,
                 route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)) \<in> vars"
  shows "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (FunctionEntry p,
               route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))))"
proof -
  let ?ctx' = "route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)"
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                (DG (enter_local S pars args (locals d) (globs gv)) bot)
                (QueryL (FunctionResult p, route u ctx (locals d) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals d) (globs gv)
                                        \<squnion> combine_global S dst (locals d) (locals dex) (globs gv2)))
                      (Answer (DG (combine_local S dst (locals d) (locals dex) (globs gv2)) bot)))))))"
  have ret: "(u, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont ctx)"
    unfolding routed_cmb_g_def Let_def using ret by (force intro: rev_image_eqI)
  have snd_bound:
    "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
       \<le> locals (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
  proof -
    have "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
        = locals (sides_of_rhs ?t sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (simp add: seed_key_ne_gk0)
    also have "\<dots> \<le> locals (sides_of_rhs
        (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_localsD[OF sides_le_side_rhs_fold_dg[OF mem]])
    also have "\<dots> \<le> locals (sides_of_rhs (Gen (cont, ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_localsD[OF sides_fold_le_Gen])
    also have "\<dots> \<le> locals (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr (seed_key (FunctionEntry p) ?ctx')"]
      by (rule le_dg_state_localsD)
    finally show ?thesis .
  qed
  have seed_le: "locals (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))
      \<le> locals (sigma (Inl (FunctionEntry p, ?ctx')))"
    by (rule routed_seed_read_bound[OF covV])
  show ?thesis using order_trans[OF snd_bound seed_le] .
qed

lemma routed_seed_publish_bound_global:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, ctx) \<in> vars"
  shows "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
           \<le> globs (sigma (Inr gk0))"
proof -
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                (DG (enter_local S pars args (locals d) (globs gv)) bot)
                (QueryL (FunctionResult p, route u ctx (locals d) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals d) (globs gv)
                                        \<squnion> combine_global S dst (locals d) (locals dex) (globs gv2)))
                      (Answer (DG (combine_local S dst (locals d) (locals dex) (globs gv2)) bot)))))))"
  have ret: "(u, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont ctx)"
    unfolding routed_cmb_g_def Let_def using ret by (force intro: rev_image_eqI)
  have "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
      \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: seed_key_ne_gk0 seed_key_ne_gk0[symmetric] sup_dg_state_def bot_dg_state_def
             intro: le_supI1)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr gk0"]
    by (rule le_dg_state_globsD)
  finally show ?thesis .
qed

theorem routed_context_call:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaM (sg (Inl (u, ctx)))"
  shows "call_enter gs (CallEdge dst pars args) s
           \<in> gammaM (sg (Inl (FunctionEntry p,
                 enterc u ctx (call_enter gs (CallEdge dst pars args) s))))"
proof (cases "(u, ctx) \<in> vars")
  case False
  hence "gammaM (sg (Inl (u, ctx))) = {}" by (rule sg_uncovered_empty)
  thus ?thesis using sin by simp
next
  case True
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ctx' = "route u ctx ?d (CallEdge dst pars args)"
  have covV: "(FunctionEntry p, ?ctx') \<in> vars"
    using call_fwd[OF True ce] .
  have covV_cont: "(cont, ctx) \<in> vars"
    using comb_fwd[OF True ce] .
  have sin': "s \<in> gammaDG ?d ?g"
    using sin True by (simp add: sg_cov)
  have route_agree: "?ctx' = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    using route_enterc_agree[OF True ce sin'] .
  have "call_enter gs (CallEdge dst pars args) s
      \<in> gammaDG (snd (dgs_enter S pars args ?d ?g)) (fst (dgs_enter S pars args ?d ?g))"
    using enter_sound_fs[OF sin'] .
  also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (FunctionEntry p, ?ctx')))) ?g"
    by (rule gammaDG_mono[OF routed_seed_publish_bound_local[OF ce covV_cont covV]
          routed_seed_publish_bound_global[OF ce covV_cont]])
  also have "\<dots> = gammaM (sg (Inl (FunctionEntry p, ?ctx')))"
    using covV by (simp add: sg_cov)
  finally show ?thesis using route_agree by simp
qed

subsection \<open>COMB: the routed return combine\<close>

lemma routed_comb_bound_local:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "snd (dgs_combine S dst (locals (sigma (Inl (cl, c1))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (cont, c1)))"
proof -
  let ?ex_ctx = "route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)"
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryG gk0 (\<lambda>gv1.
              Side (seed_key (FunctionEntry p) (route cl c1 (locals dcl) (CallEdge dst pars args)))
                (DG (enter_local S pars args (locals dcl) (globs gv1)) bot)
                (QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals dcl) (globs gv1)
                                        \<squnion> fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))))
                      (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))) bot)))))))"
  have ret: "(cl, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont c1)"
    unfolding routed_cmb_g_def Let_def using ret by (force intro: rev_image_eqI)
  have "snd (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (FunctionResult p, ?ex_ctx))))
           (globs (sigma (Inr gk0))))
      = locals (traverse_rhs ?t sigma)"
    by simp
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont c1)"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (cont, c1) sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (cont, c1)))"
    using pp_eq_bound[OF covV_cont] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma routed_comb_bound_global:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "fst (dgs_combine S dst (locals (sigma (Inl (cl, c1))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> globs (sigma (Inr gk0))"
proof -
  let ?ex_ctx = "route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)"
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryG gk0 (\<lambda>gv1.
              Side (seed_key (FunctionEntry p) (route cl c1 (locals dcl) (CallEdge dst pars args)))
                (DG (enter_local S pars args (locals dcl) (globs gv1)) bot)
                (QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals dcl) (globs gv1)
                                        \<squnion> fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))))
                      (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))) bot)))))))"
  have ret: "(cl, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont c1)"
    unfolding routed_cmb_g_def Let_def using ret by (force intro: rev_image_eqI)
  have "fst (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (FunctionResult p, ?ex_ctx))))
           (globs (sigma (Inr gk0))))
      \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: seed_key_ne_gk0 seed_key_ne_gk0[symmetric] sup_dg_state_def bot_dg_state_def
        intro: le_supI2)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont c1)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, c1)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr gk0"]
    by (rule le_dg_state_globsD)
  finally show ?thesis .
qed

theorem routed_context_comb:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and s: "s \<in> gammaM (sg (Inl (cl, c1)))"
    and t: "t \<in> gammaM (sg (Inl (FunctionResult p, enterc cl c1 es)))"
    and ces: "call_enter_store gs g cl s es"
  shows "combine_collect gs dst s t \<in> gammaM (sg (Inl (cont, c1)))"
proof (cases "(cl, c1) \<in> vars")
  case False
  hence "gammaM (sg (Inl (cl, c1))) = {}" by (rule sg_uncovered_empty)
  thus ?thesis using s by simp
next
  case True
  let ?d = "locals (sigma (Inl (cl, c1)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ex_ctx = "route cl c1 ?d (CallEdge dst pars args)"
  have sin: "s \<in> gammaDG ?d ?g"
    using s True by (simp add: sg_cov)
  have es_eq: "es = call_enter gs (CallEdge dst pars args) s"
    using call_enter_store_agree ces ce by blast
  have route_agree: "?ex_ctx = enterc cl c1 es"
    using route_enterc_agree[OF True ce sin] es_eq by simp
  show ?thesis
  proof (cases "(FunctionResult p, ?ex_ctx) \<in> vars")
    case False
    hence "gammaM (sg (Inl (FunctionResult p, ?ex_ctx))) = {}" by (rule sg_uncovered_empty)
    with route_agree have "gammaM (sg (Inl (FunctionResult p, enterc cl c1 es))) = {}" by simp
    with t show ?thesis by simp
  next
    case True
    have covV_cont: "(cont, c1) \<in> vars"
      using comb_fwd[OF \<open>(cl, c1) \<in> vars\<close> ce] .
    have tin: "t \<in> gammaDG (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g"
      using t route_agree True by (simp add: sg_cov)
    have "combine_collect gs dst s t
        \<in> gammaDG (snd (dgs_combine S dst ?d (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))
             (fst (dgs_combine S dst ?d (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))"
      using combine_sound_fs[OF sin tin] .
    also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (cont, c1)))) ?g"
      by (rule gammaDG_mono[OF routed_comb_bound_local[OF ce covV_cont]
            routed_comb_bound_global[OF ce covV_cont]])
    also have "\<dots> = gammaM (sg (Inl (cont, c1)))"
      using covV_cont by (simp add: sg_cov)
    finally show ?thesis .
  qed
qed


end

locale routed_context =
  dg_ctx_activation S gs g gk0 route "routed_cmb S gk0 seed_key" "routed_extra seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg
  for S :: "('a::sound_domain abs_state, 'a abs_state) dg_spec"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route ("context\<^sup>#")
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k" +
  fixes enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes finC[intro,simp]: "finite (calls g)"
    and seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and route_enterc_agree:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow>       s \<in> gamma_unit gs (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)
            = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    and call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (FunctionEntry p, route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (cont, c1) \<in> vars"
    and call_enter_store_agree:
    "\<And>cl s es dst pars args p cont.
       call_enter_store gs g cl s es
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> es = call_enter gs (CallEdge dst pars args) s"
begin

text \<open>
  \<open>routed_context\<close> is exactly \<open>routed_context_base\<close> at \<open>gammaDG := gamma_unit gs\<close>,
  \<open>gammaM := gamma_state\<close>, matching \<^locale>\<open>dg_ctx_activation\<close>'s own specialization.
\<close>
sublocale base: routed_context_base S "\<lambda>d g. gamma_unit gs d g" gs
  g gk0 route bot0 s0d s0g sigma vars x0 sg seed_key "\<lambda>s. \<lbrakk>s\<rbrakk>" enterc
proof unfold_locales
  show "finite (calls g)" by (rule finC)
next
  show "\<And>p ctx. seed_key p ctx \<noteq> gk0" by (rule seed_key_ne_gk0)
next
  fix u ctx dst pars args p cont s
  assume "(u, ctx) \<in> vars" "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    "s \<in> gamma_unit gs (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
  then show "route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)
      = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    by (rule route_enterc_agree)
next
  fix u ctx dst pars args p cont
  assume "(u, ctx) \<in> vars" "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  then show "(FunctionEntry p, route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
        \<in> vars"
    by (rule call_fwd)
next
  fix cl c1 dst pars args p cont
  assume "(cl, c1) \<in> vars" "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  then show "(cont, c1) \<in> vars" by (rule comb_fwd)
next
  fix cl s es dst pars args p cont
  assume "call_enter_store gs g cl s es" "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  then show "es = call_enter gs (CallEdge dst pars args) s" by (rule call_enter_store_agree)
qed

lemma le_dg_state_localsD: "d \<le> d' \<Longrightarrow> locals d \<le> locals d'"
  by (simp add: less_eq_dg_state_def)

lemma le_dg_state_globsD: "d \<le> d' \<Longrightarrow> globs d \<le> globs d'"
  by (simp add: less_eq_dg_state_def)

subsection \<open>CALL: the routed callee entry\<close>

lemma routed_seed_read_bound:
  assumes covV: "(FunctionEntry p, ctx') \<in> vars"
  shows "globs (sigma (Inr (seed_key (FunctionEntry p) ctx')))
           \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
proof -
  let ?t = "QueryG (seed_key (FunctionEntry p) ctx') (\<lambda>s. Answer (DG (globs s) bot))"
  have mem: "?t \<in> set (trees (FunctionEntry p) ctx')"
    by (simp add: routed_extra_def)
  have "globs (sigma (Inr (seed_key (FunctionEntry p) ctx')))
      = locals (traverse_rhs ?t sigma)"
    by simp
  also have "\<dots> \<le> side_acc_dg (acc0 (FunctionEntry p)) sigma (trees (FunctionEntry p) ctx')"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (FunctionEntry p, ctx') sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
    using pp_eq_bound[OF covV] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

text \<open>Split into the two componentwise bounds \<open>gamma_unit_mono\<close>/\<open>combine_env_abs\<close> routing
  needs, instead of one bound against the raw join: the local answer's own bound never
  mentions \<open>gk0\<close>, and the global publication's own bound never mentions the routed seed
  key at all, so each is proved (and usable) independently of the other.\<close>
text \<open>Restated for \<open>routed_cmb\<close>'s expanded shape (2026-08-11, issue #114): the entry-seed
  publication this bounds no longer lives in the call site's own equation
  (\<open>trees u ctx\<close>, via \<open>routed_extra\<close>) but in the continuation's (\<open>trees cont ctx\<close>, via the
  expanded \<open>routed_cmb\<close>), so the coverage premise is now \<open>(cont, ctx) \<in> vars\<close> --
  \<open>comb_fwd\<close>'s own conclusion -- instead of \<open>(u, ctx) \<in> vars\<close>. This is exactly the
  restructuring #114 asked for: the routed context \<open>?ctx'\<close> below is the same term the
  combine's callee-exit read uses, computed once inside \<open>routed_cmb\<close>, not independently
  re-derived here.\<close>
lemma routed_seed_publish_bound_local:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, ctx) \<in> vars"
    and covV: "(FunctionEntry p,
                 route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)) \<in> vars"
  shows "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (FunctionEntry p,
               route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))))"
proof -
  let ?ctx' = "route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)"
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals d) (globs gv)))
                (QueryL (FunctionResult p, route u ctx (locals d) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals d) (globs gv)
                                        \<squnion> combine_global S dst (locals d) (locals dex) (globs gv2)))
                      (Answer (DG (combine_local S dst (locals d) (locals dex) (globs gv2)) bot)))))))"
  have ret: "(u, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont ctx)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have snd_bound:
    "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
       \<le> globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
  proof -
    have "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
        = globs (sides_of_rhs ?t sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (simp add: seed_key_ne_gk0)
    also have "\<dots> \<le> globs (sides_of_rhs
        (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
    also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
    also have "\<dots> \<le> globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr (seed_key (FunctionEntry p) ?ctx')"]
      by (rule le_dg_state_globsD)
    finally show ?thesis .
  qed
  have seed_le: "globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))
      \<le> locals (sigma (Inl (FunctionEntry p, ?ctx')))"
    by (rule routed_seed_read_bound[OF covV])
  show ?thesis using order_trans[OF snd_bound seed_le] .
qed

lemma routed_seed_publish_bound_global:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, ctx) \<in> vars"
  shows "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
           \<le> globs (sigma (Inr gk0))"
proof -
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals d) (globs gv)))
                (QueryL (FunctionResult p, route u ctx (locals d) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals d) (globs gv)
                                        \<squnion> combine_global S dst (locals d) (locals dex) (globs gv2)))
                      (Answer (DG (combine_local S dst (locals d) (locals dex) (globs gv2)) bot)))))))"
  have ret: "(u, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont ctx)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
      \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: seed_key_ne_gk0 seed_key_ne_gk0[symmetric] sup_dg_state_def bot_dg_state_def
             intro: le_supI1)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr gk0"]
    by (rule le_dg_state_globsD)
  finally show ?thesis .
qed

lemma routed_cmb_contribution_matches_local:
  "locals (traverse_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau)
     = locals (traverse_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau)"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def)

lemma routed_cmb_contribution_matches_global:
  "globs (traverse_rhs (routed_cmb_contribution S gk0 seed_key route ctx ca cc ex) tau)
     = globs (sides_of_rhs (routed_cmb S gk0 seed_key route ctx ca cc ex) tau (Inr gk0))"
  unfolding routed_cmb_contribution_def routed_cmb_def
  by (cases ca) (simp add: Let_def bot_dg_state_def sup_dg_state_def
    seed_key_ne_gk0 seed_key_ne_gk0[symmetric])

theorem routed_context_call:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> \<lbrakk>sg (Inl (u, ctx))\<rbrakk>"
  shows "call_enter gs (CallEdge dst pars args) s
           \<in> \<lbrakk>sg (Inl (FunctionEntry p,
                 enterc u ctx (call_enter gs (CallEdge dst pars args) s)))\<rbrakk>"
proof (cases "(u, ctx) \<in> vars")
  case False
  hence "\<lbrakk>sg (Inl (u, ctx))\<rbrakk> = {}" by (rule sg_uncovered_empty)
  thus ?thesis using sin by simp
next
  case True
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ctx' = "route u ctx ?d (CallEdge dst pars args)"
  have covV: "(FunctionEntry p, ?ctx') \<in> vars"
    using call_fwd[OF True ce] .
  have covV_cont: "(cont, ctx) \<in> vars"
    using comb_fwd[OF True ce] .
  have sin': "s \<in> gamma_unit gs ?d ?g"
    using sin True by (simp add: sg_cov gamma_unit_def)
  have route_agree: "?ctx' = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    using route_enterc_agree[OF True ce sin'] .
  have "call_enter gs (CallEdge dst pars args) s
      \<in> gamma_unit gs (snd (dgs_enter S pars args ?d ?g)) (fst (dgs_enter S pars args ?d ?g))"
    using enter_sound_fs[OF sin'] .
  also have "\<dots> \<subseteq> gamma_unit gs (locals (sigma (Inl (FunctionEntry p, ?ctx')))) ?g"
    by (rule gamma_unit_mono[OF routed_seed_publish_bound_local[OF ce covV_cont covV]
          routed_seed_publish_bound_global[OF ce covV_cont]])
  also have "\<dots> = \<lbrakk>sg (Inl (FunctionEntry p, ?ctx'))\<rbrakk>"
    using covV by (simp add: sg_cov gamma_unit_def)
  finally show ?thesis using route_agree by simp

qed

subsection \<open>COMB: the routed return combine\<close>

text \<open>Split as \<open>routed_seed_publish_bound_local\<close>/\<open>_global\<close> was: each componentwise
  bound stands on its own, matching what \<open>gamma_unit_mono\<close> needs for the routed
  combine's \<open>combine_env_abs\<close>-shaped target.\<close>
lemma routed_comb_bound_local:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "snd (dgs_combine S dst (locals (sigma (Inl (cl, c1))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (cont, c1)))"
proof -
  let ?ex_ctx = "route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)"
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryG gk0 (\<lambda>gv1.
              Side (seed_key (FunctionEntry p) (route cl c1 (locals dcl) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals dcl) (globs gv1)))
                (QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals dcl) (globs gv1)
                                        \<squnion> fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))))
                      (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))) bot)))))))"
  have ret: "(cl, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont c1)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have "snd (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (FunctionResult p, ?ex_ctx))))
           (globs (sigma (Inr gk0))))
      = locals (traverse_rhs ?t sigma)"
    by simp
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont c1)"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (cont, c1) sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (cont, c1)))"
    using pp_eq_bound[OF covV_cont] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma routed_comb_bound_global:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "fst (dgs_combine S dst (locals (sigma (Inl (cl, c1))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> globs (sigma (Inr gk0))"
proof -
  let ?ex_ctx = "route cl c1 (locals (sigma (Inl (cl, c1)))) (CallEdge dst pars args)"
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryG gk0 (\<lambda>gv1.
              Side (seed_key (FunctionEntry p) (route cl c1 (locals dcl) (CallEdge dst pars args)))
                (DG bot (enter_local S pars args (locals dcl) (globs gv1)))
                (QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
                  (\<lambda>dex. QueryG gk0 (\<lambda>gv2.
                    Side gk0 (DG bot (enter_global S pars args (locals dcl) (globs gv1)
                                        \<squnion> fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))))
                      (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv2))) bot)))))))"
  have ret: "(cl, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont c1)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have "fst (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (FunctionResult p, ?ex_ctx))))
           (globs (sigma (Inr gk0))))
      \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: seed_key_ne_gk0 seed_key_ne_gk0[symmetric] sup_dg_state_def bot_dg_state_def
        intro: le_supI2)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont c1)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (cont, c1)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF covV_cont, THEN le_funD, of "Inr gk0"]
    by (rule le_dg_state_globsD)
  finally show ?thesis .
qed

theorem routed_context_comb:
  assumes ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and s: "s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk>"
    and t: "t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc cl c1 es))\<rbrakk>"
    and ces: "call_enter_store gs g cl s es"
  shows "combine_collect gs dst s t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
proof (cases "(cl, c1) \<in> vars")
  case False
  hence "\<lbrakk>sg (Inl (cl, c1))\<rbrakk> = {}" by (rule sg_uncovered_empty)
  thus ?thesis using s by simp
next
  case True
  let ?d = "locals (sigma (Inl (cl, c1)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ex_ctx = "route cl c1 ?d (CallEdge dst pars args)"
  have sin: "s \<in> gamma_unit gs ?d ?g"
    using s True by (simp add: sg_cov gamma_unit_def)
  have es_eq: "es = call_enter gs (CallEdge dst pars args) s"
    using call_enter_store_agree ces ce by blast
  have route_agree: "?ex_ctx = enterc cl c1 es"
    using route_enterc_agree[OF True ce sin] es_eq by simp
  show ?thesis
  proof (cases "(FunctionResult p, ?ex_ctx) \<in> vars")
    case False
    hence "\<lbrakk>sg (Inl (FunctionResult p, ?ex_ctx))\<rbrakk> = {}" by (rule sg_uncovered_empty)
    with route_agree have "\<lbrakk>sg (Inl (FunctionResult p, enterc cl c1 es))\<rbrakk> = {}" by simp
    with t show ?thesis by simp
  next
    case True
    have covV_cont: "(cont, c1) \<in> vars"
      using comb_fwd[OF \<open>(cl, c1) \<in> vars\<close> ce] .
    have tin: "t \<in> gamma_unit gs (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g"
      using t route_agree True by (simp add: sg_cov gamma_unit_def)
    have "combine_collect gs dst s t
        \<in> gamma_unit gs (snd (dgs_combine S dst ?d (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))
             (fst (dgs_combine S dst ?d (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))"
      using combine_sound_fs[OF sin tin] .
    also have "\<dots> \<subseteq> gamma_unit gs (locals (sigma (Inl (cont, c1)))) ?g"
      by (rule gamma_unit_mono[OF routed_comb_bound_local[OF ce covV_cont]
            routed_comb_bound_global[OF ce covV_cont]])
    also have "\<dots> = \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
      using covV_cont by (simp add: sg_cov gamma_unit_def)
    finally show ?thesis .
  qed
qed


end

subsection \<open>Formal-entry contexts: routing on the callee's declared formals\<close>

text \<open>
  A context type derived from the callee's declared formals rather than call-site
  history: \<open>'a list\<close>, one abstract value per formal, in the order \<^const>\<open>CallEdge\<close>
  already carries them --- populated at compile time from the callee's own
  declaration, so no separate procedure-table lookup is needed here.
  \<open>formals_context\<close> is the plain per-variable projection (\<^typ>\<open>'a abs_state\<close> is
  \<^typ>\<open>vname \<Rightarrow> 'a\<close>, so this is just \<^const>\<open>map\<close>); \<open>formals_route\<close> applies it to
  the entered local state via \<^const>\<open>enter_local\<close>, the same enter transfer every
  other CALL obligation uses; \<open>formals_context_sem\<close> is its trace-semantic counterpart,
  decoding the concrete entered store's formals the same way, given the point
  abstraction \<open>decode\<close> a domain provides for a concrete value and the CFG needed
  to look up a call site's own formal list. Neither definition mentions a
  domain-specific accessor beyond \<open>decode\<close> itself, so any domain reusing
  \<^locale>\<open>routed_context\<close> instantiates this pair once instead of hand-writing a
  per-formal projection, as \<open>route_ivl\<close>/\<open>ivl_context\<close> previously did.
\<close>

definition formals_context :: "vname list \<Rightarrow> 'a abs_state \<Rightarrow> 'a list" where
  "formals_context pars d = map d pars"

definition formals_route ::
  "('a::sound_domain abs_state, 'a abs_state) dg_spec \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route S d ca =
     (case ca of CallEdge dst pars args \<Rightarrow> formals_context pars (enter_local S pars args d bot))"

text \<open>The routing hook's exact calling convention (\<^locale>\<open>dg_ctx_activation\<close>'s
  \<open>route\<close>): generic over call site and caller context, using only the entered
  store, as \<open>route_ivl_gen\<close> already was.\<close>
definition formals_route_gen ::
  "('a::sound_domain abs_state, 'a abs_state) dg_spec
     \<Rightarrow> pp \<Rightarrow> 'a list \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route_gen S u ctx d ca = formals_route S d ca"

text \<open>The formals of the call originating at \<open>u\<close>: at most one, by the compiler's
  own invariant (\<^theory>\<open>Voblint_CFG.VIMP_Proc_to_CFG\<close> emits a single \<^const>\<open>CallEdge\<close>
  per \<^const>\<open>Call\<close>); \<open>[]\<close> if \<open>u\<close> has none.\<close>
definition formals_at_call_site :: "cfg \<Rightarrow> pp \<Rightarrow> vname list" where
  "formals_at_call_site g u =
     (case filter (\<lambda>(c, ca, ce, k). c = u) (cfg_calls_list g) of
        (_, CallEdge _ pars _, _, _) # _ \<Rightarrow> pars
      | _ \<Rightarrow> [])"

definition formals_context_sem ::
  "cfg \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> cfg_node \<Rightarrow> 'a list \<Rightarrow> store \<Rightarrow> 'a list"
where
  "formals_context_sem g decode u ctx s = formals_context (formals_at_call_site g u) (decode \<circ> s)"

text \<open>
  The whole matched \<^type>\<open>call_action\<close> at a node, not only its formals: an
  \<open>enterc\<close> built purely from the caller's own solved abstract state (rather than
  by decoding the concrete entered store, as \<^const>\<open>formals_context_sem\<close> does) needs
  the callee's actuals too, to recompute the same \<^const>\<open>dgs_enter\<close> the route
  itself already ran. Same convention as \<^const>\<open>formals_at_call_site\<close>: the head
  of the filtered call list, \<open>CallEdge None [] []\<close> if \<open>u\<close> has no outgoing call.
\<close>

definition call_action_at_call_site :: "cfg \<Rightarrow> pp \<Rightarrow> call_action" where
  "call_action_at_call_site g u =
     (case filter (\<lambda>(c, ca, ce, k). c = u) (cfg_calls_list g) of
        (_, ca, _, _) # _ \<Rightarrow> ca
      | _ \<Rightarrow> CallEdge None [] [])"

text \<open>
  Not a locale theorem, same as \<open>route_enterc_agree\<close> itself: whether a node has at
  most one outgoing call is a per-instance fact about \<open>g\<close>, true for
  \<^const>\<open>compile_prog\<close> output (\<^theory>\<open>Voblint_CFG.VIMP_Proc_to_CFG\<close>'s
  \<open>compile_prog_calls_source_unique\<close>) but not for an arbitrary hand-built CFG.
\<close>

lemma call_action_at_call_site_eq:
  assumes fin: "finite (calls g)"
    and uniq: "\<And>ca1 ce1 af1 ca2 ce2 af2.
                 (u, ca1, ce1, af1) \<in> calls g \<Longrightarrow> (u, ca2, ce2, af2) \<in> calls g
                 \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
    and ce: "(u, ca, cf, af) \<in> calls g"
  shows "call_action_at_call_site g u = ca"
proof -
  let ?P = "\<lambda>(c, ca, ce, k). c = u"
  let ?L = "cfg_calls_list g"
  have mem: "(u, ca, cf, af) \<in> set ?L" using ce fin by simp
  have distinctL: "distinct ?L" unfolding cfg_calls_list_code by (rule distinct_sorted_list_of_set)
  have "set (filter ?P ?L) = {(u, ca, cf, af)}"
  proof (rule set_eqI, rule iffI)
    fix x assume hx: "x \<in> set (filter ?P ?L)"
    then have memx: "x \<in> set ?L" and px: "?P x" by (auto simp: set_filter)
    obtain c ca' ce' af' where x: "x = (c, ca', ce', af')" by (cases x) auto
    from px x have cU: "c = u" by simp
    from memx x cU fin have "(u, ca', ce', af') \<in> calls g" by simp
    with uniq[OF ce] have "ca' = ca" "ce' = cf" "af' = af" by auto
    thus "x \<in> {(u, ca, cf, af)}" using x cU by simp
  next
    fix x assume "x \<in> {(u, ca, cf, af)}"
    thus "x \<in> set (filter ?P ?L)" using mem by simp
  qed
  moreover have "distinct (filter ?P ?L)" using distinctL by (rule distinct_filter)
  ultimately have "filter ?P ?L = [(u, ca, cf, af)]"
    apply (cases "filter (\<lambda>(c, ca, ce, k). c = u) (cfg_calls_list g)")
    using singleton_iff subset_singletonD by(fastforce)+
  thus ?thesis unfolding call_action_at_call_site_def by simp
qed

end
