theory Routed_Context
  imports Routed_Call_Trees DG_Ctx_Activation DG_Local_State_Spec "Voblint_CFG.LTR_Def"
    Activation_Backbone
begin

section \<open>One route, CALL and COMB discharged once\<close>

text \<open>
  \<^locale>\<open>dg_ctx_activation_base\<close> already discharges EDGE (\<open>dg_ctx_act_edge\<close>) generically off the
  post-solution, independent of \<open>route\<close>/\<open>cmb\<close>/\<open>extra\<close>: intra edges never route. Its COMB
  analogue (\<open>dg_ctx_act_comb_covered\<close>) is generic in the same sense but still takes the
  tree's contribution as an assumption (\<open>bound\<close>) rather than deriving it, because \<open>cmb\<close> is
  an unconstrained parameter: a context-sensitive analysis whose entry-seed publication and
  return combine are hand-written has to rederive that same routing argument itself. This
  theory fixes \<open>cmb\<close> and \<open>extra\<close> to the one canonical shape \<open>Routed_Call_Trees\<close>
  builds --- parametric only in a routing function \<open>route\<close> and a seed-key injection
  \<open>seed_key\<close> --- and discharges CALL and COMB as theorems of that shape: a k-call-string
  or a partial-tabulation context becomes an interpretation of this locale, not a second
  proof development.
\<close>

subsection \<open>The routed-context locale: D and G independently typed\<close>

text \<open>
  \<open>routed_context_base_hetero\<close> instantiates \<^locale>\<open>dg_ctx_activation_base\<close> at
  \<open>routed_call_tree\<close>/\<open>routed_entry_seed_tree\<close>, so \<open>S\<close>'s own \<open>'D\<close>/\<open>'G\<close> stay as
  independent as that locale already keeps them: no \<open>'D = 'G\<close> constraint is threaded
  in by this locale's \<open>for\<close> clause. \<^locale>\<open>dg_ctx_activation_base\<close> itself carries
  no routing-specific content: every fact it supplies (\<open>pp_eq_bound\<close>,
  \<open>pp_sides_bound\<close>, \<open>sides_fold_le_Gen\<close>, \<open>edge_bound_local\<close>/\<open>_global\<close>,
  \<open>dg_ctx_act_edge\<close>, \<open>dg_ctx_act_comb_covered\<close>) is already generic in
  \<open>cmb\<close>/\<open>extra\<close>, so instantiating it at \<open>routed_call_tree\<close>/\<open>routed_entry_seed_tree\<close>
  reuses those proofs unchanged; only the seed-specific reasoning below, which
  \<open>dg_ctx_activation_base\<close> never has since seeding is \<open>routed_call_tree\<close>'s own
  addition, is carried out here.

  Beyond \<^locale>\<open>dg_ctx_activation_base\<close>'s parameters: \<open>seed_key\<close> injects a routed
  \<open>(pp, 'c)\<close> pair into the global-key space; \<open>enterc\<close> is the trace-semantic context
  function keying the activation-local collecting semantics; and \<open>routed_entry_cover\<close>
  is the one agreement that cannot be discharged generically: at a real call edge, some
  alternative of the specification's own entry run must describe the concrete call ---
  its continuation half containing the caller store, its entry half containing the
  entered store, and its route agreeing with the semantic \<open>enterc\<close> on that store.
  The three come from one alternative rather than three, which is what keeps a
  multi-alternative entry from mixing one alternative's continuation with another's
  callee frame. Restricting the call action to an edge of \<open>g\<close> (rather than quantifying
  over every value of the \<open>call_action\<close> type) matches how CALL and COMB below only ever
  invoke this fact at a matched edge, and keeps the obligation provable for an abstract
  domain that is exact on edges actually present in the program without being exact
  everywhere. This is a per-instance proof obligation, not a locale theorem.
\<close>

locale routed_context_base_hetero =
  dg_ctx_activation_base S gammaDG gs g gk0 route
    "routed_call_tree S gk0 seed_key resolve is_bot" "routed_entry_seed_tree seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route ("context\<^sup>#")
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and resolve :: "pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'D \<Rightarrow> pname list"
    and is_bot :: "'D \<Rightarrow> bool"
    and gammaM :: "'M \<Rightarrow> store set" +
  fixes enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes finC[intro,simp]: "finite (calls g)"
    and seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and is_bot_bot[simp]: "is_bot bot"
    and is_bot_sound: "\<And>d g. is_bot d \<Longrightarrow> gammaDG d g = {}"
    and is_bot_mono: "\<And>d d'. \<not> is_bot d \<Longrightarrow> d \<le> d' \<Longrightarrow> \<not> is_bot d'"
    and resolve_sound:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> p \<in> set (resolve cont u (CallEdge dst pars args)
                       (locals (sigma (Inl (u, ctx)))))"
    and routed_entry_cover:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> \<exists>pairs pub deps cont' entry.
             enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub
           \<and> enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs deps
           \<and> (cont', entry) \<in> set pairs
           \<and> s \<in> gammaDG cont' (globs (sigma (Inr gk0)))
           \<and> call_enter gs (CallEdge dst pars args) s
               \<in> gammaDG entry (globs (sigma (Inr gk0)))
           \<and> route u ctx entry (CallEdge dst pars args)
               = enterc u ctx (call_enter gs (CallEdge dst pars args) s)
           \<and> (FunctionEntry p, route u ctx entry (CallEdge dst pars args)) \<in> vars"
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
  One place unpacks the call's entry protocol. \<open>routed_entry_cover\<close> is a nest
  of existentials over one entry run, and both CALL and COMB need the same
  witnesses: unpacking it separately in each would let them drift onto
  \<^emph>\<open>different\<close> alternatives of the same call, which is precisely the
  correlation the pair list exists to keep.

  Invoke it with \<open>obtain\<close>; it is not an elimination rule for the classical
  reasoner.
\<close>

lemma routed_enter_witness:
  assumes covV: "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
  obtains pairs pub deps cont' entry
    where "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
             (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub"
      and "enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
             (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs deps"
      and "(cont', entry) \<in> set pairs"
      and "s \<in> gammaDG cont' (globs (sigma (Inr gk0)))"
      and "call_enter gs (CallEdge dst pars args) s
             \<in> gammaDG entry (globs (sigma (Inr gk0)))"
      and "route u ctx entry (CallEdge dst pars args)
             = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
      and "(FunctionEntry p, route u ctx entry (CallEdge dst pars args)) \<in> vars"
  using routed_entry_cover[OF covV ce sin] that by blast

text \<open>
  The alternative the eliminator hands over cannot be bottom, and no case
  distinction is needed to see it: a bottom alternative concretizes to nothing,
  while this one demonstrably contains the store the callee actually starts
  from. A bottom alternative therefore never describes a real callee execution
  --- it stays in the fold only because its combine stage may still have
  effects.
\<close>

lemma entry_cover_not_bot:
  assumes "s' \<in> gammaDG entry gv"
  shows "\<not> is_bot entry"
proof
  assume "is_bot entry"
  then have "gammaDG entry gv = {}" by (rule is_bot_sound)
  with assms show False by simp
qed

lemma le_dg_state_localsD [dest]: "d \<le> d' \<Longrightarrow> locals d \<le> locals d'"
  by (simp add: less_eq_dg_state_def)

lemma le_dg_state_globsD [dest]: "d \<le> d' \<Longrightarrow> globs d \<le> globs d'"
  by (simp add: less_eq_dg_state_def)

subsection \<open>Reaching a resolved callee's contribution\<close>

text \<open>
  A call edge reaches the generated equation in two hops: the call site's own tree is one
  of the node's trees, and the resolved callee's tree is one summand of that site's fold.
  The second hop needs a concrete store at the call site, since a resolver may drop a
  target the abstract caller state rules out; where a store exists, the edge's own callee
  survives resolution.
\<close>

lemma resolved_site_mem:
  assumes ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  shows "routed_call_tree S gk0 seed_key resolve is_bot route ctx (CallEdge dst pars args) cc cont
           \<in> set (trees cont ctx)"
proof -
  have "(cc, CallEdge dst pars args) \<in> set (call_site_list g cont)"
    using ce by (auto simp: set_call_site_list[OF finC])
  then show ?thesis by (rule routed_contribution_trees_combineI)
qed

lemma resolved_target_mem:
  assumes covV: "(cc, ctx) \<in> vars"
    and ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0)))"
  shows "routed_callee_call_tree S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
             (locals (sigma (Inl (cc, ctx)))) p
           \<in> set (map (routed_callee_call_tree S gk0 seed_key route is_bot ctx
                          (CallEdge dst pars args) cc
                        (locals (sigma (Inl (cc, ctx)))))
                      (resolve cont cc (CallEdge dst pars args)
                         (locals (sigma (Inl (cc, ctx))))))"
  using resolve_sound[OF covV ce sin] by simp

lemma resolved_at_le_site_acc:
  assumes covV: "(cc, ctx) \<in> vars"
    and ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0)))"
  shows "locals (traverse_rhs
           (routed_callee_call_tree S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma)
         \<le> side_acc_dg (acc0 cont) sigma (trees cont ctx)"
proof -
  have "locals (traverse_rhs
           (routed_callee_call_tree S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma)
      \<le> locals (traverse_rhs
           (routed_call_tree S gk0 seed_key resolve is_bot route ctx
              (CallEdge dst pars args) cc cont)
           sigma)"
    using locals_traverse_le_side_acc_dg[OF resolved_target_mem[OF covV ce sin], where acc = bot]
    by (simp add: routed_call_tree_def traverse_side_rhs_fold_dg)
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont ctx)"
    by (rule locals_traverse_le_side_acc_dg[OF resolved_site_mem[OF ce]])
  finally show ?thesis .
qed

lemma resolved_at_le_site_sides:
  assumes covV: "(cc, ctx) \<in> vars"
    and ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0)))"
  shows "sides_of_rhs
           (routed_callee_call_tree S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma z
         \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg (acc0 cont) (trees cont ctx))) sigma z"
proof -
  have "sides_of_rhs
           (routed_callee_call_tree S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma z
      \<le> sides_of_rhs
           (routed_call_tree S gk0 seed_key resolve is_bot route ctx
              (CallEdge dst pars args) cc cont)
           sigma z"
    by (rule routed_call_tree_sides_ge_at
          [where resolve = resolve and v = cont and cc = cc and ctx = ctx and \<sigma> = sigma,
           OF resolve_sound[OF covV ce sin]])
  also have "\<dots> \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg (acc0 cont) (trees cont ctx))) sigma z"
    by (rule sides_le_side_rhs_fold_dg[OF resolved_site_mem[OF ce]])
  finally show ?thesis .
qed

subsection \<open>CALL: the routed callee entry\<close>

lemma routed_seed_read_bound:
  assumes covV: "(FunctionEntry p, ctx') \<in> vars"
  shows "locals (sigma (Inr (seed_key (FunctionEntry p) ctx')))
           \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
proof -
  let ?t = "QueryG (seed_key (FunctionEntry p) ctx') (\<lambda>s. Answer (DG (locals s) bot))"
  have mem: "?t \<in> set (trees (FunctionEntry p) ctx')"
    by (rule routed_contribution_trees_extraI) (simp add: routed_entry_seed_tree_def)
  have "locals (sigma (Inr (seed_key (FunctionEntry p) ctx')))
      = locals (traverse_rhs ?t sigma)"
    by simp
  also have "\<dots> \<le> side_acc_dg (acc0 (FunctionEntry p)) sigma (trees (FunctionEntry p) ctx')"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (FunctionEntry p, ctx') sigma)"
    by (simp add: eq_routed_node_rhs)
  also have "\<dots> \<le> locals (sigma (Inl (FunctionEntry p, ctx')))"
    using pp_eq_bound[OF covV] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

text \<open>
  The published callee-entry state is bounded by the seed unknown itself, and that
  bound needs only the continuation's coverage: the seed is written by the combine
  tree living at the continuation, so nothing about the callee entry's own unknown
  enters the argument.  \<open>routed_seed_publish_bound_local\<close> adds the one further hop
  from the seed to the callee-entry local, which is where the callee's own entry
  equation reads it back, and that hop is what needs the callee entry covered.
\<close>

lemma routed_seed_publish_bound_seed:
  assumes covV: "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, ctx) \<in> vars"
    and R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
              (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub"
    and mem: "(cont', entry) \<in> set pairs"
    and nb: "\<not> is_bot entry"
  shows "entry
         \<le> locals (sigma (Inr (seed_key (FunctionEntry p)
               (route u ctx entry (CallEdge dst pars args)))))"
proof -
  let ?ctx' = "route u ctx entry (CallEdge dst pars args)"
  let ?k = "Inr (seed_key (FunctionEntry p) ?ctx')"
  let ?t = "routed_callee_call_tree S gk0 seed_key route is_bot ctx (CallEdge dst pars args) u
              (locals (sigma (Inl (u, ctx)))) p"
  have seedb: "DG entry bot \<le> sides_of_rhs ?t sigma ?k"
    using R mem nb by (rule routed_callee_call_tree_sides_ge_seed)
  have "entry \<le> locals (sides_of_rhs ?t sigma ?k)"
    using le_dg_state_localsD[OF seedb] by simp
  also have "\<dots> \<le> locals (sides_of_rhs
      (sp_compile (side_rhs_fold_dg (acc0 cont) (trees cont ctx))) sigma ?k)"
    by (rule le_dg_state_localsD[OF resolved_at_le_site_sides[OF covV ce sin]])
  also have "\<dots> \<le> locals (sides_of_rhs (Gen (cont, ctx)) sigma ?k)"
    by (rule le_dg_state_localsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> locals (sigma ?k)"
    using pp_sides_bound[OF covV_cont, THEN le_funD, of ?k]
    by (rule le_dg_state_localsD)
  finally show ?thesis .
qed

lemma routed_seed_publish_bound_local:
  assumes covV_call: "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, ctx) \<in> vars"
    and R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
              (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub"
    and mem: "(cont', entry) \<in> set pairs"
    and nb: "\<not> is_bot entry"
    and covV: "(FunctionEntry p, route u ctx entry (CallEdge dst pars args)) \<in> vars"
  shows "entry
         \<le> locals (sigma (Inl (FunctionEntry p,
               route u ctx entry (CallEdge dst pars args))))"
  by (rule order_trans
        [OF routed_seed_publish_bound_seed[OF covV_call ce sin covV_cont R mem nb]
            routed_seed_read_bound[OF covV]])

theorem routed_context_call:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaM (sg (Inl (u, ctx)))"
  shows "call_enter gs (CallEdge dst pars args) s
           \<in> gammaM (sg (Inl (FunctionEntry p,
                 enterc u ctx (call_enter gs (CallEdge dst pars args) s))))"
proof (cases "(u, ctx) \<in> vars")
  case False
  hence "gammaM (sg (Inl (u, ctx))) = {}" by (rule sg_uncov)
  thus ?thesis using sin by simp
next
  case True
  let ?g = "globs (sigma (Inr gk0))"
  have covV_cont: "(cont, ctx) \<in> vars"
    using comb_fwd[OF True ce] .
  have sin': "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) ?g"
    using sin True by (simp add: sg_cov)
  obtain pairs pub deps cont' entry
    where R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
                (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub"
      and mem: "(cont', entry) \<in> set pairs"
      and ecov: "call_enter gs (CallEdge dst pars args) s \<in> gammaDG entry ?g"
      and req: "route u ctx entry (CallEdge dst pars args)
                  = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
      and covV: "(FunctionEntry p, route u ctx entry (CallEdge dst pars args)) \<in> vars"
    by (rule routed_enter_witness[OF True ce sin'])
  let ?ctx' = "route u ctx entry (CallEdge dst pars args)"
  have nb: "\<not> is_bot entry" using ecov by (rule entry_cover_not_bot)
  have "gammaDG entry ?g \<subseteq> gammaDG (locals (sigma (Inl (FunctionEntry p, ?ctx')))) ?g"
    by (rule gammaDG_mono
          [OF routed_seed_publish_bound_local[OF True ce sin' covV_cont R mem nb covV]
              order_refl])
  also have "\<dots> = gammaM (sg (Inl (FunctionEntry p, ?ctx')))"
    using covV by (simp add: sg_cov)
  finally show ?thesis using ecov req by auto
qed

subsection \<open>COMB: the routed return combine\<close>

lemma routed_comb_bound_local:
  assumes covV: "(cl, c1) \<in> vars"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, c1) \<in> vars"
    and R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
              (mk_dg_man (locals (sigma (Inl (cl, c1)))) (\<lambda>_. gk0)) sigma pairs pub"
    and mem: "(cont', entry) \<in> set pairs"
  shows "locals (traverse_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma)
         \<le> locals (sigma (Inl (cont, c1)))"
proof -
  have "locals (traverse_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma)
      \<le> locals (traverse_rhs
           (routed_callee_call_tree S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl
              (locals (sigma (Inl (cl, c1)))) p) sigma)"
    by (rule routed_callee_call_tree_traverse_ge[OF R mem])
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont c1)"
    by (rule resolved_at_le_site_acc[OF covV ce sin])
  also have "\<dots> = locals (eq Gen (cont, c1) sigma)"
    by (simp add: eq_routed_node_rhs)
  also have "\<dots> \<le> locals (sigma (Inl (cont, c1)))"
    using pp_eq_bound[OF covV_cont] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma routed_comb_bound_global:
  assumes covV: "(cl, c1) \<in> vars"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, c1) \<in> vars"
    and R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
              (mk_dg_man (locals (sigma (Inl (cl, c1)))) (\<lambda>_. gk0)) sigma pairs pub"
    and mem: "(cont', entry) \<in> set pairs"
  shows "globs (sides_of_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma (Inr gk0))
         \<le> globs (sigma (Inr gk0))"
proof -
  have "globs (sides_of_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma (Inr gk0))
      \<le> globs (sides_of_rhs
           (routed_callee_call_tree S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl
              (locals (sigma (Inl (cl, c1)))) p) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF routed_callee_call_tree_sides_ge_combine[OF R mem]])
  also have "\<dots> \<le> globs (sides_of_rhs
      (sp_compile (side_rhs_fold_dg (acc0 cont) (trees cont c1))) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF resolved_at_le_site_sides[OF covV ce sin]])
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
  hence "gammaM (sg (Inl (cl, c1))) = {}" by (rule sg_uncov)
  thus ?thesis using s by simp
next
  case True
  let ?g = "globs (sigma (Inr gk0))"
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  have sin: "s \<in> gammaDG (locals (sigma (Inl (cl, c1)))) ?g"
    using s True by (simp add: sg_cov)
  have es_eq: "es = call_enter gs (CallEdge dst pars args) s"
    using call_enter_store_agree ces ce by blast
  obtain pairs pub deps cont' entry
    where R: "enter_runs (enter\<^sup># S ?ci)
                (mk_dg_man (locals (sigma (Inl (cl, c1)))) (\<lambda>_. gk0)) sigma pairs pub"
      and mem: "(cont', entry) \<in> set pairs"
      and ccov: "s \<in> gammaDG cont' ?g"
      and ecov: "call_enter gs (CallEdge dst pars args) s \<in> gammaDG entry ?g"
      and req: "route cl c1 entry (CallEdge dst pars args)
                  = enterc cl c1 (call_enter gs (CallEdge dst pars args) s)"
    by (rule routed_enter_witness[OF True ce sin])
  let ?ex_ctx = "route cl c1 entry (CallEdge dst pars args)"
  let ?alt = "routed_call_alternative_tree S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
                (cont', entry)"
  have nb: "\<not> is_bot entry" using ecov by (rule entry_cover_not_bot)
  have route_agree: "?ex_ctx = enterc cl c1 es" using req es_eq by simp
  show ?thesis
  proof (cases "(FunctionResult p, ?ex_ctx) \<in> vars")
    case False
    hence "gammaM (sg (Inl (FunctionResult p, ?ex_ctx))) = {}" by (rule sg_uncov)
    with route_agree have "gammaM (sg (Inl (FunctionResult p, enterc cl c1 es))) = {}" by simp
    with t show ?thesis by simp
  next
    case True
    have covV_cont: "(cont, c1) \<in> vars"
      using comb_fwd[OF \<open>(cl, c1) \<in> vars\<close> ce] .
    have tin: "t \<in> gammaDG (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g"
      using t route_agree True by (simp add: sg_cov)
    let ?sub = "sp_compile_with (\<lambda>d. DG d bot)
                  (dg_spec_combine_transfer S ?ci (mk_dg_man cont' (\<lambda>_. gk0))
                    (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))))"
    have tr: "traverse_rhs ?alt sigma = traverse_rhs ?sub sigma"
      using nb by simp
    have knk: "(Inr gk0 :: (pp \<times> 'c) + 'k) \<noteq> Inr (seed_key (FunctionEntry p) ?ex_ctx)"
      by (metis seed_key_ne_gk0 sum.inject(2))
    have sd: "sides_of_rhs ?alt sigma (Inr gk0) = sides_of_rhs ?sub sigma (Inr gk0)"
      using nb by (simp add: Let_def fun_upd_other[OF knk] del: fun_upd_apply)
    have "combine_collect gs dst s t
        \<in> gammaDG (locals (traverse_rhs ?sub sigma))
                  (globs (sides_of_rhs ?sub sigma (Inr gk0)))"
      using combine_sound[where dc = cont'
          and de = "locals (sigma (Inl (FunctionResult p, ?ex_ctx)))"
          and \<tau> = sigma and gk = gk0 and ci = ?ci, OF ccov tin]
      by simp
    also have "\<dots> = gammaDG (locals (traverse_rhs ?alt sigma))
                            (globs (sides_of_rhs ?alt sigma (Inr gk0)))"
      by (simp only: tr sd)
    also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (cont, c1)))) ?g"
      by (rule gammaDG_mono
            [OF routed_comb_bound_local[OF \<open>(cl, c1) \<in> vars\<close> ce sin covV_cont R mem]
                routed_comb_bound_global[OF \<open>(cl, c1) \<in> vars\<close> ce sin covV_cont R mem]])
    also have "\<dots> = gammaM (sg (Inl (cont, c1)))"
      using covV_cont by (simp add: sg_cov)
    finally show ?thesis .
  qed
qed


subsection \<open>An entry-local bound in the shape \<open>pp_entry_s0g_bound\<close> gives for globals\<close>

text \<open>
  The local-carrier twin of \<open>pp_entry_s0g_bound\<close> (\<^theory>\<open>Voblint_Framework.DG_Ctx_Activation\<close>),
  proved the same way: \<open>Gen\<close>'s own entry accumulator starts at \<open>bot0 \<squnion> s0d\<close>,
  \<open>side_acc_dg_ge_acc\<close> only grows it, and \<open>pp_eq_bound\<close> transports the
  bound across a covered point's post-solution equation.
\<close>

lemma locals_ge_s0d:
  assumes cov: "(cfg_entry g, ctx) \<in> vars"
  shows "s0d \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
proof -
  have "s0d \<le> locals (eq Gen (cfg_entry g, ctx) sigma)"
    by (simp add: eq_routed_node_rhs)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
    using pp_eq_bound[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

subsection \<open>Activation-collect soundness against the routed local unknown\<close>

text \<open>
  Every activation-collected store at any \<open>(v, ctx)\<close> pair is concretized by the routed
  local unknown's own \<open>gammaM\<close> reading. The four obligations of
  \<open>activation_collect_sound\<close> are this locale's own facts: the two entry bounds discharge
  \<open>INIT\<close> together, \<open>dg_ctx_act_edge\<close> is \<open>INTRA\<close>, and the CALL and COMB theorems above are
  \<open>CALL\<close> and \<open>RETURN\<close>. An instance therefore gets its activation-indexed soundness theorem
  by interpretation alone.
\<close>

lemma activation_collect_dg_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c
  assumes entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
  shows "activation_collect gs enterc initial_ctx g S0 v ctx
           \<subseteq> gammaM (sg (Inl (v, ctx)))"
proof (rule activation_collect_sound[where cover = "\<lambda>v c. gammaM (sg (Inl (v, c)))"])
  fix s0 assume s0mem: "s0 \<in> S0"
  have le_local: "s0d \<le> locals (sigma (Inl (cfg_entry g, initial_ctx)))"
    by (rule locals_ge_s0d[OF entry_cov])
  have le_global: "s0g \<le> globs (sigma (Inr gk0))"
    by (rule pp_entry_s0g_bound[OF entry_cov])
  have "gammaDG s0d s0g
        \<subseteq> gammaDG (locals (sigma (Inl (cfg_entry g, initial_ctx)))) (globs (sigma (Inr gk0)))"
    by (rule gammaDG_mono[OF le_local le_global])
  with s0mem s0_sound have "s0 \<in> gammaDG (locals (sigma (Inl (cfg_entry g, initial_ctx))))
                                   (globs (sigma (Inr gk0)))" by blast
  thus "s0 \<in> gammaM (sg (Inl (cfg_entry g, initial_ctx)))"
    using entry_cov by (simp add: sg_cov)
next
  fix u a v' c' s' s''
  assume "(u, a, v') \<in> intra g" "s' \<in> gammaM (sg (Inl (u, c')))" "s'' \<in> edge_step a s'"
  thus "s'' \<in> gammaM (sg (Inl (v', c')))" by (rule dg_ctx_act_edge)
next
  fix u dst pars args p cont c' s'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sm: "s' \<in> gammaM (sg (Inl (u, c')))"
  show "call_enter gs (CallEdge dst pars args) s'
          \<in> gammaM
              (sg (Inl (FunctionEntry p, enterc u c' (call_enter gs (CallEdge dst pars args) s'))))"
    using routed_context_call[OF ce sm] .
next
  fix cl dst pars args p cont c1 s' t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sm: "s' \<in> gammaM (sg (Inl (cl, c1)))"
    and tm: "t \<in> gammaM (sg (Inl (FunctionResult p, enterc cl c1 es)))"
    and ces: "call_enter_store gs g cl s' es"
  show "combine_collect gs dst s' t \<in> gammaM (sg (Inl (cont, c1)))"
    using tm routed_context_comb[OF ce sm _ ces] by blast
qed

end


subsection \<open>Formal-entry contexts: routing on the callee's declared formals\<close>

text \<open>
  A context type derived from the callee's declared formals rather than call-site
  history: \<open>'a list\<close>, one abstract value per formal, in the order \<^const>\<open>CallEdge\<close>
  already carries them --- populated at compile time from the callee's own
  declaration, so no separate procedure-table lookup is needed here.
  \<open>formals_context\<close> is the plain per-variable projection (\<^typ>\<open>'a abs_state\<close> is
  \<^typ>\<open>vname \<Rightarrow> 'a\<close>, so this is just \<^const>\<open>map\<close>), and the routing functions
  below apply it to the state they are handed. That state is already the
  \<^emph>\<open>entered\<close> callee frame:
  \<^const>\<open>routed_callee_call_tree\<close> runs the specification's own enter transfer first and
  passes its answer to \<open>route\<close>, so a routing function must not enter again.
  \<open>formals_context_sem\<close> is the trace-semantic counterpart, decoding the concrete
  entered store's formals the same way, given the point abstraction \<open>decode\<close> a
  domain provides for a concrete value and the CFG needed to look up a call
  site's own formal list. Neither definition mentions a domain-specific accessor
  beyond \<open>decode\<close> itself, nor a specification, so any domain reusing
  \<^locale>\<open>routed_context_base_hetero\<close> instantiates this pair once instead of
  hand-writing a per-formal projection.
\<close>

definition formals_context :: "vname list \<Rightarrow> 'a abs_state \<Rightarrow> 'a list" where
  "formals_context pars d = map d pars"

text \<open>The formals of the call originating at \<open>u\<close>: at most one, by the compiler's
  own invariant (\<open>Voblint_Compile.VIMP_Proc_to_CFG\<close> emits a single \<^const>\<open>CallEdge\<close>
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
  The callee's own entry node at the same call site, so a caller lacking any
  \<^typ>\<open>pname\<close> of its own (only the \<^type>\<open>call_action\<close>) can still reconstruct a
  \<^type>\<open>call_info\<close> via \<^const>\<open>call_info_of\<close>. Same head-of-filtered-list convention
  as \<^const>\<open>call_action_at_call_site\<close>, over the third tuple component instead of
  the second.
\<close>

definition callee_entry_at_call_site :: "cfg \<Rightarrow> pp \<Rightarrow> pp" where
  "callee_entry_at_call_site g u =
     (case filter (\<lambda>(c, ca, ce, k). c = u) (cfg_calls_list g) of
        (_, _, ce, _) # _ \<Rightarrow> ce
      | _ \<Rightarrow> FunctionEntry undefined)"

text \<open>
  Not a locale theorem, same as routing agreement itself: whether a node has at
  most one outgoing call is a per-instance fact about \<open>g\<close>, true for
  \<open>compile_prog\<close> output (\<open>Voblint_Compile.VIMP_Proc_to_CFG\<close>'s
  \<open>compile_prog_calls_source_unique\<close>) but not for an arbitrary hand-built CFG.
\<close>

lemma calls_filter_singleton:
  assumes fin: "finite (calls g)"
    and uniq: "\<And>ca1 ce1 af1 ca2 ce2 af2.
                 (u, ca1, ce1, af1) \<in> calls g \<Longrightarrow> (u, ca2, ce2, af2) \<in> calls g
                 \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
    and ce: "(u, ca, cf, af) \<in> calls g"
  shows "filter (\<lambda>(c, ca, ce, k). c = u) (cfg_calls_list g) = [(u, ca, cf, af)]"
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
  ultimately show ?thesis
    apply (cases "filter (\<lambda>(c, ca, ce, k). c = u) (cfg_calls_list g)")
    using singleton_iff subset_singletonD by(fastforce)+
qed

lemma call_action_at_call_site_eq:
  assumes fin: "finite (calls g)"
    and uniq: "\<And>ca1 ce1 af1 ca2 ce2 af2.
                 (u, ca1, ce1, af1) \<in> calls g \<Longrightarrow> (u, ca2, ce2, af2) \<in> calls g
                 \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
    and ce: "(u, ca, cf, af) \<in> calls g"
  shows "call_action_at_call_site g u = ca"
  unfolding call_action_at_call_site_def
  using calls_filter_singleton[OF fin uniq ce] by simp

lemma callee_entry_at_call_site_eq:
  assumes fin: "finite (calls g)"
    and uniq: "\<And>ca1 ce1 af1 ca2 ce2 af2.
                 (u, ca1, ce1, af1) \<in> calls g \<Longrightarrow> (u, ca2, ce2, af2) \<in> calls g
                 \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
    and ce: "(u, ca, cf, af) \<in> calls g"
  shows "callee_entry_at_call_site g u = cf"
  unfolding callee_entry_at_call_site_def
  using calls_filter_singleton[OF fin uniq ce] by simp

subsection \<open>Formal-entry contexts at the routed spine's lifted carrier\<close>

text \<open>
  \<^const>\<open>formals_context\<close> above operates on the unlifted
  \<^typ>\<open>'a abs_state\<close>, the shape an abstract-carrier \<^locale>\<open>routed_context_base_hetero\<close> caller state
  has. The routed executable spine (\<^locale>\<open>dg_ctx_activation_base\<close>, every current
  instance) instead carries \<^typ>\<open>'a abs_state lifted\<close> throughout, to represent an
  activation the solver has not yet covered. \<open>formals_route_lifted\<close>/
  \<open>formals_route_lifted_gen\<close> are the same formal-entry projection at that carrier:
  a caller point that is \<^const>\<open>Bot\<close> routes to the all-\<open>bot\<close> formal context (the
  entered callee frame is then \<^const>\<open>Bot\<close> too), the same collapse an EntryState
  routed instance needs for its own executable/abstract route. Like the
  projection above, these read the state they are handed and never re-enter, so
  neither mentions a specification.
\<close>

definition formals_route_lifted ::
  "'a::sound_domain abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route_lifted d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0))"

definition formals_route_lifted_gen ::
  "pp \<Rightarrow> 'a list \<Rightarrow> 'a::sound_domain abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route_lifted_gen u ctx d ca = formals_route_lifted d ca"

subsection \<open>A solved-table \<open>enterc\<close> agrees with any \<open>route\<close> reading the same table\<close>

text \<open>
  \<open>routed_entry_cover\<close> (\<^locale>\<open>routed_context_base_hetero\<close>) asks for a trace-semantic
  \<open>enterc\<close> agreeing with the executable \<open>route\<close> on every matched call. When \<open>route\<close>
  is state-dependent (unlike \<open>route_unit\<close> or \<open>cs_route\<close>, both of which ignore their
  state argument outright and so satisfy this for any \<open>enterc\<close> built the
  same way), the natural \<open>enterc\<close> recomputes \<open>route\<close> from the caller's own solved
  table instead of decoding the concrete entered store: \<open>route_enterc_of_sigma\<close>
  ignores its store argument \<open>s\<close> entirely and reads \<open>route\<close> at the caller's own
  \<open>sigma\<close>-recorded local value and the one \<^const>\<open>call_action_at_call_site\<close> a
  well-formed compiled program's own call-site uniqueness (\<open>compile_prog_calls_source_unique\<close>)
  guarantees. \<open>route_enterc_of_sigma_agree\<close> then discharges that agreement for
  \<^emph>\<open>any\<close> \<open>route\<close>, generically: the two sides differ only in which \<^type>\<open>call_action\<close>
  they pass to \<open>route\<close> (the matched call edge vs. \<^const>\<open>call_action_at_call_site\<close>'s own
  read), and \<open>call_action_at_call_site_eq\<close> identifies those under the same
  uniqueness premise.
\<close>

definition route_enterc_of_sigma ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
     \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D)
     \<Rightarrow> (pp \<times> 'c + 'k \<Rightarrow> ('D::bounded_semilattice_sup_bot,
                            'G::bounded_semilattice_sup_bot) dg_state)
     \<Rightarrow> cfg \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
where
  "route_enterc_of_sigma route en sigma g u ctx s =
     (let ca = call_action_at_call_site g u;
          p = (case callee_entry_at_call_site g u of FunctionEntry q \<Rightarrow> q | _ \<Rightarrow> undefined)
      in route u ctx (en (call_info_of ca p) (locals (sigma (Inl (u, ctx))))) ca)"

text \<open>
  The premise \<open>ent\<close> is the restriction, and it is deliberately explicit rather
  than folded into the definition: this \<open>enterc\<close> can only be built where the call
  has \<^emph>\<open>one\<close> alternative, since it must answer a single context for a concrete
  store and several alternatives may route to several. That is exactly the case
  every context instance in the tree is in, and stating it here keeps a
  multi-alternative instance from silently inheriting a context function that
  cannot describe it.
\<close>

lemma route_enterc_of_sigma_agree:
  assumes fin: "finite (calls g)"
    and uniq: "\<And>ca1 ce1 af1 ca2 ce2 af2.
                 (u, ca1, ce1, af1) \<in> calls g \<Longrightarrow> (u, ca2, ce2, af2) \<in> calls g
                 \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ent: "entry = en (call_info_of (CallEdge dst pars args) p)
                        (locals (sigma (Inl (u, ctx))))"
  shows "route u ctx entry (CallEdge dst pars args)
       = route_enterc_of_sigma route en sigma g u ctx s"
  unfolding route_enterc_of_sigma_def
  using call_action_at_call_site_eq[OF fin uniq ce] callee_entry_at_call_site_eq[OF fin uniq ce]
        ent
  by (simp add: Let_def)

end
