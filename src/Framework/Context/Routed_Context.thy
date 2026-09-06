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
  \<open>(pp, 'c)\<close> pair into the global-key space; \<open>R\<close> is the trace-semantic context relation
  keying the activation-local collecting semantics; and two obligations about it cannot be
  discharged generically.  \<open>routed_entry_cover\<close> is adequacy: whenever \<open>R\<close> admits a context
  for a real call edge and a covered caller store, some alternative of the specification's
  own entry run describes that call --- its continuation half containing the caller store,
  its entry half containing the entered store, and its route being exactly the admitted
  context.  The three come from one alternative rather than three, which is what keeps a
  multi-alternative entry from mixing one alternative's continuation with another's callee
  frame.  \<open>routed_entry_total\<close> is existence: every covered call admits some context.
  Restricting both to an edge of \<open>g\<close> (rather than quantifying over every value of the
  \<open>call_action\<close> type) matches how CALL and COMB below only ever invoke them at a matched
  edge, and keeps the obligations provable for an abstract domain that is exact on edges
  actually present in the program without being exact everywhere.  These are per-instance
  proof obligations, not locale theorems.

  \<open>calls_unique\<close> ties the edge a return reads to the edge its callee was entered through;
  the collecting semantics itself never needs it, and compiled programs have it for free.
\<close>

locale routed_context_base_hetero =
  dg_ctx_activation_base S gammaDG gs g gk0 route
    "routed_call_tree S gk0 seed_key resolve is_bot" "routed_entry_seed_tree seed_key"
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
  fixes R :: "'c call_context_rel"
  assumes finC: "finite (calls g)"
    and calls_unique: "calls_source_unique g"
    and seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and is_bot_bot[simp]: "is_bot bot"
    and is_bot_sound: "\<And>d g. is_bot d \<Longrightarrow> gammaDG d g = {}"
    and resolve_sound:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> p \<in> set (resolve cont u (CallEdge dst pars args)
                       (locals (sigma (Inl (u, ctx)))))"
    and routed_entry_cover:
    "\<And>u ctx dst pars args p cont s ctx'.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) p) s
             (call_enter gs (CallEdge dst pars args) s) ctx'
       \<Longrightarrow> \<exists>pairs pub deps cont' entry.
             enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub
           \<and> enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs deps
           \<and> (cont', entry) \<in> set pairs
           \<and> s \<in> gammaDG cont' (globs (sigma (Inr gk0)))
           \<and> call_enter gs (CallEdge dst pars args) s
               \<in> gammaDG entry (globs (sigma (Inr gk0)))
           \<and> route u ctx entry (CallEdge dst pars args) = ctx'
           \<and> (FunctionEntry p, ctx') \<in> vars"
    and routed_entry_total:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) p) s
                     (call_enter gs (CallEdge dst pars args) s) ctx'"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (cont, c1) \<in> vars"
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
    and Rc: "R u ctx (call_info_of (CallEdge dst pars args) p) s
               (call_enter gs (CallEdge dst pars args) s) ctx'"
  obtains pairs pub deps cont' entry
    where "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
             (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub"
      and "enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
             (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs deps"
      and "(cont', entry) \<in> set pairs"
      and "s \<in> gammaDG cont' (globs (sigma (Inr gk0)))"
      and "call_enter gs (CallEdge dst pars args) s
             \<in> gammaDG entry (globs (sigma (Inr gk0)))"
      and "route u ctx entry (CallEdge dst pars args) = ctx'"
      and "(FunctionEntry p, ctx') \<in> vars"
  using routed_entry_cover[OF covV ce sin Rc] that by blast

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

lemma le_dg_state_localsD: "d \<le> d' \<Longrightarrow> locals d \<le> locals d'"
  by (simp add: less_eq_dg_state_def)

lemma le_dg_state_globsD: "d \<le> d' \<Longrightarrow> globs d \<le> globs d'"
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

text \<open>The CALL obligation, ending in \<open>routed_context_call\<close>: the store a call hands the callee
  is covered by the callee entry read at the routed context.  The bound does not go there
  directly.  It goes through the seed unknown, which is the only place the caller's own tree
  and the callee's entry equation meet.\<close>
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
    and Rc: "R u ctx (call_info_of (CallEdge dst pars args) p) s
               (call_enter gs (CallEdge dst pars args) s) ctx'"
  shows "call_enter gs (CallEdge dst pars args) s \<in> gammaM (sg (Inl (FunctionEntry p, ctx')))"
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
    using sin True by simp
  obtain pairs pub deps cont' entry
    where Rr: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
                (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs pub"
      and D: "enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
                (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. gk0)) sigma pairs deps"
      and mem: "(cont', entry) \<in> set pairs"
      and ecov: "call_enter gs (CallEdge dst pars args) s \<in> gammaDG entry ?g"
      and req: "route u ctx entry (CallEdge dst pars args) = ctx'"
      and covV: "(FunctionEntry p, ctx') \<in> vars"
    by (rule routed_enter_witness[OF True ce sin' Rc])
  let ?ctx' = "route u ctx entry (CallEdge dst pars args)"
  have nb: "\<not> is_bot entry" using ecov by (rule entry_cover_not_bot)
  have "gammaDG entry ?g \<subseteq> gammaDG (locals (sigma (Inl (FunctionEntry p, ?ctx')))) ?g"
    by (rule gammaDG_mono
          [OF routed_seed_publish_bound_local[OF True ce sin' covV_cont Rr mem nb covV[folded req]]
              order_refl])
  also have "\<dots> = gammaM (sg (Inl (FunctionEntry p, ?ctx')))"
    using covV[folded req] by simp
  finally show ?thesis using ecov req by auto
qed

subsection \<open>COMB: the routed return combine\<close>

text \<open>The COMB obligation, ending in \<open>routed_context_comb\<close>: the state a return combines is
  covered by the continuation read at the caller's own context.  The return takes one
  alternative among those the enter step produced, so the work is to bound that single
  alternative -- once locally, once at the global key -- against what the continuation's
  unknown already holds.\<close>
lemma routed_comb_bound_local:
  assumes covV: "(cl, c1) \<in> vars"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, c1) \<in> vars"
    and R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
              (mk_dg_man (locals (sigma (Inl (cl, c1)))) (\<lambda>_. gk0)) sigma pairs pub"
    and mem: "(cont', entry) \<in> set pairs"
  shows "locals (traverse_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1
              (CallEdge dst pars args) cl p (cont', entry)) sigma)
         \<le> locals (sigma (Inl (cont, c1)))"
proof -
  have "locals (traverse_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1
              (CallEdge dst pars args) cl p (cont', entry)) sigma)
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
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1
              (CallEdge dst pars args) cl p (cont', entry)) sigma (Inr gk0))
         \<le> globs (sigma (Inr gk0))"
proof -
  have "globs (sides_of_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot c1
              (CallEdge dst pars args) cl p (cont', entry)) sigma (Inr gk0))
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
    and adm: "admits_call_context gs g R cl c1 p' s es ctx'"
    and t: "t \<in> gammaM (sg (Inl (FunctionResult p, ctx')))"
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
    using s True by simp
  \<comment> \<open>The callee was entered along some edge out of \<open>cl\<close>; call-source uniqueness makes it
      the edge the return reads.\<close>
  from adm obtain dst2 pars2 args2 cont2
    where e2: "(cl, CallEdge dst2 pars2 args2, FunctionEntry p', cont2) \<in> calls g"
      and es_eq: "es = call_enter gs (CallEdge dst2 pars2 args2) s"
      and Rc2: "R cl c1 (call_info_of (CallEdge dst2 pars2 args2) p') s es ctx'"
    by (rule admits_call_contextE)
  have same: "CallEdge dst2 pars2 args2 = CallEdge dst pars args" and pp': "p' = p"
    using calls_source_unique_edgesD(1,2)[OF calls_unique e2 ce] by simp_all
  have Rc: "R cl c1 ?ci s (call_enter gs (CallEdge dst pars args) s) ctx'"
    using Rc2 unfolding es_eq same pp' .
  obtain pairs pub deps cont' entry
    where Rr: "enter_runs (enter\<^sup># S ?ci)
                (mk_dg_man (locals (sigma (Inl (cl, c1)))) (\<lambda>_. gk0)) sigma pairs pub"
      and D: "enter_deps (enter\<^sup># S ?ci)
                (mk_dg_man (locals (sigma (Inl (cl, c1)))) (\<lambda>_. gk0)) sigma pairs deps"
      and mem: "(cont', entry) \<in> set pairs"
      and ccov: "s \<in> gammaDG cont' ?g"
      and ecov: "call_enter gs (CallEdge dst pars args) s \<in> gammaDG entry ?g"
      and req: "route cl c1 entry (CallEdge dst pars args) = ctx'"
    by (rule routed_enter_witness[OF True ce sin Rc])
  let ?ex_ctx = "route cl c1 entry (CallEdge dst pars args)"
  let ?alt = "routed_call_alternative_tree S gk0 seed_key route is_bot c1
                (CallEdge dst pars args) cl p (cont', entry)"
  have nb: "\<not> is_bot entry" using ecov by (rule entry_cover_not_bot)
  show ?thesis
  proof (cases "(FunctionResult p, ?ex_ctx) \<in> vars")
    case False
    hence "gammaM (sg (Inl (FunctionResult p, ?ex_ctx))) = {}" by (rule sg_uncov)
    with req have "gammaM (sg (Inl (FunctionResult p, ctx'))) = {}" by simp
    with t show ?thesis by simp
  next
    case True
    have covV_cont: "(cont, c1) \<in> vars"
      using comb_fwd[OF \<open>(cl, c1) \<in> vars\<close> ce] .
    have tin: "t \<in> gammaDG (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g"
      using t req True by simp
    let ?sub = "sp_compile_with (\<lambda>d. DG d bot)
                  (dg_spec_combine_transfer S ?ci (mk_dg_man cont' (\<lambda>_. gk0))
                    (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))))"
    have tr: "traverse_rhs ?alt sigma = traverse_rhs ?sub sigma"
      using nb by simp
    have knk: "(Inr gk0 :: (pp \<times> 'c) + 'k) \<noteq> Inr (seed_key (FunctionEntry p) ?ex_ctx)"
      by (rule not_sym) simp
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
            [OF routed_comb_bound_local[OF \<open>(cl, c1) \<in> vars\<close> ce sin covV_cont Rr mem]
                routed_comb_bound_global[OF \<open>(cl, c1) \<in> vars\<close> ce sin covV_cont Rr mem]])
    also have "\<dots> = gammaM (sg (Inl (cont, c1)))"
      using covV_cont by simp
    finally show ?thesis .
  qed
qed


subsection \<open>Activation-collect soundness against the routed local unknown\<close>

text \<open>
  Every activation-collected store at any \<open>(v, ctx)\<close> pair is concretized by the routed
  local unknown's own \<open>gammaM\<close> reading. The five obligations of
  \<open>activation_collect_sound\<close> are this locale's own facts: the two entry bounds discharge
  \<open>INIT\<close> together, \<open>dg_ctx_act_edge\<close> is \<open>INTRA\<close>, the CALL and COMB theorems above are
  \<open>CALL\<close> and \<open>RETURN\<close>, and \<open>routed_entry_total\<close> read through the reader is \<open>TOTAL\<close>. An
  instance therefore gets its activation-indexed soundness theorem by interpretation alone.
\<close>

lemma routed_call_context_total:
  "call_context_total_on (\<lambda>v c. gammaM (sg (Inl (v, c)))) R gs g"
  unfolding call_context_total_on_def
proof (intro allI impI)
  fix u dst pars args p cont ctx s
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaM (sg (Inl (u, ctx)))"
  have covV: "(u, ctx) \<in> vars"
  proof (rule ccontr)
    assume "(u, ctx) \<notin> vars"
    then have "gammaM (sg (Inl (u, ctx))) = {}" by (rule sg_uncov)
    with sin show False by simp
  qed
  with sin have "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))" by simp
  from routed_entry_total[OF covV ce this]
  show "\<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) p) s
                 (call_enter gs (CallEdge dst pars args) s) ctx'" .
qed

lemma activation_collect_dg_sound:
  fixes S0 :: "store set" and startcontext :: 'c
  assumes entry_cov: "(cfg_entry g, startcontext) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
  shows "activation_collect gs R startcontext g S0 v ctx
           \<subseteq> gammaM (sg (Inl (v, ctx)))"
proof (rule activation_collect_sound[where cover = "\<lambda>v c. gammaM (sg (Inl (v, c)))"])
  fix s0 assume s0mem: "s0 \<in> S0"
  have le_local: "s0d \<le> locals (sigma (Inl (cfg_entry g, startcontext)))"
    by (rule pp_entry_s0d_bound[OF entry_cov])
  have le_global: "s0g \<le> globs (sigma (Inr gk0))"
    by (rule pp_entry_s0g_bound[OF entry_cov])
  have "gammaDG s0d s0g
        \<subseteq> gammaDG (locals (sigma (Inl (cfg_entry g, startcontext)))) (globs (sigma (Inr gk0)))"
    by (rule gammaDG_mono[OF le_local le_global])
  with s0mem s0_sound have "s0 \<in> gammaDG (locals (sigma (Inl (cfg_entry g, startcontext))))
                                   (globs (sigma (Inr gk0)))" by blast
  thus "s0 \<in> gammaM (sg (Inl (cfg_entry g, startcontext)))"
    using entry_cov by simp
next
  fix u a v' c' s' s''
  assume "(u, a, v') \<in> intra g" "s' \<in> gammaM (sg (Inl (u, c')))" "s'' \<in> edge_step a s'"
  thus "s'' \<in> gammaM (sg (Inl (v', c')))" by (rule dg_ctx_act_edge)
next
  fix u dst pars args p cont c' c'' s'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sm: "s' \<in> gammaM (sg (Inl (u, c')))"
    and Rc: "R u c' (call_info_of (CallEdge dst pars args) p) s'
               (call_enter gs (CallEdge dst pars args) s') c''"
  show "call_enter gs (CallEdge dst pars args) s' \<in> gammaM (sg (Inl (FunctionEntry p, c'')))"
    using routed_context_call[OF ce sm Rc] .
next
  fix cl dst pars args p cont c1 c' p' s' t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sm: "s' \<in> gammaM (sg (Inl (cl, c1)))"
    and adm: "admits_call_context gs g R cl c1 p' s' es c'"
    and tm: "t \<in> gammaM (sg (Inl (FunctionResult p, c')))"
  show "combine_collect gs dst s' t \<in> gammaM (sg (Inl (cont, c1)))"
    using routed_context_comb[OF ce sm adm tm] .
next
  show "call_context_total_on (\<lambda>v c. gammaM (sg (Inl (v, c)))) R gs g"
    by (rule routed_call_context_total)
qed

text \<open>
  Every valid trace of a covered program carries some context under this instance's own
  \<open>R\<close>: the same four EDGE/CALL/COMB/TOTAL facts that bound the buckets above also make
  \<open>ltr_coverage\<close> total here, so a \<open>Source_Ctx\<close>-style example can discharge the
  \<open>has_ctx\<close> premise \<open>source_sound_from_collecting_cap\<close> asks for without restating the
  interpretation itself.
\<close>

lemma routed_valid_ltr_has_context:
  fixes S0 :: "store set" and startcontext :: 'c
  assumes entry_cov: "(cfg_entry g, startcontext) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
    and tv: "t \<in> valid_ltr gs g S0"
  shows "\<exists>c. trace_context gs R startcontext g t c"
proof -
  interpret G: ltr_coverage g S0 "\<lambda>v c. gammaM (sg (Inl (v, c)))" R startcontext gs
  proof unfold_locales
    fix s0 assume s0mem: "s0 \<in> S0"
    have le_local: "s0d \<le> locals (sigma (Inl (cfg_entry g, startcontext)))"
      by (rule pp_entry_s0d_bound[OF entry_cov])
    have le_global: "s0g \<le> globs (sigma (Inr gk0))"
      by (rule pp_entry_s0g_bound[OF entry_cov])
    have "gammaDG s0d s0g
          \<subseteq> gammaDG (locals (sigma (Inl (cfg_entry g, startcontext)))) (globs (sigma (Inr gk0)))"
      by (rule gammaDG_mono[OF le_local le_global])
    with s0mem s0_sound have "s0 \<in> gammaDG (locals (sigma (Inl (cfg_entry g, startcontext))))
                                     (globs (sigma (Inr gk0)))" by blast
    thus "s0 \<in> gammaM (sg (Inl (cfg_entry g, startcontext)))"
      using entry_cov by simp
  next
    fix u a v' c' s' s''
    assume "(u, a, v') \<in> intra g" "s' \<in> gammaM (sg (Inl (u, c')))" "s'' \<in> edge_step a s'"
    thus "s'' \<in> gammaM (sg (Inl (v', c')))" by (rule dg_ctx_act_edge)
  next
    fix u dst pars args p cont c' c'' s'
    assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
      and sm: "s' \<in> gammaM (sg (Inl (u, c')))"
      and Rc: "R u c' (call_info_of (CallEdge dst pars args) p) s'
                 (call_enter gs (CallEdge dst pars args) s') c''"
    show "call_enter gs (CallEdge dst pars args) s' \<in> gammaM (sg (Inl (FunctionEntry p, c'')))"
      using routed_context_call[OF ce sm Rc] .
  next
    fix cl dst pars args p cont c1 c' p' s' t es
    assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
      and sm: "s' \<in> gammaM (sg (Inl (cl, c1)))"
      and adm: "admits_call_context gs g R cl c1 p' s' es c'"
      and tm: "t \<in> gammaM (sg (Inl (FunctionResult p, c')))"
    show "combine_collect gs dst s' t \<in> gammaM (sg (Inl (cont, c1)))"
      using routed_context_comb[OF ce sm adm tm] .
  next
    show "call_context_total_on (\<lambda>v c. gammaM (sg (Inl (v, c)))) R gs g"
      by (rule routed_call_context_total)
  qed
  show ?thesis using G.valid_ltr_has_context[OF tv] by blast
qed

end


subsection \<open>The context relation a solved entry-state table induces\<close>

text \<open>
  A state-dependent policy picks a context from an abstract entry value, and a pure entry
  answers a list of them, so one concrete call may be routed to several contexts --- one
  per alternative whose continuation covers the caller store and whose entry covers the
  entered store.  \<open>routed_entry_context_rel alts\<close> is exactly that set, for an entry
  operation whose alternatives are the pure function \<open>alts\<close> of the call information and the
  caller's solved local value: it admits \<open>ctx'\<close> whenever some alternative has those two
  coverings and its \<open>route\<close> is \<open>ctx'\<close>.  Stated as an equivalence, both routed obligations
  come for free: adequacy is the definition read forwards, and totality is the alternatives
  covering the concrete call at all, which is what \<^const>\<open>entry_pairs_cover\<close> says.  No
  decoder of the concrete store is involved: the context is induced by the analyzer's own
  decision, as Goblint's \<open>context\<close> applied to each \<open>enter\<close> alternative induces it.

  The relation is stated over \<open>alts\<close> rather than over an arbitrary entry run because a run
  does not determine its alternative list in general --- over a one-point carrier every
  list traverses alike --- while a pure entry's list is the function's own answer.
\<close>

definition routed_entry_context_rel ::
  "(call_info \<Rightarrow> 'D \<Rightarrow> 'D enter_result list)
     \<Rightarrow> ('D \<Rightarrow> 'G \<Rightarrow> store set) \<Rightarrow> (pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state) \<Rightarrow> 'k
     \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c call_context_rel"
where
  "routed_entry_context_rel alts gammaDG sigma gk0 route u ctx ci caller entered ctx' \<longleftrightarrow>
     (\<exists>cont entry.
        (cont, entry) \<in> set (alts ci (locals (sigma (Inl (u, ctx)))))
      \<and> caller \<in> gammaDG cont (globs (sigma (Inr gk0)))
      \<and> entered \<in> gammaDG entry (globs (sigma (Inr gk0)))
      \<and> ctx' = route u ctx entry (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)))"

lemma routed_entry_context_relI:
  assumes "(cont, entry) \<in> set (alts ci (locals (sigma (Inl (u, ctx)))))"
    and "caller \<in> gammaDG cont (globs (sigma (Inr gk0)))"
    and "entered \<in> gammaDG entry (globs (sigma (Inr gk0)))"
  shows "routed_entry_context_rel alts gammaDG sigma gk0 route u ctx ci caller entered
           (route u ctx entry (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)))"
  using assms unfolding routed_entry_context_rel_def by blast

text \<open>Invoke with \<open>obtain\<close>: the alternative is a witness the classical reasoner should not
  be left to guess.\<close>
lemma routed_entry_context_relE:
  assumes "routed_entry_context_rel alts gammaDG sigma gk0 route u ctx ci caller entered ctx'"
  obtains cont entry
    where "(cont, entry) \<in> set (alts ci (locals (sigma (Inl (u, ctx)))))"
      and "caller \<in> gammaDG cont (globs (sigma (Inr gk0)))"
      and "entered \<in> gammaDG entry (globs (sigma (Inr gk0)))"
      and "ctx' = route u ctx entry (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci))"
  using assms unfolding routed_entry_context_rel_def by blast

text \<open>Totality is the alternatives covering the concrete call: exactly the
  \<^const>\<open>entry_pairs_cover\<close> obligation every routed instance already carries.\<close>
lemma routed_entry_context_rel_total:
  assumes "entry_pairs_cover (\<lambda>d. gammaDG d (globs (sigma (Inr gk0)))) caller entered
             (alts ci (locals (sigma (Inl (u, ctx)))))"
  shows "\<exists>ctx'. routed_entry_context_rel alts gammaDG sigma gk0 route u ctx ci caller entered ctx'"
  using assms unfolding routed_entry_context_rel_def
  by blast


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
    then have memx: "x \<in> set ?L" and px: "?P x" by auto
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


end
