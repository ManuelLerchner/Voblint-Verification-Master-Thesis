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
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>), so \<open>routed_cmb S gk0\<close>, closing over only the
  spec and the shared slot, is the value that instantiates \<open>cmb\<close>.\<close>
definition routed_cmb ::
  "('d::bounded_semilattice_sup_bot, 'd) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'd) dg_state) strategy_tree"
where
  "routed_cmb S gk0 route ctx ca cc ex =
     with_call ca (\<lambda>dst _ _. do {
       caller_state \<leftarrow> read_local (cc, ctx);
       let ctx' = route cc ctx (locals caller_state) ca;
       callee_state \<leftarrow> read_local (ex, ctx');
       globals_state \<leftarrow> read_global gk0;
       let caller = locals caller_state;
       let callee = locals callee_state;
       let globals = globs globals_state;
       publish_global gk0 (combine_global S dst caller callee globals);
       answer_local (combine_local S dst caller callee globals)
     })"

text \<open>Per node \<open>v\<close>: if \<open>v\<close> is a callee entry, read back its own routed seed; for every
  outgoing call from \<open>v\<close>, publish the entered store into the callee's routed seed slot,
  reading the shared global \<open>gk0\<close> the same way \<^const>\<open>routed_cmb\<close> does. The seed key is
  injected through an arbitrary \<open>seed_key\<close> function rather than fixed to any particular
  global-key type, so the same shape serves any routing policy.\<close>
definition routed_extra ::
  "cfg \<Rightarrow> ('d::bounded_semilattice_sup_bot, 'd) dg_spec
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'd) dg_state) strategy_tree list"
where
  "routed_extra g S seed_key gk0 route ctx v =
     (case v of FunctionEntry _ \<Rightarrow>
        [do { seed_state \<leftarrow> read_global (seed_key v ctx); answer_local (globs seed_state) }]
       | _ \<Rightarrow> [])
     @ map (\<lambda>(w, ca, k).
             with_call ca (\<lambda>dst fs as. do {
               entry_state \<leftarrow> read_local (v, ctx);
               globals_state \<leftarrow> read_global gk0;
               let entry = locals entry_state;
               let globals = globs globals_state;
               publish_global gk0 (enter_global S fs as entry globals);
               publish_seed (seed_key w (route v ctx entry ca))
                 (enter_local S fs as entry globals);
               answer_local bot
             }))
           (call_successor_list g v)"

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

locale routed_context =
  dg_ctx_activation S gs g gk0 route "routed_cmb S gk0" "routed_extra g S seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg
  for S :: "('a::sound_domain abs_state, 'a abs_state) dg_spec"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0 route bot0 s0d s0g sigma vars x0 sg
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

text \<open>Split into the two componentwise bounds \<open>gamma_unit_mono\<close>/\<open>combine_abs\<close> routing
  needs, instead of one bound against the raw join: the local answer's own bound never
  mentions \<open>gk0\<close>, and the global publication's own bound never mentions the routed seed
  key at all, so each is proved (and usable) independently of the other.\<close>
lemma routed_seed_publish_bound_local:
  assumes ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and covU: "(u, ctx) \<in> vars"
    and covV: "(FunctionEntry p,
                 route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)) \<in> vars"
  shows "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (FunctionEntry p,
               route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))))"
proof -
  let ?ctx' = "route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)"
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side gk0 (DG bot (fst (dgs_enter S pars args (locals d) (globs gv))))
                (Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                  (DG bot (snd (dgs_enter S pars args (locals d) (globs gv))))
                  (Answer (DG bot bot)))))"
  have succ: "(FunctionEntry p, CallEdge dst pars args, cont) \<in> set (call_successor_list g u)"
    using ce by (simp add: set_call_successor_list[OF finC] call_successors_iff)
  have mem: "?t \<in> set (trees u ctx)"
    unfolding routed_extra_def Let_def using succ by (force intro: rev_image_eqI)
  have snd_bound:
    "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
       \<le> globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
  proof -
    have "snd (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
        = globs (sides_of_rhs ?t sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (simp add: seed_key_ne_gk0)
    also have "\<dots> \<le> globs (sides_of_rhs
        (side_rhs_fold_dg (acc0 u) (trees u ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
    also have "\<dots> \<le> globs (sides_of_rhs (Gen (u, ctx)) sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
    also have "\<dots> \<le> globs (sigma (Inr (seed_key (FunctionEntry p) ?ctx')))"
      using pp_sides_bound[OF covU, THEN le_funD, of "Inr (seed_key (FunctionEntry p) ?ctx')"]
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
    and covU: "(u, ctx) \<in> vars"
  shows "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
           \<le> globs (sigma (Inr gk0))"
proof -
  let ?t = "QueryL (u, ctx) (\<lambda>d. QueryG gk0 (\<lambda>gv.
              Side gk0 (DG bot (fst (dgs_enter S pars args (locals d) (globs gv))))
                (Side (seed_key (FunctionEntry p) (route u ctx (locals d) (CallEdge dst pars args)))
                  (DG bot (snd (dgs_enter S pars args (locals d) (globs gv))))
                  (Answer (DG bot bot)))))"
  have succ: "(FunctionEntry p, CallEdge dst pars args, cont) \<in> set (call_successor_list g u)"
    using ce by (simp add: set_call_successor_list[OF finC] call_successors_iff)
  have mem: "?t \<in> set (trees u ctx)"
    unfolding routed_extra_def Let_def using succ by (force intro: rev_image_eqI)
  have "fst (dgs_enter S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
      = globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (simp add: seed_key_ne_gk0 seed_key_ne_gk0[symmetric])
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 u) (trees u ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_le_side_rhs_fold_dg[OF mem]])
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (u, ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF sides_fold_le_Gen])
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF covU, THEN le_funD, of "Inr gk0"]
    by (rule le_dg_state_globsD)
  finally show ?thesis .
qed

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
  have sin': "s \<in> gamma_unit gs ?d ?g"
    using sin True by (simp add: sg_cov gamma_unit_def)
  have route_agree: "?ctx' = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    using route_enterc_agree[OF True ce sin'] .
  have "call_enter gs (CallEdge dst pars args) s
      \<in> gamma_unit gs (snd (dgs_enter S pars args ?d ?g)) (fst (dgs_enter S pars args ?d ?g))"
    using enter_sound_fs[OF sin'] .
  also have "\<dots> \<subseteq> gamma_unit gs (locals (sigma (Inl (FunctionEntry p, ?ctx')))) ?g"
    by (rule gamma_unit_mono[OF routed_seed_publish_bound_local[OF ce True covV]
          routed_seed_publish_bound_global[OF ce True]])
  also have "\<dots> = \<lbrakk>sg (Inl (FunctionEntry p, ?ctx'))\<rbrakk>"
    using covV by (simp add: sg_cov gamma_unit_def)
  finally show ?thesis using route_agree by simp

qed

subsection \<open>COMB: the routed return combine\<close>

text \<open>Split as \<open>routed_seed_publish_bound_local\<close>/\<open>_global\<close> was: each componentwise
  bound stands on its own, matching what \<open>gamma_unit_mono\<close> needs for the routed
  combine's \<open>combine_abs\<close>-shaped target.\<close>
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
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
              (\<lambda>dex. QueryG gk0 (\<lambda>gv.
                Side gk0 (DG bot (fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv))))
                  (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv))) bot)))))"
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
  let ?t = "QueryL (cl, c1) (\<lambda>dcl. QueryL (FunctionResult p, route cl c1 (locals dcl) (CallEdge dst pars args))
              (\<lambda>dex. QueryG gk0 (\<lambda>gv.
                Side gk0 (DG bot (fst (dgs_combine S dst (locals dcl) (locals dex) (globs gv))))
                  (Answer (DG (snd (dgs_combine S dst (locals dcl) (locals dex) (globs gv))) bot)))))"
  have ret: "(cl, CallEdge dst pars args, FunctionResult p) \<in> set (return_call_action_list g cont)"
    using ce by (simp add: set_return_call_action_list[OF finC] return_call_actions_iff)
  have mem: "?t \<in> set (trees cont c1)"
    unfolding routed_cmb_def Let_def using ret by (force intro: rev_image_eqI)
  have "fst (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (FunctionResult p, ?ex_ctx))))
           (globs (sigma (Inr gk0))))
      = globs (sides_of_rhs ?t sigma (Inr gk0))"
    by simp
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
  other CALL obligation uses; \<open>formals_enterc\<close> is its trace-semantic counterpart,
  decoding the concrete entered store's formals the same way, given the point
  abstraction \<open>decode\<close> a domain provides for a concrete value and the CFG needed
  to look up a call site's own formal list. Neither definition mentions a
  domain-specific accessor beyond \<open>decode\<close> itself, so any domain reusing
  \<^locale>\<open>routed_context\<close> instantiates this pair once instead of hand-writing a
  per-formal projection, as \<open>route_ivl\<close>/\<open>ivl_enterc\<close> previously did.
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

definition formals_enterc ::
  "cfg \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> cfg_node \<Rightarrow> 'a list \<Rightarrow> store \<Rightarrow> 'a list"
where
  "formals_enterc g decode u ctx s = formals_context (formals_at_call_site g u) (decode \<circ> s)"

text \<open>
  The whole matched \<^type>\<open>call_action\<close> at a node, not only its formals: an
  \<open>enterc\<close> built purely from the caller's own solved abstract state (rather than
  by decoding the concrete entered store, as \<^const>\<open>formals_enterc\<close> does) needs
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
