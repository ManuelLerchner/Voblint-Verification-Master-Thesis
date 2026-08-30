theory Routed_Context
  imports DG_Ctx_Activation DG_Base "Voblint_Solver.Strategy_Tree_Combinators" DG_Transfer_Combinators
    "Voblint_Solver.Strategy_Tree_Do" "Voblint_CFG.LTR_Def" Activation_Backbone
begin

section \<open>One route, CALL and COMB discharged once\<close>

text \<open>
  \<^locale>\<open>dg_ctx_activation_base\<close> already discharges EDGE (\<open>dg_ctx_act_edge\<close>) generically off the
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

text \<open>
  The routing combine reads the caller under its own context, the callee exit under the
  context \<open>route\<close> selects from the caller's local value and the exact matched
  \<^typ>\<open>call_action\<close> (from \<^const>\<open>return_call_action_list\<close>, never re-derived from
  the call site's outgoing edges), and the one shared global slot \<open>gk0\<close>.

  Parameter order matches \<^locale>\<open>dg_ctx_activation_base\<close>'s \<open>cmb\<close> calling
  convention: the generator supplies \<open>route\<close> as \<open>cmb\<close>'s own first argument
  (\<open>cmb route c ca cc ex\<close> in \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>), so
  \<open>routed_cmb_g S gk0 seed_key\<close>, closing over the spec, the shared slot, and the
  seed-key injection, is the value that instantiates \<open>cmb\<close>.

  This tree owns the whole call lifecycle for one call action: it reads the caller once,
  routes the callee context once (\<open>ctx'\<close>), and shares that one \<open>ctx'\<close> between the
  entry-seed publication and the combine's callee-exit read. The callee is therefore
  activated as a side effect of whichever equation combines its result, discharging
  \<open>enter#\<close> exactly once per call action rather than once per hook. Only the half that
  cannot move stays with \<open>routed_extra_g\<close>: a callee's own entry equation is the one
  place that can read its own seed slot back. \<open>route\<close> is kept as a parameter of that
  hook purely to match \<^locale>\<open>dg_ctx_activation_base\<close>'s \<open>extra\<close> calling
  convention, which always supplies it.

  The seed channel is \<open>'D\<close>-typed, so \<open>'D\<close> and \<open>'G\<close> stay independent. The
  publication writes the callee's freshly entered local state --- a \<open>'D\<close>-typed value
  --- into the \<open>locals\<close> half of the \<^type>\<open>dg_state\<close> published at the seed key. A
  \<^type>\<open>dg_state\<close> already carries both fields at every key regardless of whether the
  key is reached through \<open>Inl\<close> (a \<open>(pp, 'c)\<close> local unknown) or \<open>Inr\<close> (a \<open>'k\<close>
  global unknown): \<open>locals\<close>/\<open>globs\<close> are call-site conventions, not something
  \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> themselves enforce. Since \<open>seed_key p ctx\<close> is
  always distinct from \<open>gk0\<close> (\<open>seed_key_ne_gk0\<close>) and no other equation ever
  publishes to a seed key, nothing else reads or writes that key's \<open>locals\<close> half.
  \<open>gk0\<close>'s own \<open>globs\<close>-typed publication (\<open>publish_global\<close>) is untouched, so
  \<open>'G\<close> can be instantiated independently of \<open>'D\<close> --- \<open>unit\<close> for a Base-style
  spec, honestly reflecting that no genuine global content exists there: its whole local
  carrier already holds every VIMP variable, \<^const>\<open>dgs_enter\<close>/\<^const>\<open>dgs_combine\<close>'s
  \<open>fst\<close> half is the identity on \<open>g\<close>, and its local answer (\<open>snd\<close>) never reads
  \<open>g\<close> either, so \<open>gk0\<close> is provably inert for such a spec rather than merely unused
  by convention.
\<close>

text \<open>
  One resolved callee: enter the frame, key it, publish it, read that activation's exit
  back and combine. The caller's local state and the global unknown's value are passed
  in rather than read here, because the call site reads them once and every target it
  resolves to is entered from that same pair.
\<close>

definition routed_cmb_g_at ::
  "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> 'D \<Rightarrow> 'G \<Rightarrow> pname
   \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g_at S gk0 seed_key route ctx ca cc caller globals1 p =
     with_call ca (\<lambda>dst fs as. do {
      let ci = call_info_of ca p;
      let entry = enter_local S ci caller globals1;
      let ctx' = route cc ctx entry ca;
      let dcont = caller_cont S ci caller globals1;
      let eg = enter_global S ci caller globals1;
       depend_on (seed_key (FunctionEntry p) ctx')
         (DG entry bot) (answer (DG bot bot));
       callee_state \<leftarrow> read_local (FunctionResult p, ctx');
       globals_state2 \<leftarrow> read_global gk0;
       let callee = locals callee_state;
       let globals2 = globs globals_state2;
       let cg = combine_global S ci dcont callee globals2;
       publish_global gk0 (eg \<squnion> cg);
       answer_local (combine_local S ci dcont callee globals2)
     })"

text \<open>
  The call site's own contribution: read the caller state and the global unknown, ask
  \<open>resolve\<close> which procedures this site can enter given that state, and join what each
  resolved activation returns. The callee is the resolver's answer, not a component of
  the enumeration the equation system was built from, so a resolver reading the caller
  state selects the target at solve time. \<^const>\<open>static_targets\<close> is the resolver that
  ignores the state and answers from the CFG, which reproduces the statically
  enumerated behaviour exactly.

  An empty answer contributes \<^const>\<open>bot\<close>. Under \<^const>\<open>static_targets\<close> that happens
  only where the CFG has no call edge, i.e. where the enumeration produced no combine
  tree either.
\<close>

definition routed_cmb_g ::
  "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'D \<Rightarrow> pname list)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g S gk0 seed_key resolve route ctx ca cc v =
     do {
       caller_state \<leftarrow> read_local (cc, ctx);
       globals_state1 \<leftarrow> read_global gk0;
       side_rhs_fold_dg bot
         (map (routed_cmb_g_at S gk0 seed_key route ctx ca cc
                 (locals caller_state) (globs globals_state1))
              (resolve v cc ca (locals caller_state)))
     }"


text \<open>The seed read-back hook: at a callee entry it reads the seed out of the
  \<open>locals\<close> half, matching \<open>routed_cmb_g\<close>'s write.\<close>
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

subsection \<open>Addressing a callee entry at the seed it is published to\<close>

text \<open>
  A callee entry receives no intra edge: its value is exactly the join of the entry
  contributions published at its seed key.  \<open>seed_addr\<close> is the address function that
  says so --- a \<^const>\<open>FunctionEntry\<close> is carried by the contribution-only unknown
  \<open>seed_key v ctx\<close>, every other program point by its own \<open>(pp, 'c)\<close> equation-driven
  unknown --- and \<open>seed_predecessor_addr_list\<close> is the predecessor selection built
  from it, to be supplied where \<^const>\<open>intra_predecessor_addr_list\<close> addresses every
  predecessor locally.

  \<open>val_at\<close> is the same function read the other way round: the abstract value a
  solution assigns to a program point, whichever side of the solver's valuation
  carries it.  Reading a solution through \<open>val_at\<close> rather than through
  \<^const>\<open>Inl\<close> directly is what keeps a coverage statement uniform over program
  points once the two kinds coexist.
\<close>

definition seed_addr :: "(pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> (pp \<times> 'c + 'k)" where
  "seed_addr seed_key v ctx =
     (case v of FunctionEntry _ \<Rightarrow> Inr (seed_key v ctx) | _ \<Rightarrow> Inl (v, ctx))"

lemma seed_addr_FunctionEntry [simp]:
  "seed_addr seed_key (FunctionEntry p) ctx = Inr (seed_key (FunctionEntry p) ctx)"
  by (simp add: seed_addr_def)

lemma seed_addr_Statement [simp]:
  "seed_addr seed_key (Statement n) ctx = Inl (Statement n, ctx)"
  by (simp add: seed_addr_def)

lemma seed_addr_FunctionResult [simp]:
  "seed_addr seed_key (FunctionResult p) ctx = Inl (FunctionResult p, ctx)"
  by (simp add: seed_addr_def)

definition seed_predecessor_addr_list ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> ((pp \<times> 'c + 'k) \<times> edge_action) list"
where
  "seed_predecessor_addr_list seed_key g v ctx =
     map (\<lambda>(u, a). (seed_addr seed_key u ctx, a)) (intra_predecessor_list g v)"

definition val_at ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> (pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'D"
where
  "val_at seed_key sigma v ctx = locals (sigma (seed_addr seed_key v ctx))"

lemma val_at_FunctionEntry:
  "val_at seed_key sigma (FunctionEntry p) ctx
     = locals (sigma (Inr (seed_key (FunctionEntry p) ctx)))"
  by (simp add: val_at_def)

lemma val_at_not_entry:
  "(\<And>p. v \<noteq> FunctionEntry p) \<Longrightarrow> val_at seed_key sigma v ctx = locals (sigma (Inl (v, ctx)))"
  by (cases v) (auto simp: val_at_def seed_addr_def)

text \<open>
  Side-free analogue of \<^const>\<open>routed_cmb_g\<close>: instead of publishing \<open>gk0\<close> itself
  it answers the
  unsplit \<open>(combine_local ..., eg \<squnion> cg)\<close> pair, matching
  \<^const>\<open>dg_edge_contribution_tree\<close>'s shape, so several \<open>comb\<close>/\<open>intra\<close> contributions
  fold into one buffered generator equation and \<open>gk0\<close> is published once, after every
  contribution has been read. The \<open>'D\<close>-typed seed publication is unaffected: each call
  action's \<open>seed_key\<close> is distinct from \<open>gk0\<close> and from every other call action's, so it
  never collides within one fold and stays a \<^const>\<open>Side\<close> here exactly as in
  \<^const>\<open>routed_cmb_g\<close>.
\<close>
definition routed_cmb_g_contribution_at ::
  "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> 'D \<Rightarrow> 'G \<Rightarrow> pname
   \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g_contribution_at S gk0 seed_key route ctx ca cc caller globals1 p =
     with_call ca (\<lambda>dst fs as. do {
      let ci = call_info_of ca p;
      let entry = enter_local S ci caller globals1;
      let ctx' = route cc ctx entry ca;
      let dcont = caller_cont S ci caller globals1;
      let eg = enter_global S ci caller globals1;
       depend_on (seed_key (FunctionEntry p) ctx')
         (DG entry bot) (answer (DG bot bot));
       callee_state \<leftarrow> read_local (FunctionResult p, ctx');
       globals_state2 \<leftarrow> read_global gk0;
       let callee = locals callee_state;
       let globals2 = globs globals_state2;
       let cg = combine_global S ci dcont callee globals2;
       answer (DG (combine_local S ci dcont callee globals2) (eg \<squnion> cg))
     })"

text \<open>The buffered call-site contribution accumulates both halves of each resolved
  activation's answer, since its whole point is that the global half rides the answer
  and is published once by the generator rather than per contribution.\<close>

definition routed_cmb_g_contribution ::
  "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'D \<Rightarrow> pname list)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g_contribution S gk0 seed_key resolve route ctx ca cc v =
     do {
       caller_state \<leftarrow> read_local (cc, ctx);
       globals_state1 \<leftarrow> read_global gk0;
       fold_rhs_trees bot
         (map (routed_cmb_g_contribution_at S gk0 seed_key route ctx ca cc
                 (locals caller_state) (globs globals_state1))
              (resolve v cc ca (locals caller_state)))
     }"

text \<open>
  Purely syntactic facts about the tree shapes of \<^const>\<open>routed_cmb_g\<close> and
  \<^const>\<open>routed_cmb_g_contribution\<close> --- independent of any solved system, needed
  only to discharge \<^theory>\<open>Voblint_Core.DG_Framework\<close>'s
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered_correspondence\<close> hypotheses when
  \<open>routed_cmb_g\<close>/\<open>routed_cmb_g_contribution\<close>/\<open>routed_extra_g\<close> instantiate its
  \<open>cmb\<close>/\<open>cmb_c\<close>/\<open>extra\<close> parameters; \<open>routed_extra_g\<close>'s own two facts sit
  with its definition above. Stated standalone, since they need only \<open>seed_key\<close>'s
  freeness from \<open>gk0\<close>, not a solved-system interpretation.
\<close>

text \<open>Per resolved target first: the two trees for one activation differ only in whether
  the global half is published or ridden out on the answer.\<close>

lemma routed_cmb_g_contribution_at_matches_local:
  "locals (traverse_rhs
       (routed_cmb_g_contribution_at S gk0 seed_key route ctx ca cc caller globals1 p) tau)
     = locals (traverse_rhs
       (routed_cmb_g_at S gk0 seed_key route ctx ca cc caller globals1 p) tau)"
  unfolding routed_cmb_g_contribution_at_def routed_cmb_g_at_def
  by (cases ca) (simp add: Let_def)

lemma routed_cmb_g_contribution_at_matches_global:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "globs (traverse_rhs
       (routed_cmb_g_contribution_at S gk0 seed_key route ctx ca cc caller globals1 p) tau)
     = globs (sides_of_rhs
       (routed_cmb_g_at S gk0 seed_key route ctx ca cc caller globals1 p) tau (Inr gk0))"
  unfolding routed_cmb_g_contribution_at_def routed_cmb_g_at_def
  by (cases ca) (simp add: Let_def ne[THEN not_sym])

lemma routed_cmb_g_at_side_pure:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "locals (sides_of_rhs
       (routed_cmb_g_at S gk0 seed_key route ctx ca cc caller globals1 p) tau (Inr gk0)) = bot"
  unfolding routed_cmb_g_at_def
  by (cases ca) (simp add: Let_def ne ne[THEN not_sym])

lemma routed_cmb_g_contribution_at_free_at_key:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "sides_of_rhs
       (routed_cmb_g_contribution_at S gk0 seed_key route ctx ca cc caller globals1 p)
       tau (Inr gk0) = bot"
  unfolding routed_cmb_g_contribution_at_def
  by (cases ca) (simp add: Let_def ne[THEN not_sym])

lemma routed_cmb_g_contribution_at_sides_off_key:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
    and z: "z \<noteq> Inr gk0"
  shows "sides_of_rhs
       (routed_cmb_g_contribution_at S gk0 seed_key route ctx ca cc caller globals1 p) tau z
     = sides_of_rhs
       (routed_cmb_g_at S gk0 seed_key route ctx ca cc caller globals1 p) tau z"
  unfolding routed_cmb_g_contribution_at_def routed_cmb_g_at_def
  by (cases ca) (simp add: Let_def ne z)

lemma routed_cmb_g_contribution_at_dep:
  "dep_aux tau
       (routed_cmb_g_contribution_at S gk0 seed_key route ctx ca cc caller globals1 p)
     = dep_aux tau (routed_cmb_g_at S gk0 seed_key route ctx ca cc caller globals1 p)"
  unfolding routed_cmb_g_contribution_at_def routed_cmb_g_at_def
  by (cases ca) (simp add: Let_def)

text \<open>
  Lifting a per-activation fact to the call site is the same argument four times: the
  two trees fold the same resolved list, one accumulating both halves of each answer and
  one only the local half. These state that argument once, over an arbitrary list of
  targets, so each lifted fact below is one \<open>rule\<close> away from its per-target version.
\<close>

lemma locals_fold_eq_side_fold_acc:
  assumes "\<And>x. locals (traverse_rhs (f x) sigma) = locals (traverse_rhs (h x) sigma)"
  shows "locals (traverse_rhs (fold_rhs_trees acc (map f xs)) sigma)
           = locals (traverse_rhs (side_rhs_fold_dg (locals acc) (map h xs)) sigma)"
  by (induction xs arbitrary: acc)
     (simp_all add: sup_dg_state_def assms)

lemma locals_fold_eq_side_fold:
  assumes "\<And>x. locals (traverse_rhs (f x) sigma) = locals (traverse_rhs (h x) sigma)"
  shows "locals (traverse_rhs (fold_rhs_trees bot (map f xs)) sigma)
           = locals (traverse_rhs (side_rhs_fold_dg bot (map h xs)) sigma)"
  using locals_fold_eq_side_fold_acc[OF assms, where acc = bot]
  by (simp add: bot_dg_state_def)

lemma globs_foldr_sup:
  "globs (foldr (\<lambda>t acc'. F t \<squnion> acc') ts acc)
     = foldr (\<lambda>t acc'. globs (F t) \<squnion> acc') ts (globs acc)"
  by (induction ts) (simp_all add: sup_dg_state_def)

lemma globs_traverse_fold_rhs_trees_foldr:
  "globs (traverse_rhs (fold_rhs_trees acc ts) sigma)
     = foldr (\<lambda>t a. globs (traverse_rhs t sigma) \<squnion> a) ts (globs acc)"
  by (simp add: traverse_fold_rhs_trees_char globs_foldr_sup)

lemma globs_sides_side_rhs_fold_dg_foldr:
  "globs (sides_of_rhs (side_rhs_fold_dg accl ts) sigma z)
     = foldr (\<lambda>t a. globs (sides_of_rhs t sigma z) \<squnion> a) ts bot"
  by (induction ts arbitrary: accl)
     (simp_all add: sup_dg_state_def bot_dg_state_def ac_simps)

lemma globs_fold_eq_side_fold_sides:
  assumes "\<And>x. globs (traverse_rhs (f x) sigma) = globs (sides_of_rhs (h x) sigma z)"
  shows "globs (traverse_rhs (fold_rhs_trees bot (map f xs)) sigma)
           = globs (sides_of_rhs (side_rhs_fold_dg accl (map h xs)) sigma z)"
  by (simp add: globs_traverse_fold_rhs_trees_foldr globs_sides_side_rhs_fold_dg_foldr
        bot_dg_state_def assms foldr_map o_def)

lemma locals_side_fold_sides_bot:
  assumes "\<And>x. locals (sides_of_rhs (h x) sigma z) = bot"
  shows "locals (sides_of_rhs (side_rhs_fold_dg accl (map h xs)) sigma z) = bot"
  by (induction xs)
     (simp_all add: sides_of_rhs_side_rhs_fold_dg_char sup_dg_state_def bot_dg_state_def assms)

lemma sides_fold_rhs_trees_bot_map:
  assumes "\<And>x. sides_of_rhs (f x) sigma z = bot"
  shows "sides_of_rhs (fold_rhs_trees acc (map f xs)) sigma z = bot"
  by (induction xs)
     (simp_all add: sides_of_rhs_fold_rhs_trees_char assms)

lemma sides_fold_eq_side_fold:
  assumes "\<And>x. sides_of_rhs (f x) sigma z = sides_of_rhs (h x) sigma z"
  shows "sides_of_rhs (fold_rhs_trees acc (map f xs)) sigma z
           = sides_of_rhs (side_rhs_fold_dg accl (map h xs)) sigma z"
  by (simp add: sides_of_rhs_fold_rhs_trees_char sides_of_rhs_side_rhs_fold_dg_char
        assms foldr_map o_def)

lemma dep_fold_eq_side_fold:
  assumes "\<And>x. dep_aux sigma (f x) = dep_aux sigma (h x)"
  shows "dep_aux sigma (fold_rhs_trees acc (map f xs))
           = dep_aux sigma (side_rhs_fold_dg accl (map h xs))"
  by (simp add: dep_aux_fold_rhs_trees_char dep_aux_side_rhs_fold_dg_char assms)

text \<open>The call site's two trees, related target by target.\<close>

lemma routed_cmb_g_contribution_matches_local:
  "locals (traverse_rhs (routed_cmb_g_contribution S gk0 seed_key resolve route ctx ca cc v) tau)
     = locals (traverse_rhs (routed_cmb_g S gk0 seed_key resolve route ctx ca cc v) tau)"
  unfolding routed_cmb_g_contribution_def routed_cmb_g_def
  by (simp add: locals_fold_eq_side_fold routed_cmb_g_contribution_at_matches_local)

lemma routed_cmb_g_contribution_matches_global:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "globs (traverse_rhs (routed_cmb_g_contribution S gk0 seed_key resolve route ctx ca cc v) tau)
     = globs (sides_of_rhs (routed_cmb_g S gk0 seed_key resolve route ctx ca cc v) tau (Inr gk0))"
  unfolding routed_cmb_g_contribution_def routed_cmb_g_def
  by (simp add: globs_fold_eq_side_fold_sides routed_cmb_g_contribution_at_matches_global[OF ne])

lemma routed_cmb_g_side_pure:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "locals (sides_of_rhs (routed_cmb_g S gk0 seed_key resolve route ctx ca cc v) tau (Inr gk0)) = bot"
  unfolding routed_cmb_g_def
  by (simp add: locals_side_fold_sides_bot routed_cmb_g_at_side_pure[OF ne])

lemma routed_cmb_g_contribution_free_at_key:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
  shows "sides_of_rhs (routed_cmb_g_contribution S gk0 seed_key resolve route ctx ca cc v) tau (Inr gk0) = bot"
  unfolding routed_cmb_g_contribution_def
  by (simp add: sides_fold_rhs_trees_bot_map routed_cmb_g_contribution_at_free_at_key[OF ne])

lemma routed_cmb_g_contribution_sides_off_key:
  assumes ne: "\<And>p c. seed_key p c \<noteq> gk0"
    and z: "z \<noteq> Inr gk0"
  shows "sides_of_rhs (routed_cmb_g_contribution S gk0 seed_key resolve route ctx ca cc v) tau z
       = sides_of_rhs (routed_cmb_g S gk0 seed_key resolve route ctx ca cc v) tau z"
  unfolding routed_cmb_g_contribution_def routed_cmb_g_def
  by (simp add: sides_fold_eq_side_fold routed_cmb_g_contribution_at_sides_off_key[OF ne z])

lemma routed_cmb_g_contribution_dep:
  "dep_aux tau (routed_cmb_g_contribution S gk0 seed_key resolve route ctx ca cc v)
     = dep_aux tau (routed_cmb_g S gk0 seed_key resolve route ctx ca cc v)"
  unfolding routed_cmb_g_contribution_def routed_cmb_g_def
  by (simp add: dep_aux_fold_rhs_trees_char dep_aux_side_rhs_fold_dg_char
        routed_cmb_g_contribution_at_dep)

subsection \<open>The routed-context locale: D and G independently typed\<close>

text \<open>
  \<open>routed_context_base_hetero\<close> instantiates \<^locale>\<open>dg_ctx_activation_base\<close> at
  \<open>routed_cmb_g\<close>/\<open>routed_extra_g\<close>, so \<open>S\<close>'s own \<open>'D\<close>/\<open>'G\<close> stay as
  independent as that locale already keeps them: no \<open>'D = 'G\<close> constraint is threaded
  in by this locale's \<open>for\<close> clause. \<^locale>\<open>dg_ctx_activation_base\<close> itself carries
  no routing-specific content: every fact it supplies (\<open>pp_eq_bound\<close>,
  \<open>pp_sides_bound\<close>, \<open>sides_fold_le_Gen\<close>, \<open>edge_bound_local\<close>/\<open>_global\<close>,
  \<open>dg_ctx_act_edge\<close>, \<open>dg_ctx_act_comb_covered\<close>) is already generic in
  \<open>cmb\<close>/\<open>extra\<close>, so instantiating it at \<open>routed_cmb_g\<close>/\<open>routed_extra_g\<close>
  reuses those proofs unchanged; only the seed-specific reasoning below, which
  \<open>dg_ctx_activation_base\<close> never has since seeding is \<open>routed_cmb_g\<close>'s own
  addition, is carried out here.

  Beyond \<^locale>\<open>dg_ctx_activation_base\<close>'s parameters: \<open>seed_key\<close> injects a routed
  \<open>(pp, 'c)\<close> pair into the global-key space; \<open>enterc\<close> is the trace-semantic context
  function keying the activation-local collecting semantics; and \<open>route_enterc_agree\<close>
  is the one agreement that cannot be discharged generically: at a real call edge, the
  equation-level \<open>route\<close>, evaluated on an abstract caller-local value, must agree with
  the semantic \<open>enterc\<close> on every concrete entered store the value concretizes to.
  Restricting the call action to an edge of \<open>g\<close> (rather than quantifying over every
  value of the \<open>call_action\<close> type) matches how CALL and COMB below only ever invoke
  this fact at a matched edge, and keeps the obligation provable for an abstract domain
  that is exact on edges actually present in the program without being exact everywhere.
  This is a per-instance proof obligation, not a locale theorem.
\<close>

locale routed_context_base_hetero =
  dg_ctx_activation_base S gammaDG gs g gk0 route
    "routed_cmb_g S gk0 seed_key resolve" "routed_extra_g seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route ("context\<^sup>#")
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and resolve :: "pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'D \<Rightarrow> pname list"
    and gammaM :: "'M \<Rightarrow> store set" +
  fixes enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes finC[intro,simp]: "finite (calls g)"
    and seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and resolve_sound:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> p \<in> set (resolve cont u (CallEdge dst pars args)
                       (locals (sigma (Inl (u, ctx)))))"
    and route_enterc_agree:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow>       s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))    \<Longrightarrow> route u ctx (enter_local S (call_info_of (CallEdge dst pars args) p)
                         (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
             (CallEdge dst pars args)
         = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    and call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (FunctionEntry p,
             route u ctx (enter_local S (call_info_of (CallEdge dst pars args) p) (locals (sigma (Inl (u, ctx))))
                              (globs (sigma (Inr gk0)))) (CallEdge dst pars args))
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
  shows "routed_cmb_g S gk0 seed_key resolve route ctx (CallEdge dst pars args) cc cont
           \<in> set (trees cont ctx)"
proof -
  have "(cc, CallEdge dst pars args) \<in> set (call_site_list g cont)"
    using ce by (auto simp: set_call_site_list[OF finC])
  then show ?thesis by (force intro: rev_image_eqI)
qed

lemma resolved_target_mem:
  assumes covV: "(cc, ctx) \<in> vars"
    and ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0)))"
  shows "routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) cc
             (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0))) p
           \<in> set (map (routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) cc
                        (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0))))
                      (resolve cont cc (CallEdge dst pars args)
                         (locals (sigma (Inl (cc, ctx))))))"
  using resolve_sound[OF covV ce sin] by simp

lemma resolved_at_le_site_acc:
  assumes covV: "(cc, ctx) \<in> vars"
    and ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0)))"
  shows "locals (traverse_rhs
           (routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0))) p) sigma)
         \<le> side_acc_dg (acc0 cont) sigma (trees cont ctx)"
proof -
  have "locals (traverse_rhs
           (routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0))) p) sigma)
      \<le> locals (traverse_rhs
           (routed_cmb_g S gk0 seed_key resolve route ctx (CallEdge dst pars args) cc cont)
           sigma)"
    using locals_traverse_le_side_acc_dg[OF resolved_target_mem[OF covV ce sin], where acc = bot]
    by (simp add: routed_cmb_g_def traverse_side_rhs_fold_dg)
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont ctx)"
    by (rule locals_traverse_le_side_acc_dg[OF resolved_site_mem[OF ce]])
  finally show ?thesis .
qed

lemma resolved_at_le_site_sides:
  assumes covV: "(cc, ctx) \<in> vars"
    and ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0)))"
  shows "sides_of_rhs
           (routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0))) p) sigma z
         \<le> sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma z"
proof -
  have "sides_of_rhs
           (routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0))) p) sigma z
      \<le> sides_of_rhs
           (routed_cmb_g S gk0 seed_key resolve route ctx (CallEdge dst pars args) cc cont)
           sigma z"
    using sides_le_side_rhs_fold_dg
      [OF resolved_target_mem[OF covV ce sin], where acc = bot and k = z]
    by (simp add: routed_cmb_g_def)
  also have "\<dots> \<le> sides_of_rhs (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma z"
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
  shows "snd (dgs_enter S (call_info_of (CallEdge dst pars args) p)
               (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inr (seed_key (FunctionEntry p)
               (route u ctx (enter_local S (call_info_of (CallEdge dst pars args) p)
                                (locals (sigma (Inl (u, ctx))))
                                (globs (sigma (Inr gk0)))) (CallEdge dst pars args)))))"
proof -
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?gv = "globs (sigma (Inr gk0))"
  let ?ctx' = "route u ctx (enter_local S ?ci ?d ?gv) (CallEdge dst pars args)"
  let ?k = "Inr (seed_key (FunctionEntry p) ?ctx')"
  let ?t = "routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) u ?d ?gv p"
  have "snd (dgs_enter S ?ci ?d ?gv) = locals (sides_of_rhs ?t sigma ?k)"
    by (simp add: routed_cmb_g_at_def Let_def seed_key_ne_gk0)
  also have "\<dots> \<le> locals (sides_of_rhs
      (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma ?k)"
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
    and covV: "(FunctionEntry p,
                 route u ctx (enter_local S (call_info_of (CallEdge dst pars args) p)
                     (locals (sigma (Inl (u, ctx))))
                     (globs (sigma (Inr gk0)))) (CallEdge dst pars args)) \<in> vars"
  shows "snd (dgs_enter S (call_info_of (CallEdge dst pars args) p)
               (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (FunctionEntry p,
               route u ctx (enter_local S (call_info_of (CallEdge dst pars args) p)
                   (locals (sigma (Inl (u, ctx))))
                   (globs (sigma (Inr gk0)))) (CallEdge dst pars args))))"
  by (rule order_trans[OF routed_seed_publish_bound_seed[OF covV_call ce sin covV_cont]
                          routed_seed_read_bound[OF covV]])

lemma routed_seed_publish_bound_global:
  assumes covV: "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, ctx) \<in> vars"
  shows "fst (dgs_enter S (call_info_of (CallEdge dst pars args) p)
               (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
           \<le> globs (sigma (Inr gk0))"
proof -
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?gv = "globs (sigma (Inr gk0))"
  let ?t = "routed_cmb_g_at S gk0 seed_key route ctx (CallEdge dst pars args) u ?d ?gv p"
  have "fst (dgs_enter S ?ci ?d ?gv) \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: routed_cmb_g_at_def Let_def seed_key_ne_gk0 seed_key_ne_gk0[symmetric]
             sup_dg_state_def bot_dg_state_def intro: le_supI1)
  also have "\<dots> \<le> globs (sides_of_rhs
      (side_rhs_fold_dg (acc0 cont) (trees cont ctx)) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF resolved_at_le_site_sides[OF covV ce sin]])
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
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ctx' = "route u ctx (enter_local S ?ci ?d ?g) (CallEdge dst pars args)"
  have covV: "(FunctionEntry p, ?ctx') \<in> vars"
    using call_fwd[OF True ce] .
  have covV_cont: "(cont, ctx) \<in> vars"
    using comb_fwd[OF True ce] .
  have sin': "s \<in> gammaDG ?d ?g"
    using sin True by (simp add: sg_cov)
  have route_agree: "?ctx' = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
    using route_enterc_agree[OF True ce sin'] .
  have "call_enter gs (CallEdge dst pars args) s
      \<in> gammaDG (snd (dgs_enter S ?ci ?d ?g)) (fst (dgs_enter S ?ci ?d ?g))"
    using enter_sound_fs[where ci = "?ci", OF sin'] by simp
  also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (FunctionEntry p, ?ctx')))) ?g"
    by (rule gammaDG_mono[OF routed_seed_publish_bound_local[OF True ce sin' covV_cont covV]
          routed_seed_publish_bound_global[OF True ce sin' covV_cont]])
  also have "\<dots> = gammaM (sg (Inl (FunctionEntry p, ?ctx')))"
    using covV by (simp add: sg_cov)
  finally show ?thesis using route_agree by simp
qed

subsection \<open>COMB: the routed return combine\<close>

lemma routed_comb_bound_local:
  assumes covV: "(cl, c1) \<in> vars"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "snd (dgs_combine S (call_info_of (CallEdge dst pars args) p)
               (caller_cont S (call_info_of (CallEdge dst pars args) p)
                  (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (enter_local S (call_info_of (CallEdge dst pars args) p)
                     (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0))))
                     (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> locals (sigma (Inl (cont, c1)))"
proof -
  let ?d = "locals (sigma (Inl (cl, c1)))"
  let ?gv = "globs (sigma (Inr gk0))"
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?ex_ctx = "route cl c1 (enter_local S ?ci ?d ?gv) (CallEdge dst pars args)"
  let ?t = "routed_cmb_g_at S gk0 seed_key route c1 (CallEdge dst pars args) cl ?d ?gv p"
  have "snd (dgs_combine S ?ci (caller_cont S ?ci ?d ?gv)
               (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?gv)
      = locals (traverse_rhs ?t sigma)"
    by (simp add: routed_cmb_g_at_def Let_def)
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont c1)"
    by (rule resolved_at_le_site_acc[OF covV ce sin])
  also have "\<dots> = locals (eq Gen (cont, c1) sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (cont, c1)))"
    using pp_eq_bound[OF covV_cont] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma routed_comb_bound_global:
  assumes covV: "(cl, c1) \<in> vars"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0)))"
    and covV_cont: "(cont, c1) \<in> vars"
  shows "fst (dgs_combine S (call_info_of (CallEdge dst pars args) p)
               (caller_cont S (call_info_of (CallEdge dst pars args) p)
                  (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0))))
               (locals (sigma (Inl (FunctionResult p,
                 route cl c1 (enter_local S (call_info_of (CallEdge dst pars args) p)
                     (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0))))
                     (CallEdge dst pars args)))))
               (globs (sigma (Inr gk0))))
         \<le> globs (sigma (Inr gk0))"
proof -
  let ?d = "locals (sigma (Inl (cl, c1)))"
  let ?gv = "globs (sigma (Inr gk0))"
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?ex_ctx = "route cl c1 (enter_local S ?ci ?d ?gv) (CallEdge dst pars args)"
  let ?t = "routed_cmb_g_at S gk0 seed_key route c1 (CallEdge dst pars args) cl ?d ?gv p"
  have "fst (dgs_combine S ?ci (caller_cont S ?ci ?d ?gv)
               (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?gv)
      \<le> globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (auto simp: routed_cmb_g_at_def Let_def seed_key_ne_gk0 seed_key_ne_gk0[symmetric]
             sup_dg_state_def bot_dg_state_def intro: le_supI2)
  also have "\<dots> \<le> globs (sides_of_rhs
      (side_rhs_fold_dg (acc0 cont) (trees cont c1)) sigma (Inr gk0))"
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
  hence "gammaM (sg (Inl (cl, c1))) = {}" by (rule sg_uncovered_empty)
  thus ?thesis using s by simp
next
  case True
  let ?d = "locals (sigma (Inl (cl, c1)))"
  let ?g = "globs (sigma (Inr gk0))"
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?ex_ctx = "route cl c1 (enter_local S ?ci ?d ?g) (CallEdge dst pars args)"
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
        \<in> gammaDG (snd (dgs_combine S ?ci (caller_cont S ?ci ?d ?g)
                          (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))
             (fst (dgs_combine S ?ci (caller_cont S ?ci ?d ?g)
                          (locals (sigma (Inl (FunctionResult p, ?ex_ctx)))) ?g))"
      using combine_sound_at_call_fs[where ci = ?ci, OF sin tin order_refl] by simp
    also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (cont, c1)))) ?g"
      by (rule gammaDG_mono[OF routed_comb_bound_local[OF \<open>(cl, c1) \<in> vars\<close> ce sin covV_cont]
            routed_comb_bound_global[OF \<open>(cl, c1) \<in> vars\<close> ce sin covV_cont]])
    also have "\<dots> = gammaM (sg (Inl (cont, c1)))"
      using covV_cont by (simp add: sg_cov)
    finally show ?thesis .
  qed
qed


subsection \<open>An entry-local bound in the shape \<open>pp_entry_s0g_bound\<close> gives for globals\<close>

text \<open>
  The local-carrier twin of \<open>pp_entry_s0g_bound\<close> (\<^theory>\<open>Voblint_Core.DG_Ctx_Activation\<close>),
  proved the same way: \<open>Gen\<close>'s own entry accumulator starts at \<open>bot0 \<squnion> s0d\<close>,
  \<open>side_acc_dg_ge_acc\<close> only grows it, and \<open>pp_eq_bound\<close> transports the
  bound across a covered point's post-solution equation.
\<close>

lemma locals_ge_s0d:
  assumes cov: "(cfg_entry g, ctx) \<in> vars"
  shows "s0d \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
proof -
  have "s0d \<le> locals (eq Gen (cfg_entry g, ctx) sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
    using pp_eq_bound[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

subsection \<open>Activation-collect soundness against the routed local unknown\<close>

text \<open>
  Every activation-collected store at any \<open>(v, ctx)\<close> pair is concretized by the routed
  local unknown's own \<open>gammaM\<close> reading. The six obligations of
  \<open>activation_collect_sound_gen\<close> are this locale's own facts: the two entry bounds,
  \<open>dg_ctx_act_edge\<close>, and the CALL and COMB theorems above. An instance therefore
  gets its activation-indexed soundness theorem by interpretation alone.
\<close>

lemma activation_collect_dg_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c
  assumes entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
  shows "activation_collect gs enterc initial_ctx g S0 v ctx
           \<subseteq> gammaM (sg (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen)
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
  \<^typ>\<open>vname \<Rightarrow> 'a\<close>, so this is just \<^const>\<open>map\<close>); \<open>formals_route\<close> applies it to
  the entered local state via \<^const>\<open>enter_local\<close>, the same enter transfer every
  other CALL obligation uses; \<open>formals_context_sem\<close> is its trace-semantic counterpart,
  decoding the concrete entered store's formals the same way, given the point
  abstraction \<open>decode\<close> a domain provides for a concrete value and the CFG needed
  to look up a call site's own formal list. Neither definition mentions a
  domain-specific accessor beyond \<open>decode\<close> itself, so any domain reusing
  \<^locale>\<open>routed_context_base_hetero\<close> instantiates this pair once instead of
  hand-writing a per-formal projection.
\<close>

definition formals_context :: "vname list \<Rightarrow> 'a abs_state \<Rightarrow> 'a list" where
  "formals_context pars d = map d pars"

definition formals_route ::
  "('a::sound_domain abs_state, 'a abs_state) dg_spec \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route S d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (enter_local S (call_info_of ca undefined) d bot))"

text \<open>The routing hook's exact calling convention (\<^locale>\<open>dg_ctx_activation_base\<close>'s
  \<open>route\<close>): generic over call site and caller context, using only the entered
  store.\<close>
definition formals_route_gen ::
  "('a::sound_domain abs_state, 'a abs_state) dg_spec
     \<Rightarrow> pp \<Rightarrow> 'a list \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route_gen S u ctx d ca = formals_route S d ca"

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
  Not a locale theorem, same as \<open>route_enterc_agree\<close> itself: whether a node has at
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
  \<^const>\<open>formals_route\<close>/\<^const>\<open>formals_route_gen\<close> above operate on the unlifted
  \<^typ>\<open>'a abs_state\<close>, the shape an abstract-carrier \<^locale>\<open>routed_context_base_hetero\<close> caller state
  has. The routed executable spine (\<^locale>\<open>dg_ctx_activation_base\<close>, every current
  instance) instead carries \<^typ>\<open>'a abs_state lifted\<close> throughout, to represent an
  activation the solver has not yet covered. \<open>formals_route_lifted\<close>/
  \<open>formals_route_lifted_gen\<close> are the same formal-entry projection at that carrier:
  a caller point that is \<^const>\<open>Bot\<close> routes to the all-\<open>bot\<close> formal context (the
  entered callee frame is then \<^const>\<open>Bot\<close> too), the same collapse an EntryState
  routed instance needs for its own executable/abstract route, generalized to any
  domain's own lifted-carrier \<open>dg_spec\<close> instead of restated per domain.
\<close>

definition formals_route_lifted ::
  "('a::sound_domain abs_state lifted, 'G::bounded_semilattice_sup_bot) dg_spec
     \<Rightarrow> 'a abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route_lifted S d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0))"

definition formals_route_lifted_gen ::
  "('a::sound_domain abs_state lifted, 'G::bounded_semilattice_sup_bot) dg_spec
     \<Rightarrow> pp \<Rightarrow> 'a list \<Rightarrow> 'a abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'a list"
where
  "formals_route_lifted_gen S u ctx d ca = formals_route_lifted S d ca"

subsection \<open>A solved-table \<open>enterc\<close> agrees with any \<open>route\<close> reading the same table\<close>

text \<open>
  \<open>route_enterc_agree\<close> (\<^locale>\<open>routed_context_base_hetero\<close>) asks for a trace-semantic
  \<open>enterc\<close> agreeing with the executable \<open>route\<close> on every matched call. When \<open>route\<close>
  is state-dependent (unlike \<open>route_unit\<close> or \<open>cs_route\<close>, both of which ignore their
  state argument outright and so satisfy this for any \<open>enterc\<close> built the
  same way), the natural \<open>enterc\<close> recomputes \<open>route\<close> from the caller's own solved
  table instead of decoding the concrete entered store: \<open>route_enterc_of_sigma\<close>
  ignores its store argument \<open>s\<close> entirely and reads \<open>route\<close> at the caller's own
  \<open>sigma\<close>-recorded local value and the one \<^const>\<open>call_action_at_call_site\<close> a
  well-formed compiled program's own call-site uniqueness (\<open>compile_prog_calls_source_unique\<close>)
  guarantees. \<open>route_enterc_of_sigma_agree\<close> then discharges \<open>route_enterc_agree\<close> for
  \<^emph>\<open>any\<close> \<open>route\<close>, generically: the two sides differ only in which \<^type>\<open>call_action\<close>
  they pass to \<open>route\<close> (the matched call edge vs. \<^const>\<open>call_action_at_call_site\<close>'s own
  read), and \<open>call_action_at_call_site_eq\<close> identifies those under the same
  uniqueness premise.
\<close>

definition route_enterc_of_sigma ::
  "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec
     \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> (pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state) \<Rightarrow> 'k
     \<Rightarrow> cfg \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
where
  "route_enterc_of_sigma S route sigma gk0 g u ctx s =
     (let ca = call_action_at_call_site g u;
          p = (case callee_entry_at_call_site g u of FunctionEntry q \<Rightarrow> q | _ \<Rightarrow> undefined)
      in route u ctx (enter_local S (call_info_of ca p)
                        (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))) ca)"

lemma route_enterc_of_sigma_agree:
  assumes fin: "finite (calls g)"
    and uniq: "\<And>ca1 ce1 af1 ca2 ce2 af2.
                 (u, ca1, ce1, af1) \<in> calls g \<Longrightarrow> (u, ca2, ce2, af2) \<in> calls g
                 \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  shows "route u ctx (enter_local S (call_info_of (CallEdge dst pars args) p)
                         (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
             (CallEdge dst pars args)
       = route_enterc_of_sigma S route sigma gk0 g u ctx s"
  unfolding route_enterc_of_sigma_def
  using call_action_at_call_site_eq[OF fin uniq ce] callee_entry_at_call_site_eq[OF fin uniq ce]
  by (simp add: Let_def)

end
