theory DG_Keyed_Generator
  imports DG_Framework "TD.TD_side"
begin

text \<open>\<open>TD_side\<close> defines a record field \<open>\<sigma>\<close> for its internal state; hide the short
  name so our \<open>\<sigma>\<close> variables (abstract state maps) are unambiguous.\<close>

hide_const (open) \<sigma>

section \<open>Keyed equation generators\<close>

text \<open>
  Builds a strategy-tree equation system over a CFG from a \<open>dg_spec\<close>, where
  every unknown carries an extra \<open>'k\<close> key alongside its node -- context,
  activation, or any other routing tag a caller wants the generator to
  thread through. \<open>side_cfg_T_eff_keyed_seed_dg\<close> is the direct generator:
  one Side contribution per edge, each keyed and folded independently.
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close> is the same equation system with
  Side contributions folded once per node instead of published per edge, and
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered_correspondence\<close> proves the two
  agree.
  \<open>side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen\<close>,
  \<open>side_cfg_T_eff_keyed_seed_dg_mono_sides_gen\<close> and
  \<open>side_cfg_T_eff_keyed_seed_dg_mono_deps_gen\<close> close the file by
  discharging the vendored solver's own @{const TD_side_mono} preconditions
  for an arbitrary generator instance -- the least-post-solution obligation,
  met once here rather than at every interpreter.
\<close>

subsection \<open>The representation-neutral keyed generator\<close>

text \<open>The keyed generator constructs the equation shape from supplied tree hooks.  Each hook receives the CFG nodes that determine its source and destination; routing and representation choices remain outside the generator.\<close>

definition side_cfg_T_eff_keyed_seed_trees ::
  "(cfg => pp => (pp \<times> edge_action) list)
   => ('c => 'k)
   => ('c => pp => edge_action => pp
        => (pp \<times> 'c, 'k, ('d::bounded_semilattice_sup_bot,
          'h::bounded_semilattice_sup_bot) dg_state) strategy_tree)
   => ('c => pp => call_action => pp => pp
        => (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   => ('c => pp => call_action => pp
        => (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   => cfg => 'd => 'd => 'h
   => (pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
where
  "side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
      g bot0 s0d s0g =
    (\<lambda>(v, ctx).
      let acc0 = (if v = cfg_entry g then bot0 \<squnion> s0d else bot0);
          intra = map (\<lambda>(u, action). edge_tree ctx u action v) (pred_sel g v);
          combine = map (\<lambda>(call, action, exit). combine_tree ctx call action exit v)
            (return_call_action_list g v);
          enter = map (\<lambda>(call, action). enter_tree ctx call action v)
            (entry_call_list g v);
          tree = side_rhs_fold_dg acc0 (intra @ combine @ enter)
      in if v = cfg_entry g then side_effect (gkey ctx) (DG bot s0g) tree else tree)"

lemma eq_side_cfg_T_eff_keyed_seed_trees:
  "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
      g bot0 s0d s0g) (v, ctx) sigma =
    DG (side_acc_dg (if v = cfg_entry g then bot0 \<squnion> s0d else bot0) sigma
      (map (\<lambda>(u, action). edge_tree ctx u action v) (pred_sel g v)
       @ map (\<lambda>(call, action, exit). combine_tree ctx call action exit v)
           (return_call_action_list g v)
       @ map (\<lambda>(call, action). enter_tree ctx call action v)
           (entry_call_list g v))) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_trees_def Let_def
    traverse_side_rhs_fold_dg)

text \<open>
  Every node of a CFG has at most one incoming hook tree per predecessor
  kind, and a typical node has exactly one incoming tree overall (a single
  intra predecessor, a single call return, or a single call entry, with the
  other two kinds empty). These four lemmas reduce the generator to that one
  tree directly, so an instance proves per-node soundness or refinement
  against the named tree constructor instead of re-deriving the fold's
  single-element degeneracy at every call site. They are stated for
  \<^const>\<open>side_cfg_T_eff_keyed_seed_trees\<close> itself, so they specialize to any
  concrete generator built from it -- the hook-parametric \<open>hook_gen\<close>
  included -- without re-unfolding \<open>side_cfg_T_eff_keyed_seed_trees_def\<close>
  at each one.
\<close>

lemma side_cfg_T_eff_keyed_seed_trees_single_edge:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and pred: "pred_sel g v = [(u, a)]"
    and no_combine: "return_call_action_list g v = []"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (v, ctx) sigma =
       DG (locals (traverse_rhs (edge_tree ctx u a v) sigma)) bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (v, ctx)) sigma (Inr (gkey ctx)) =
       sides_of_rhs (edge_tree ctx u a v) sigma (Inr (gkey ctx))"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: not_entry pred no_combine no_enter bot0
    Let_def sides_of_rhs_seqcomp traverse_seqcomp)

lemma side_cfg_T_eff_keyed_seed_trees_single_enter:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "pred_sel g v = []"
    and no_combine: "return_call_action_list g v = []"
    and pred: "entry_call_list g v = [(caller, action)]"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (v, ctx) sigma =
       DG (locals (traverse_rhs (enter_tree ctx caller action v) sigma)) bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (v, ctx)) sigma (Inr (gkey ctx)) =
       sides_of_rhs (enter_tree ctx caller action v) sigma (Inr (gkey ctx))"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: not_entry no_edge no_combine pred bot0
    Let_def sides_of_rhs_seqcomp traverse_seqcomp)

lemma side_cfg_T_eff_keyed_seed_trees_single_combine:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "pred_sel g v = []"
    and pred: "return_call_action_list g v = [(caller, action, callee_exit)]"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (v, ctx) sigma =
       DG (locals (traverse_rhs (combine_tree ctx caller action callee_exit v) sigma)) bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (v, ctx)) sigma (Inr (gkey ctx)) =
       sides_of_rhs (combine_tree ctx caller action callee_exit v) sigma (Inr (gkey ctx))"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: not_entry no_edge pred no_enter bot0
    Let_def sides_of_rhs_seqcomp traverse_seqcomp)

lemma side_cfg_T_eff_keyed_seed_trees_entry:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes no_edge: "pred_sel g (cfg_entry g) = []"
    and no_combine: "return_call_action_list g (cfg_entry g) = []"
    and no_enter: "entry_call_list g (cfg_entry g) = []"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (cfg_entry g, ctx) sigma = DG s0d bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (cfg_entry g, ctx)) sigma (Inr (gkey ctx)) = DG bot s0g"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: no_edge no_combine no_enter bot0 Let_def)

subsection \<open>The heterogeneous seeded keyed generator\<close>

text \<open>
  The one context-generic generator.  Enter handling is routed by three hooks so
  that a monovariant and a context-sensitive analysis are both instances:

  \<^item> \<open>pred_sel g v ctx\<close> selects the intra predecessors folded as Answers into a node,
    each paired with the \<^emph>\<open>address\<close> in the solver's valuation space that carries its
    value.  \<open>intra_predecessor_addr_list\<close> over \<^const>\<open>intra\<close> addresses every
    predecessor at its own \<open>(pp, 'c)\<close> local unknown; a callee entry over
    \<^const>\<open>calls\<close> merges into the single callee context, while the
    context-sensitive instance instead publishes routed callee seeds.
  \<^item> \<open>cmb\<close> is the procedure-return combine tree (already fully abstract: the
    context-sensitive instance reads the callee exit under the routed context).
  \<^item> \<open>extra c v\<close> supplies additional per-node trees folded after the intra and
    combine trees.  Their Answers add to the node's local accumulator and their
    \<^const>\<open>Side\<close> effects are collected --- this is where a frame-entry seed
    \<^emph>\<open>read\<close> (a \<^const>\<open>QueryG\<close> of the incoming seed slot) and the caller-side
    call-entry \<^emph>\<open>publication\<close> (a routed \<^const>\<open>Side\<close> to the callee seed
    slot) live.  The monovariant instance supplies \<open>\<lambda>_ _. []\<close>.
\<close>

definition apply_dg_spec_at ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> edge_action \<Rightarrow> 'x + 'k \<Rightarrow> 'k \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state) strategy_tree"
where
  "apply_dg_spec_at S a src gk = dg_edge_tree_at (dg_spec_step S a) src gk"

definition apply_dg_spec_contribution_at ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> edge_action \<Rightarrow> 'x + 'k \<Rightarrow> 'k \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state) strategy_tree"
where
  "apply_dg_spec_contribution_at S a src gk =
     dg_edge_contribution_tree_at (dg_spec_step S a) src gk"

lemma apply_dg_spec_as_at:
  "apply_dg_spec S a u = apply_dg_spec_at S a (Inl u) ()"
  unfolding apply_dg_spec_def apply_dg_spec_at_def by (rule dg_edge_tree_as_at)

lemma apply_dg_spec_contribution_as_at:
  "apply_dg_spec_contribution S a u = apply_dg_spec_contribution_at S a (Inl u) ()"
  unfolding apply_dg_spec_contribution_def apply_dg_spec_contribution_at_def
  by (rule dg_edge_contribution_tree_as_at)

text \<open>The keyed analogue of \<^const>\<open>dg_spec_combine_tree\<close>: the caller and callee-exit
  reads and the published slot are addresses in the solver's own valuation space, not
  bare local unknowns and the fixed \<^typ>\<open>unit\<close> global key. Built the same way
  \<^const>\<open>apply_dg_spec_at\<close> is, over \<^const>\<open>dg_combine_tree_at\<close> instead of
  \<^const>\<open>dg_edge_tree_at\<close>.\<close>

definition dg_spec_combine_tree_at ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> call_info \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> 'k \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_spec_combine_tree_at S ci src_cc src_ex gk =
     dg_combine_tree_at
       (\<lambda>ci' dc de g. dgs_combine S ci' (dgs_caller_cont S ci' dc g) de g) ci src_cc src_ex gk"

lemma dg_spec_combine_tree_as_at:
  "dg_spec_combine_tree S ci cc ex = dg_spec_combine_tree_at S ci (Inl cc) (Inl ex) ()"
  unfolding dg_spec_combine_tree_def dg_spec_combine_tree_at_def by (rule dg_combine_tree_as_at)

text \<open>The standard predecessor selection: every intra predecessor is carried by its
  own \<open>(pp, 'c)\<close> local unknown, so its address is \<^const>\<open>Inl\<close> of that pair.\<close>

definition intra_predecessor_addr_list ::
  "cfg \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> ((pp \<times> 'c + 'k) \<times> edge_action) list"
where
  "intra_predecessor_addr_list g v ctx =
     map (\<lambda>(u, a). (Inl (u, ctx), a)) (intra_predecessor_list g v)"

definition side_cfg_T_eff_keyed_seed_dg ::
  "(cfg \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> ((pp \<times> 'c + 'k) \<times> edge_action) list)
   \<Rightarrow> ('c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree list)
   \<Rightarrow> cfg
   \<Rightarrow> ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
   \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
where
  "side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> s0d else bot0);
            intra = map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c))
                        (pred_sel g v c);
            comb = map (\<lambda>(cc, ca). cmb route c ca cc v)
                       (call_site_list g v);
            t = side_rhs_fold_dg acc0 (intra @ comb @ extra route c v)
        in if v = cfg_entry g then side_effect (gkey c) (DG bot s0g) t else t)"


lemma eq_side_cfg_T_eff_keyed_seed_dg:
  "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)
      (v, ctx) \<tau> =
   DG (side_acc_dg
     (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
     \<tau>
     (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey ctx))
           (pred_sel g v ctx)
      @ map (\<lambda>(cc, ca). cmb route ctx ca cc v)
            (call_site_list g v)
      @ extra route ctx v)) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def
        traverse_side_rhs_fold_dg)

lemma sides_side_cfg_T_eff_keyed_seed_dg:
  "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g
      (v, ctx)) \<tau> (Inr (gkey ctx)) =
   (if v = cfg_entry g then DG bot s0g else bot)
   \<squnion> foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
       (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey ctx))
          (pred_sel g v ctx)
        @ map (\<lambda>(cc, ca). cmb route ctx ca cc v) (call_site_list g v)
        @ extra route ctx v) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def sides_of_rhs_side_rhs_fold_dg_char
        bot_dg_state_def[symmetric] ac_simps)

subsection \<open>Buffered generator: fold Side-free contributions, publish once\<close>

text \<open>
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close> writes a node's own key once per contribution: a
  merge node with several intra predecessors, or several return call actions, each
  independently publishes a \<open>Side (gkey c) ...\<close> via \<^const>\<open>dg_edge_tree\<close>/\<open>routed_cmb_g\<close>'s
  own \<^const>\<open>side_effect\<close>, so several writes to the same \<open>gkey c\<close> land in one RHS
  evaluation. \<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close> folds Side-free contribution trees
  (\<^const>\<open>apply_dg_spec_contribution\<close> for \<open>intra\<close>; the caller's own Side-free \<open>cmb_c\<close> for
  \<open>comb\<close>) with \<^const>\<open>fold_rhs_trees\<close> and publishes \<open>gkey c\<close> once, after every
  contribution has been read.

  That fold shapes the node's \<^emph>\<open>own\<close> key, but \<open>extra route c v\<close> stays a list of
  independent trees, and a caller node's extras publish one routed callee seed per call
  action. Two call sites resuming at the same node therefore still name one seed key
  twice. \<^const>\<open>buffer_sides\<close> closes that case for every key uniformly, so
  \<open>distinct_side_path_buffer_sides\<close> --- not an argument about which keys the hooks
  happen to choose --- is what establishes at most one \<^const>\<open>Side\<close> per key per RHS
  evaluation. It preserves the declarative
  \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value, so the correspondence with the
  unbuffered generator below is unaffected.
\<close>

definition side_cfg_T_eff_keyed_seed_dg_buffered ::
  "(cfg \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> ((pp \<times> 'c + 'k) \<times> edge_action) list)
   \<Rightarrow> ('c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree list)
   \<Rightarrow> cfg
   \<Rightarrow> ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
   \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
where
  "side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot);
            intra = map (\<lambda>(src, a). apply_dg_spec_contribution_at S a src (gkey c))
                        (pred_sel g v c);
            comb = map (\<lambda>(cc, ca). cmb_c route c ca cc v) (call_site_list g v);
            t = fold_rhs_trees acc0 (intra @ comb @ extra route c v)
        in buffer_sides (do {
          res \<leftarrow> t;
          side_effect (gkey c) (DG bot (globs res)) (answer (DG (locals res) bot))
        }))"

lemma eq_side_cfg_T_eff_keyed_seed_dg_buffered:
  "eq (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g)
      (v, ctx) \<tau> =
   DG (locals (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc')
     (map (\<lambda>(src, a). apply_dg_spec_contribution_at S a src (gkey ctx)) (pred_sel g v ctx)
      @ map (\<lambda>(cc, ca). cmb_c route ctx ca cc v) (call_site_list g v)
      @ extra route ctx v)
     (if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot))) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def traverse_fold_rhs_trees_char)

lemma sides_apply_dg_spec_contribution_at:
  "sides_of_rhs (apply_dg_spec_contribution_at S a src gk) \<tau> z = bot"
  unfolding apply_dg_spec_contribution_at_def
  by (rule sides_dg_edge_contribution_tree_at)

lemma foldr_sup_bot_of_all_bot:
  fixes L :: "'a list" and h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes "\<And>x. x \<in> set L \<Longrightarrow> h x = bot"
  shows "foldr (\<lambda>x acc'. h x \<squnion> acc') L bot = bot"
  using assms by (induction L) simp_all

lemma sides_side_cfg_T_eff_keyed_seed_dg_buffered:
  assumes comb_free_at_key: "\<And>c' ca cc ex \<sigma>. sides_of_rhs (cmb_c route c' ca cc ex) \<sigma> (Inr (gkey c')) = bot"
    and extra_free: "\<And>c' w \<sigma> z x. x \<in> set (extra route c' w) \<Longrightarrow> sides_of_rhs x \<sigma> z = bot"
  shows "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
      (v, ctx)) \<tau> (Inr (gkey ctx)) =
   DG bot (globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc')
     (map (\<lambda>(src, a). apply_dg_spec_contribution_at S a src (gkey ctx)) (pred_sel g v ctx)
      @ map (\<lambda>(cc, ca). cmb_c route ctx ca cc v) (call_site_list g v)
      @ extra route ctx v)
     (if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot)))"
proof -
  have free: "\<And>w \<sigma> x. x \<in> set (map (\<lambda>(src, a). apply_dg_spec_contribution_at S a src (gkey ctx))
                    (pred_sel g w ctx)
      @ map (\<lambda>(cc, ca). cmb_c route ctx ca cc w) (call_site_list g w)
      @ extra route ctx w) \<Longrightarrow> sides_of_rhs x \<sigma> (Inr (gkey ctx)) = bot"
    using comb_free_at_key extra_free sides_apply_dg_spec_contribution_at
    by fastforce
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have z0: "sides_of_rhs (fold_rhs_trees (DG (bot0 \<squnion> s0d) s0g)
        (map (\<lambda>(src, a). apply_dg_spec_contribution_at S a src (gkey ctx))
             (pred_sel g (cfg_entry g) ctx)
         @ map (\<lambda>(cc, ca). cmb_c route ctx ca cc (cfg_entry g)) (call_site_list g (cfg_entry g))
         @ extra route ctx (cfg_entry g))) \<tau> (Inr (gkey ctx)) = bot"
      by (simp only: sides_of_rhs_fold_rhs_trees_char
          foldr_sup_bot_of_all_bot[OF free[where w = "cfg_entry g"]])
    from True show ?thesis
      by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def traverse_fold_rhs_trees_char
          bot_dg_state_def sup_dg_state_def z0)
  next
    case False
    have z0: "sides_of_rhs (fold_rhs_trees (DG bot0 bot)
        (map (\<lambda>(src, a). apply_dg_spec_contribution_at S a src (gkey ctx)) (pred_sel g v ctx)
         @ map (\<lambda>(cc, ca). cmb_c route ctx ca cc v) (call_site_list g v)
         @ extra route ctx v)) \<tau> (Inr (gkey ctx)) = bot"
      by (simp only: sides_of_rhs_fold_rhs_trees_char
          foldr_sup_bot_of_all_bot[OF free[where w = v]])
    from False show ?thesis
      by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def traverse_fold_rhs_trees_char
          bot_dg_state_def sup_dg_state_def z0)
  qed
qed

subsection \<open>Correspondence: the buffered generator matches the original\<close>

lemma apply_dg_spec_contribution_at_matches_local:
  "locals (traverse_rhs (apply_dg_spec_contribution_at S a src gk) \<tau>)
     = locals (traverse_rhs (apply_dg_spec_at S a src gk) \<tau>)"
  by (simp add: apply_dg_spec_contribution_at_def apply_dg_spec_at_def
        traverse_dg_edge_contribution_tree_at traverse_dg_edge_tree_at)

lemma apply_dg_spec_contribution_at_matches_global:
  "globs (traverse_rhs (apply_dg_spec_contribution_at S a src gk) \<tau>)
     = globs (sides_of_rhs (apply_dg_spec_at S a src gk) \<tau> (Inr gk))"
  by (simp add: apply_dg_spec_contribution_at_def apply_dg_spec_at_def
        traverse_dg_edge_contribution_tree_at sides_dg_edge_tree_at)

lemma apply_dg_spec_contribution_at_dep_aux:
  "dep_aux \<tau> (apply_dg_spec_contribution_at S a src gk)
     = dep_aux \<tau> (apply_dg_spec_at S a src gk)"
  by (simp add: apply_dg_spec_contribution_at_def apply_dg_spec_at_def
        dep_aux_dg_edge_contribution_tree_at dep_aux_dg_edge_tree_at)

lemma side_acc_dg_eq_foldr:
  "side_acc_dg acc \<tau> ts = foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') ts acc"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  have "foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') ts (acc \<squnion> locals (traverse_rhs a \<tau>))
      = locals (traverse_rhs a \<tau>) \<squnion> foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') ts acc"
    by (simp add: sup_commute[of acc] foldr_sup_seed_swap)
  then show ?case using Cons.IH by simp
qed

text \<open>
  A pointwise correspondence between two parallel contribution lists -- one Side-free
  (feeding \<^const>\<open>fold_rhs_trees\<close>), one Side-emitting (feeding \<^const>\<open>side_rhs_fold_dg\<close>)
  -- lifts to their whole-list fold, in both the local-answer and global-side
  components. This is the list-level engine behind
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered_correspondence\<close>: each of \<open>intra\<close>, \<open>comb\<close>, and
  \<open>extra\<close> instantiates it once, and \<open>foldr_append\<close> combines the three.
\<close>

lemma fold_rhs_trees_side_rhs_fold_dg_local_char:
  assumes h: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
                L_new L_old"
  shows "foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') L_new (acc::'d::bounded_semilattice_sup_bot)
       = foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') L_old acc"
  using h by (induction rule: list_all2_induct) simp_all

lemma foldr_globs_sides_char:
  fixes L :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
                strategy_tree list"
  shows "foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> z) \<squnion> acc') L bot
       = globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') L bot)"
  by (induction L) (simp_all add: bot_dg_state_def sup_dg_state_def)

lemma DG_sup_bot_left:
  "DG (bot::'d::bounded_semilattice_sup_bot) a \<squnion> DG bot b = DG bot (a \<squnion> b)"
  by (simp add: sup_dg_state_def bot_dg_state_def)

lemma foldr_sides_locals_bot:
  fixes L :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
                strategy_tree list"
  assumes "\<And>t. t \<in> set L \<Longrightarrow> locals (sides_of_rhs t \<tau> z) = bot"
  shows "locals (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') L bot) = bot"
  using assms
proof (induction L)
  case Nil
  then show ?case by (simp add: bot_dg_state_def)
next
  case (Cons t ts)
  then show ?case by (simp add: sup_dg_state_def)
qed

lemma list_all2_map_diag:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P (f x) (g x)) \<Longrightarrow> list_all2 P (map f xs) (map g xs)"
  by (induction xs) simp_all

lemma sides_of_rhs_Inl_bot:
  "sides_of_rhs T \<sigma> (Inl x) = bot"
  by (induction T arbitrary: \<sigma>) (auto simp: Let_def)

lemma list_all2_Union_eq:
  assumes "list_all2 (\<lambda>a b. f a = g b) xs ys"
  shows "(\<Union>x\<in>set xs. f x) = (\<Union>y\<in>set ys. g y)"
  using assms by (induction rule: list_all2_induct) auto

lemma locals_foldr_generic:
  "locals (foldr (\<lambda>t acc'. h t \<squnion> acc') L
      (acc::('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state))
     = foldr (\<lambda>t acc'. locals (h t) \<squnion> acc') L (locals acc)"
  by (induction L) (simp_all add: sup_dg_state_def)

lemma globs_foldr_generic:
  "globs (foldr (\<lambda>t acc'. h t \<squnion> acc') L
      (acc::('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state))
     = foldr (\<lambda>t acc'. globs (h t) \<squnion> acc') L (globs acc)"
  by (induction L) (simp_all add: sup_dg_state_def)

lemma foldr_join_seed_out:
  "foldr (\<lambda>t acc'. h t \<squnion> acc') ts (a::'a::bounded_semilattice_sup_bot)
     = a \<squnion> foldr (\<lambda>t acc'. h t \<squnion> acc') ts bot"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then show ?case by (simp add: ac_simps)
qed

lemma fold_rhs_trees_side_rhs_fold_dg_global_char:
  assumes h: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>) = globs (sides_of_rhs t_old \<tau> z))
                L_new L_old"
  shows "foldr (\<lambda>t acc'. globs (traverse_rhs t \<tau>) \<squnion> acc') L_new (acc::'h::bounded_semilattice_sup_bot)
       = foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> z) \<squnion> acc') L_old acc"
  using h by (induction rule: list_all2_induct) simp_all

text \<open>
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close>'s declarative value matches
  \<open>side_cfg_T_eff_keyed_seed_dg\<close>'s, given that \<open>cmb_c\<close> is the Side-free contribution
  analogue of \<open>cmb\<close> at the SAME \<open>gkey ctx\<close> slot (\<open>comb_t\<close>/\<open>comb_s\<close>/\<open>comb_free\<close> --
  \<open>routed_cmb_g_contribution\<close>/\<open>routed_cmb_g\<close> discharge these, per
  \<open>routed_cmb_g_contribution_matches_local\<close>/\<open>_global\<close> in \<open>Routed_Context\<close>) and \<open>extra\<close> is
  Side-free and answers only its local slot (\<open>extra_free\<close>/\<open>extra_local_only\<close> --
  \<open>routed_extra_g\<close> discharges both by direct inspection, since it answers via
  \<open>answer_local\<close> and issues no \<open>Side\<close>). \<open>intra\<close> needs no hypothesis:
  \<^const>\<open>apply_dg_spec_contribution\<close> vs \<^const>\<open>apply_dg_spec\<close> match unconditionally, for
  any \<open>dg_spec\<close>.
\<close>

lemma apply_dg_spec_side_pure_at:
  "locals (sides_of_rhs (apply_dg_spec_at S a src gk) \<tau> (Inr gk)) = bot"
  by (simp add: apply_dg_spec_at_def sides_dg_edge_tree_at)

lemma side_cfg_T_eff_keyed_seed_dg_buffered_correspondence:
  fixes cmb cmb_c ::
    "(pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
       \<Rightarrow> (pp \<times> 'c, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
            strategy_tree"
  assumes comb_t: "\<And>c' ca cc ex \<tau>. locals (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = locals (traverse_rhs (cmb route c' ca cc ex) \<tau>)"
    and comb_side_pure: "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c'))) = bot"
    and comb_s: "\<And>c' ca cc ex \<tau>. globs (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = globs (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c')))"
    and comb_free_at_key: "\<And>c' ca cc ex \<tau>. sides_of_rhs (cmb_c route c' ca cc ex) \<tau> (Inr (gkey c')) = bot"
    and comb_sides_off_key: "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr (gkey c')
                     \<Longrightarrow> sides_of_rhs (cmb_c route c' ca cc ex) \<tau> z = sides_of_rhs (cmb route c' ca cc ex) \<tau> z"
    and comb_dep: "\<And>c' ca cc ex \<tau>. dep_aux \<tau> (cmb_c route c' ca cc ex) = dep_aux \<tau> (cmb route c' ca cc ex)"
    and extra_free: "\<And>c' w \<tau> z x. x \<in> set (extra route c' w) \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
    and extra_local_only: "\<And>c' w \<tau> x. x \<in> set (extra route c' w) \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
  shows "traverse_rhs
           (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
             (v, ctx)) \<tau>
         = traverse_rhs
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>"
    (is ?T)
    and "dep_aux \<tau>
           (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g (v, ctx))
         = dep_aux \<tau>
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx))"
    (is ?D)
    and "sides_of_rhs
           (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
             (v, ctx)) \<tau>
         = sides_of_rhs
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>"
    (is ?S)
proof -
  let ?intra_new = "map (\<lambda>(src, a). apply_dg_spec_contribution_at S a src (gkey ctx))
                        (pred_sel g v ctx)"
  let ?intra_old = "map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey ctx)) (pred_sel g v ctx)"
  let ?comb_new = "map (\<lambda>(cc, ca). cmb_c route ctx ca cc v) (call_site_list g v)"
  let ?comb_old = "map (\<lambda>(cc, ca). cmb route ctx ca cc v) (call_site_list g v)"
  let ?extra = "extra route ctx v"
  let ?acc0 = "if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot"
  have intra_local: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      ?intra_new ?intra_old"
    by (rule list_all2_map_diag) (auto simp: apply_dg_spec_contribution_at_matches_local)
  have intra_global: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                    = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx)))) ?intra_new ?intra_old"
    by (rule list_all2_map_diag) (auto simp: apply_dg_spec_contribution_at_matches_global)
  have comb_local: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_t)
  have comb_global: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                   = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx)))) ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_s)
  have extra_local: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      ?extra ?extra"
    by (rule list.rel_refl_strong) simp
  have extra_global: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                    = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx)))) ?extra ?extra"
    by (rule list.rel_refl_strong) (simp add: extra_free extra_local_only bot_dg_state_def)
  have local_list: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_local comb_local extra_local by (intro list_all2_appendI)
  have global_list: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                   = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx))))
      (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_global comb_global extra_global by (intro list_all2_appendI)
  show ?T
  proof -
    have "traverse_rhs
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
          (v, ctx)) \<tau>
        = DG (locals (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0)) bot"
      by (rule eq_side_cfg_T_eff_keyed_seed_dg_buffered)
    also have "\<dots> = DG (foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc')
                     (?intra_new @ ?comb_new @ ?extra) (locals ?acc0)) bot"
      by (simp add: locals_foldr_generic)
    also have "\<dots> = DG (foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc')
                     (?intra_old @ ?comb_old @ ?extra) (locals ?acc0)) bot"
      by (simp only: fold_rhs_trees_side_rhs_fold_dg_local_char[OF local_list])
    also have "\<dots> = DG (side_acc_dg (locals ?acc0) \<tau> (?intra_old @ ?comb_old @ ?extra)) bot"
      by (simp add: side_acc_dg_eq_foldr)
    also have "\<dots> = traverse_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>"
      by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
    finally show ?thesis .
  qed
  have global_new: "sides_of_rhs
      (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
        (v, ctx)) \<tau> (Inr (gkey ctx))
      = DG bot (globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0))"
    by (intro sides_side_cfg_T_eff_keyed_seed_dg_buffered) (use comb_free_at_key extra_free in blast)+
  have globs_new_char: "globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0)
      = globs ?acc0
        \<squnion> foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> (Inr (gkey ctx))) \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
  proof -
    have "globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0)
        = foldr (\<lambda>t acc'. globs (traverse_rhs t \<tau>) \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) (globs ?acc0)"
      by (rule globs_foldr_generic)
    also have "\<dots> = foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> (Inr (gkey ctx))) \<squnion> acc')
                     (?intra_old @ ?comb_old @ ?extra) (globs ?acc0)"
      by (simp only: fold_rhs_trees_side_rhs_fold_dg_global_char[OF global_list])
    also have "\<dots> = globs ?acc0
                     \<squnion> foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> (Inr (gkey ctx))) \<squnion> acc')
                         (?intra_old @ ?comb_old @ ?extra) bot"
      by (rule foldr_join_seed_out)
    finally show ?thesis .
  qed
  have old_elem_side_pure: "\<And>t. t \<in> set (?intra_old @ ?comb_old @ ?extra)
      \<Longrightarrow> locals (sides_of_rhs t \<tau> (Inr (gkey ctx))) = bot"
    using comb_side_pure extra_free
    by (auto simp: apply_dg_spec_side_pure_at bot_dg_state_def split: prod.splits)
  have old_fold_side_pure: "locals
      (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot)
      = bot"
    by (rule foldr_sides_locals_bot) (rule old_elem_side_pure)
  have old_fold_collapse: "foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
      (?intra_old @ ?comb_old @ ?extra) bot
      = DG bot (globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
           (?intra_old @ ?comb_old @ ?extra) bot))"
    using old_fold_side_pure by (cases "foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
           (?intra_old @ ?comb_old @ ?extra) bot") simp
  have old_sides: "sides_of_rhs
      (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
      (Inr (gkey ctx))
      = DG bot (globs ?acc0
                \<squnion> globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
                     (?intra_old @ ?comb_old @ ?extra) bot))"
  proof -
    have "sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
        (Inr (gkey ctx))
        = (if v = cfg_entry g then DG bot s0g else bot)
          \<squnion> foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
              (?intra_old @ ?comb_old @ ?extra) bot"
      by (rule sides_side_cfg_T_eff_keyed_seed_dg)
    also have "\<dots> = DG bot (globs ?acc0
          \<squnion> globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
              (?intra_old @ ?comb_old @ ?extra) bot))"
      by (subst old_fold_collapse) (cases "v = cfg_entry g", simp_all add: DG_sup_bot_left bot_dg_state_def)
    finally show ?thesis .
  qed
  have S_at_key: "sides_of_rhs
      (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
        (v, ctx)) \<tau> (Inr (gkey ctx))
      = sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
        (Inr (gkey ctx))"
  proof -
    have "sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
          (v, ctx)) \<tau> (Inr (gkey ctx))
        = DG bot (globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0))"
      by (rule global_new)
    also have "\<dots> = DG bot (globs ?acc0
        \<squnion> globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
             (?intra_old @ ?comb_old @ ?extra) bot))"
      by (simp only: globs_new_char foldr_globs_sides_char)
    also have "\<dots> = sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
        (Inr (gkey ctx))"
      by (rule old_sides[symmetric])
    finally show ?thesis .
  qed
  have intra_dep: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old) ?intra_new ?intra_old"
    by (rule list_all2_map_diag) (auto simp: apply_dg_spec_contribution_at_dep_aux)
  have comb_dep_list: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old) ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_dep)
  have extra_dep: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old) ?extra ?extra"
    by (rule list.rel_refl_strong) simp
  have dep_list: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old)
      (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_dep comb_dep_list extra_dep by (intro list_all2_appendI)
  show ?D
  proof -
    have "dep_aux \<tau>
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g (v, ctx))
        = (\<Union>t\<in>set (?intra_new @ ?comb_new @ ?extra). dep_aux \<tau> t)"
      by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def dep_aux_seqcomp
          dep_aux_fold_rhs_trees_char)
    also have "\<dots> = (\<Union>t\<in>set (?intra_old @ ?comb_old @ ?extra). dep_aux \<tau> t)"
      by (rule list_all2_Union_eq[OF dep_list])
    also have "\<dots> = dep_aux \<tau>
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx))"
      by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def dep_aux_seqcomp
          dep_aux_side_rhs_fold_dg_char)
    finally show ?thesis .
  qed
  have intra_sides_off: "\<And>z. z \<noteq> Inr (gkey ctx)
      \<Longrightarrow> list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z) ?intra_new ?intra_old"
  proof -
    fix z :: "cfg_node \<times> 'c + 'k"
    assume z: "z \<noteq> Inr (gkey ctx)"
    have old_bot: "\<And>src a. sides_of_rhs (apply_dg_spec_at S a src (gkey ctx)) \<tau> z = bot"
      unfolding apply_dg_spec_at_def by (rule sides_dg_edge_tree_at_other[OF z])
    show "list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z) ?intra_new ?intra_old"
      by (rule list_all2_map_diag)
         (auto simp: sides_apply_dg_spec_contribution_at old_bot)
  qed
  have comb_sides_off: "\<And>z. z \<noteq> Inr (gkey ctx)
      \<Longrightarrow> list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z) ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_sides_off_key)
  have extra_sides_off: "\<And>z. list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z)
      ?extra ?extra"
    by (rule list.rel_refl_strong) simp
  have sides_list_off: "\<And>z. z \<noteq> Inr (gkey ctx)
      \<Longrightarrow> list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z)
          (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_sides_off comb_sides_off extra_sides_off by (intro list_all2_appendI)
  have fold_sides_off: "\<And>z. z \<noteq> Inr (gkey ctx) \<Longrightarrow>
      foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) bot
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
  proof -
    fix z :: "cfg_node \<times> 'c + 'k"
    assume z: "z \<noteq> Inr (gkey ctx)"
    show "foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) bot
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
      using sides_list_off[OF z] by (induction rule: list_all2_induct) simp_all
  qed
  show ?S
  proof (rule ext)
    fix z
    show "sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
          (v, ctx)) \<tau> z
      = sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau> z"
    proof (cases "z = Inr (gkey ctx)")
      case True
      with S_at_key show ?thesis by simp
    next
      case False
      have new_off: "sides_of_rhs
          (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
            (v, ctx)) \<tau> z
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) bot"
        using False
        by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def sides_of_rhs_seqcomp
            sides_of_rhs_fold_rhs_trees_char bot_dg_state_def[symmetric])
      have old_off: "sides_of_rhs
          (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau> z
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
        using False
        by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def sides_of_rhs_fold_rhs_trees_char
            sides_of_rhs_side_rhs_fold_dg_char)
      from new_off old_off fold_sides_off[OF False] show ?thesis by simp
    qed
  qed
qed

text \<open>
  The observational interface \<^const>\<open>part_post_solution\<close> actually consumes: given the
  correspondence, a buffered post-solution is also an unbuffered one. Callers only need
  this fact, never the tree-shape argument behind \<open>side_cfg_T_eff_keyed_seed_dg_buffered_correspondence\<close>
  itself -- \<^const>\<open>part_post_solution\<close>'s three conjuncts (\<open>dep\<^sub>L\<close>, \<open>eq\<close>, \<open>sides_of_rhs\<close>) are
  exactly \<open>?D\<close>/\<open>?T\<close>/\<open>?S\<close>, read pointwise at each \<open>u \<in> vars\<close>.
\<close>

lemma part_post_solution_seed_dg_buffered_to_old:
  fixes cmb cmb_c ::
    "(pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
       \<Rightarrow> (pp \<times> 'c, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
            strategy_tree"
  assumes comb_t: "\<And>c' ca cc ex \<tau>. locals (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = locals (traverse_rhs (cmb route c' ca cc ex) \<tau>)"
    and comb_side_pure: "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c'))) = bot"
    and comb_s: "\<And>c' ca cc ex \<tau>. globs (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = globs (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c')))"
    and comb_free_at_key: "\<And>c' ca cc ex \<tau>. sides_of_rhs (cmb_c route c' ca cc ex) \<tau> (Inr (gkey c')) = bot"
    and comb_sides_off_key: "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr (gkey c')
                     \<Longrightarrow> sides_of_rhs (cmb_c route c' ca cc ex) \<tau> z = sides_of_rhs (cmb route c' ca cc ex) \<tau> z"
    and comb_dep: "\<And>c' ca cc ex \<tau>. dep_aux \<tau> (cmb_c route c' ca cc ex) = dep_aux \<tau> (cmb route c' ca cc ex)"
    and extra_free: "\<And>c' w \<tau> z x. x \<in> set (extra route c' w) \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
    and extra_local_only: "\<And>c' w \<tau> x. x \<in> set (extra route c' w) \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
    and pp_buf: "part_post_solution
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g)
        x sigma vars"
  shows "part_post_solution
      (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) x sigma vars"
proof -
  let ?Tbuf = "side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g"
  let ?Told = "side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g"
  have corr: "\<And>u. traverse_rhs (?Tbuf u) sigma = traverse_rhs (?Told u) sigma
      \<and> dep_aux sigma (?Tbuf u) = dep_aux sigma (?Told u)
      \<and> sides_of_rhs (?Tbuf u) sigma = sides_of_rhs (?Told u) sigma"
  proof -
    fix u :: "pp \<times> 'c"
    obtain v ctx where u: "u = (v, ctx)" by (cases u) auto
    show "traverse_rhs (?Tbuf u) sigma = traverse_rhs (?Told u) sigma
        \<and> dep_aux sigma (?Tbuf u) = dep_aux sigma (?Told u)
        \<and> sides_of_rhs (?Tbuf u) sigma = sides_of_rhs (?Told u) sigma"
      unfolding u
      using side_cfg_T_eff_keyed_seed_dg_buffered_correspondence
              [where cmb = cmb and cmb_c = cmb_c and route = route and gkey = gkey,
               OF comb_t comb_side_pure comb_s comb_free_at_key comb_sides_off_key comb_dep
                  extra_free extra_local_only]
      by simp
  qed
  from pp_buf have x_in: "x \<in> vars" by simp
  have "\<forall>u\<in>vars. dep\<^sub>L ?Told sigma u \<subseteq> vars \<and> eq ?Told u sigma \<le> sigma (Inl u)
      \<and> sides_of_rhs (?Told u) sigma \<le> sigma"
  proof
    fix u assume uv: "u \<in> vars"
    with pp_buf have buf: "dep\<^sub>L ?Tbuf sigma u \<subseteq> vars" "eq ?Tbuf u sigma \<le> sigma (Inl u)"
        "sides_of_rhs (?Tbuf u) sigma \<le> sigma"
      by auto
    have dL: "dep\<^sub>L ?Told sigma u = dep\<^sub>L ?Tbuf sigma u"
      using corr[of u] unfolding dep\<^sub>L_def dep_def by simp
    have eqv: "eq ?Told u sigma = eq ?Tbuf u sigma"
      using corr[of u] by simp
    have sv: "sides_of_rhs (?Told u) sigma = sides_of_rhs (?Tbuf u) sigma"
      using corr[of u] by simp
    show "dep\<^sub>L ?Told sigma u \<subseteq> vars \<and> eq ?Told u sigma \<le> sigma (Inl u) \<and> sides_of_rhs (?Told u) sigma \<le> sigma"
      unfolding dL eqv sv using buf by simp
  qed
  with x_in show ?thesis by simp
qed

subsection \<open>Threefold monotonicity for an arbitrary generator instance\<close>

text \<open>
  The three
  @{const TD_side_mono} preconditions reduce to a per-tree contract on the
  intra, combine, and extra hooks, discharged once here and reusable at every
  routing policy --- a routed context policy is then a second interpretation
  of this reduction, not a second monotonicity proof. The outer @{const Side}
  wrapper at @{term "cfg_entry g"} is invisible to @{const traverse_rhs} and
  @{const dep_aux} (a \<^const>\<open>Side\<close> node only ever repackages, never queries);
  it only has to be threaded through the @{const sides_of_rhs} case via
  \<open>fun_upd_sup_mono\<close>, below.
\<close>

lemma side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen:
  fixes g :: cfg
    and S :: "('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec"
  assumes intra_mono: "\<forall>v c src a s1 s2. (src, a) \<in> set (pred_sel g v c) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs (apply_dg_spec_at S a src (gkey c)) s1
        \<le> traverse_rhs (apply_dg_spec_at S a src (gkey c)) s2"
  assumes comb_mono: "\<forall>v c cc ca s1 s2. (cc, ca) \<in> set (call_site_list g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs (cmb route c ca cc v) s1 \<le> traverse_rhs (cmb route c ca cc v) s2"
  assumes extra_mono: "\<forall>v c t s1 s2. t \<in> set (extra route c v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs t s1 \<le> traverse_rhs t s2"
  shows "is_mono_eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
proof -
  have key: "\<And>v c s1 s2. s1 \<le> s2 \<Longrightarrow>
      eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s1
        \<le> eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s2"
  proof -
    fix v c s1 s2
    show "s1 \<le> s2 \<Longrightarrow>
        eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s1
          \<le> eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s2"
    proof -
      assume le: "s1 \<le> s2"
      have tree_mono: "\<forall>t \<in> set (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c))
                                  (pred_sel g v c)
                            @ map (\<lambda>(cc, ca). cmb route c ca cc v) (call_site_list g v)
                            @ extra route c v).
                         \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
        using intra_mono comb_mono extra_mono by auto
      have step: "traverse_rhs (side_rhs_fold_dg (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
                     (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c)) (pred_sel g v c)
                       @ map (\<lambda>(cc, ca). cmb route c ca cc v) (call_site_list g v)
                       @ extra route c v)) s1
                  \<le> traverse_rhs (side_rhs_fold_dg (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
                     (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c)) (pred_sel g v c)
                       @ map (\<lambda>(cc, ca). cmb route c ca cc v) (call_site_list g v)
                       @ extra route c v)) s2"
        by (rule side_rhs_fold_dg_mono[OF tree_mono le])
      show "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s1
            \<le> eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s2"
        unfolding eq_side_cfg_T_eff_keyed_seed_dg using step
        by (simp add: traverse_side_rhs_fold_dg)
    qed
  qed
  show ?thesis
    unfolding is_mono_eq_def using key by fastforce
qed

text \<open>
  A generic fact about pointwise-ordered functions, function update, and join
  -- nothing here mentions a strategy tree. It has exactly one use, below:
  threading the outer \<open>Side\<close> wrapper at \<open>cfg_entry g\<close> through the
  \<^const>\<open>sides_of_rhs\<close> case, so it stays local to its one call site rather
  than living in generic infrastructure.
\<close>

lemma fun_upd_sup_mono:
  fixes m1 m2 :: "'b \<Rightarrow> 'a::bounded_semilattice_sup_bot"
  assumes "m1 \<le> m2"
  shows "m1(y := m1 y \<squnion> cd) \<le> m2(y := m2 y \<squnion> cd)"
proof -
  have eq: "\<And>m. m(y := m y \<squnion> cd) = m \<squnion> ((\<lambda>_. bot)(y := cd))"
    unfolding fun_upd_def sup_fun_def by (rule ext) simp
  show ?thesis unfolding eq by (rule sup_mono[OF assms order_refl])
qed

lemma side_cfg_T_eff_keyed_seed_dg_mono_sides_gen:
  fixes g :: cfg
    and S :: "('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec"
  assumes intra_sides_mono: "\<forall>v c src a s1 s2. (src, a) \<in> set (pred_sel g v c) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs (apply_dg_spec_at S a src (gkey c)) s1
        \<le> sides_of_rhs (apply_dg_spec_at S a src (gkey c)) s2"
  assumes comb_sides_mono: "\<forall>v c cc ca s1 s2. (cc, ca) \<in> set (call_site_list g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs (cmb route c ca cc v) s1 \<le> sides_of_rhs (cmb route c ca cc v) s2"
  assumes extra_sides_mono: "\<forall>v c t s1 s2. t \<in> set (extra route c v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs t s1 \<le> sides_of_rhs t s2"
  shows "mono_sides (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
proof -
  have key: "\<And>v c s1 s2. s1 \<le> s2 \<Longrightarrow>
      sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s1
        \<le> sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s2"
  proof -
    fix v c s1 s2
    show "s1 \<le> s2 \<Longrightarrow>
        sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s1
          \<le> sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s2"
    proof -
      assume le: "s1 \<le> s2"
      have tree_sides_mono: "\<And>w. \<forall>t \<in> set (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c))
                                  (pred_sel g w c)
                            @ map (\<lambda>(cc, ca). cmb route c ca cc w) (call_site_list g w)
                            @ extra route c w).
                         \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> sides_of_rhs t s1 \<le> sides_of_rhs t s2"
        using intra_sides_mono comb_sides_mono extra_sides_mono by auto
      have fold_le: "\<And>acc w. sides_of_rhs (side_rhs_fold_dg acc
                        (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c)) (pred_sel g w c)
                          @ map (\<lambda>(cc, ca). cmb route c ca cc w) (call_site_list g w)
                          @ extra route c w)) s1
                    \<le> sides_of_rhs (side_rhs_fold_dg acc
                        (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c)) (pred_sel g w c)
                          @ map (\<lambda>(cc, ca). cmb route c ca cc w) (call_site_list g w)
                          @ extra route c w)) s2"
        by (rule side_rhs_fold_dg_sides_mono[OF tree_sides_mono le])
      show "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s1
            \<le> sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s2"
        unfolding side_cfg_T_eff_keyed_seed_dg_def
        by (simp add: Let_def fold_le fun_upd_sup_mono[OF fold_le] split: if_splits)
    qed
  qed
  show ?thesis
    unfolding mono_sides_def using key by fastforce
qed

lemma side_cfg_T_eff_keyed_seed_dg_mono_deps_gen:
  fixes g :: cfg
    and S :: "('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec"
  assumes intra_static: "\<forall>v c src a. (src, a) \<in> set (pred_sel g v c) \<longrightarrow>
      env_indep_deps (apply_dg_spec_at S a src (gkey c))"
  assumes comb_static: "\<forall>v c cc ca. (cc, ca) \<in> set (call_site_list g v) \<longrightarrow>
      env_indep_deps (cmb route c ca cc v)"
  assumes extra_static: "\<forall>v c t. t \<in> set (extra route c v) \<longrightarrow> env_indep_deps t"
  shows "mono_deps (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
proof -
  have key: "\<And>v c s1 s2. s1 \<le> s2 \<Longrightarrow>
      dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s1 (v, c)
        \<subseteq> dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s2 (v, c)"
  proof -
    fix v c s1 s2
    have tree_static: "\<And>w. \<forall>t \<in> set (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c))
                                (pred_sel g w c)
                          @ map (\<lambda>(cc, ca). cmb route c ca cc w) (call_site_list g w)
                          @ extra route c w).
                       env_indep_deps t"
      using intra_static comb_static extra_static by auto
    have fold_mono: "\<And>acc w. mono_tree_deps (side_rhs_fold_dg acc
                      (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c)) (pred_sel g w c)
                        @ map (\<lambda>(cc, ca). cmb route c ca cc w) (call_site_list g w)
                        @ extra route c w))"
      by (rule side_rhs_fold_dg_mono_tree_deps[OF tree_static])
    show "s1 \<le> s2 \<Longrightarrow>
        dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s1 (v, c)
          \<subseteq> dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s2 (v, c)"
    proof -
      assume ord: "s1 \<le> s2"
      have dsub: "\<And>acc w. dep_aux s1 (side_rhs_fold_dg acc
                    (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c)) (pred_sel g w c)
                      @ map (\<lambda>(cc, ca). cmb route c ca cc w) (call_site_list g w)
                      @ extra route c w))
                  \<subseteq> dep_aux s2 (side_rhs_fold_dg acc
                    (map (\<lambda>(src, a). apply_dg_spec_at S a src (gkey c)) (pred_sel g w c)
                      @ map (\<lambda>(cc, ca). cmb route c ca cc w) (call_site_list g w)
                      @ extra route c w))"
        using fold_mono[unfolded mono_tree_deps_def] ord by blast
      show "dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s1 (v, c)
              \<subseteq> dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s2 (v, c)"
        unfolding dep_def side_cfg_T_eff_keyed_seed_dg_def
        by (simp add: Let_def dsub split: if_splits)
    qed
    qed
  show ?thesis
    unfolding mono_deps_def using key by fastforce
qed


text \<open>
  The generator consumes \\\<^typ>\<open>('d, 'h) dg_spec\<close> directly: Answers carry
  \<open>D\<close>, Side publications carry \<open>G\<close>, and only
  \\\<^typ>\<open>('d, 'h) dg_state\<close> packs them for the vendor solver's single
  value parameter.
\<close>

end
