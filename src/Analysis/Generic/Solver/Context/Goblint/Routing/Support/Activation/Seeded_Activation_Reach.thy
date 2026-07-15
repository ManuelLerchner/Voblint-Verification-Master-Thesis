theory Seeded_Activation_Reach
  imports Seeded_Activation_Sound
begin

section \<open>Dependency reachability for the seeded generator\<close>

text \<open>
  The activation \<open>vars\<close> obligations (\<open>cov_edge\<close> / \<open>cov_frame\<close>) are discharged from the
  \<^emph>\<open>dependency\<close> closure that \<^const>\<open>part_post_solution\<close> already provides
  (\<open>u \<in> vars \<Longrightarrow> dep\<^sub>L T sg u \<subseteq> vars\<close>), not a new forward-closure invariant.  The key
  facts are that each activation edge/combine unknown appears in the dependency set of
  its successor RHS:

    \<^item> \<^bold>\<open>intra\<close>: a non-\<^const>\<open>EA_Enter\<close> predecessor \<open>(u, ctx)\<close> is a dependency of \<open>(v, ctx)\<close>
      (the clean edge tree \<^const>\<open>QueryL\<close>s the predecessor local slot);
    \<^item> \<^bold>\<open>combine\<close>: the caller call node \<open>(cc, ctx)\<close> and the routed callee \<^emph>\<open>exit\<close>
      \<open>(ex, callee_ctx)\<close> are dependencies of the return node \<open>(v, ctx)\<close> (supplied per
      combine, established for the rehydrating combine).

  \<^const>\<open>dep_aux\<close> ignores \<^const>\<open>Side\<close> targets (\<open>dep_aux \<sigma> (Side y d t) = dep_aux \<sigma> t\<close>), so
  the callee \<^emph>\<open>entry\<close> is \<^emph>\<open>not\<close> a direct dependency of the combine --- it is reached
  through the callee exit and the callee body's backward dependency chain.  This is why
  CFG reachability implies dependency reachability: the combine names the callee exit,
  and the exit depends back through the body to the entry.
\<close>

subsection \<open>Dependency of the clean edge tree and the relabelled intra summand\<close>

lemma dep_aux_clean_edge_tree:
  "dep_aux sg (clean_edge_tree f u) = {Inl u}"
  by (simp add: clean_edge_tree_def Let_def)

text \<open>\<^const>\<open>map_ltree\<close> relabels the local dependency keys by \<open>h\<close>; the clean edge tree
  then contributes exactly the relabelled predecessor.\<close>
lemma dep_aux_map_ltree_clean_edge_tree:
  "dep_aux sg (map_ltree h (clean_edge_tree f u)) = {Inl (h u)}"
  by (simp add: dep_aux_map_ltree dep_aux_clean_edge_tree)

text \<open>\<^const>\<open>map_gtree\<close> reroutes only global (\<^const>\<open>Inr\<close>) query keys, so it preserves
  every local (\<^const>\<open>Inl\<close>) dependency.\<close>
lemma Inl_dep_aux_map_gtree:
  "(Inl z \<in> dep_aux sg (map_gtree r t)) = (Inl z \<in> dep_aux (\<lambda>w. sg (map_sum id r w)) t)"
  by (induction t) auto

text \<open>The intra summand of the seeded generator depends on its predecessor local slot
  at the same context.\<close>
lemma Inl_dep_aux_intra_summand:
  "Inl (u, ctx) \<in> dep_aux sg
     (map_gtree (\<lambda>_. gkey ctx)
        (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u)))"
  by (simp add: Inl_dep_aux_map_gtree apply_etf_clean_etf dep_aux_map_ltree_clean_edge_tree)

subsection \<open>Dependency of the seeded RHS: the union over its summands\<close>

text \<open>The seeded fold's dependency set is the union of its summands' dependencies; the
  accumulator only lands in the final \<^const>\<open>Answer\<close> and contributes none.\<close>
lemma dep_aux_side_rhs_fold_ctx:
  "dep_aux sg (side_rhs_fold_ctx acc ts) = (\<Union>t\<in>set ts. dep_aux sg t)"
  by (induction ts arbitrary: acc) (auto simp: dep_aux_seqcomp)

text \<open>The seeded generator RHS at \<open>(v, ctx)\<close> depends exactly on the union of its intra
  and combine summands (the entry \<^const>\<open>Side\<close> wrapper adds no dependency).\<close>
lemma dep_aux_side_cfg_T_eff_cmp_seed:
  "dep_aux sg (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0 (v, ctx))
   = (\<Union>t\<in>set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                        (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                (non_enter_predecessor_list g v)
              @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v)).
        dep_aux sg t)"
  by (simp add: side_cfg_T_eff_cmp_seed_def Let_def dep_aux_side_rhs_fold_ctx)

text \<open>\<^bold>\<open>Intra dependency (task 2).\<close>  A non-\<^const>\<open>EA_Enter\<close> predecessor local slot
  \<open>(u, ctx)\<close> is a dependency of the successor \<open>(v, ctx)\<close> --- the clean edge tree
  \<^const>\<open>QueryL\<close>s it.\<close>
lemma Inl_dep_L_intra_pred:
  assumes "(u, a) \<in> set (non_enter_predecessor_list g v)"
  shows "(u, ctx) \<in> dep\<^sub>L
           (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) sg (v, ctx)"
proof -
  let ?t = "map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u))"
  let ?trees = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                      (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u)))
                  (non_enter_predecessor_list g v)
                @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v)"
  have d: "Inl (u, ctx) \<in> dep_aux sg ?t" by (rule Inl_dep_aux_intra_summand)
  have m: "?t \<in> set ?trees" using assms by (force intro: rev_image_eqI)
  have "Inl (u, ctx) \<in> (\<Union>t\<in>set ?trees. dep_aux sg t)" using d m by blast
  thus ?thesis
    unfolding dep\<^sub>L_def dep_def by (simp add: dep_aux_side_cfg_T_eff_cmp_seed)
qed

text \<open>\<^bold>\<open>Combine dependencies (task 2), supplied per combine.\<close>  If the combine tree
  \<^term>\<open>cmb ctx dst cc ex\<close> reads the caller call node and the routed callee exit --- as the
  rehydrating combine does --- both are dependencies of the return node \<open>(v, ctx)\<close>.\<close>
lemma Inl_dep_L_combine_summand:
  assumes mem: "(cc, ex, dst) \<in> set (combine_predecessor_list g v)"
    and dep: "Inl w \<in> dep_aux sg (cmb ctx dst cc ex)"
  shows "w \<in> dep\<^sub>L (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0) sg (v, ctx)"
proof -
  let ?trees = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                      (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                  (non_enter_predecessor_list g v)
                @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v)"
  have m: "cmb ctx dst cc ex \<in> set ?trees" using mem by (force intro: rev_image_eqI)
  have "Inl w \<in> (\<Union>t\<in>set ?trees. dep_aux sg t)" using dep m by blast
  thus ?thesis
    unfolding dep\<^sub>L_def dep_def by (simp add: dep_aux_side_cfg_T_eff_cmp_seed)
qed

subsection \<open>Backward vars-membership: a dependency of a solved unknown is solved\<close>

text \<open>The dependency-closure half of \<^const>\<open>part_post_solution\<close>, projected out.\<close>
lemma part_post_solution_depL_closed:
  assumes "part_post_solution T x sg vars" and "u \<in> vars"
  shows "dep\<^sub>L T sg u \<subseteq> vars"
  using assms by auto

text \<open>\<^bold>\<open>Task 4, intra.\<close>  A non-\<^const>\<open>EA_Enter\<close> predecessor of a solved unknown is
  solved --- the backward direction the dependency closure gives directly.\<close>
lemma intra_pred_in_vars:
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
  shows "(u, ctx) \<in> vars"
proof -
  have "(u, ctx) \<in> dep\<^sub>L
          (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) sg (v, ctx)"
    by (rule Inl_dep_L_intra_pred[OF mem])
  with part_post_solution_depL_closed[OF pp cov] show ?thesis by blast
qed

text \<open>\<^bold>\<open>Task 4, combine.\<close>  Any local slot read by the combine tree of a solved return
  node --- the caller call node and the routed callee exit --- is solved.\<close>
lemma combine_dep_in_vars:
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and mem: "(cc, ex, dst) \<in> set (combine_predecessor_list g v)"
    and dep: "Inl w \<in> dep_aux sg (cmb ctx dst cc ex)"
  shows "w \<in> vars"
proof -
  have "w \<in> dep\<^sub>L (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0) sg (v, ctx)"
    by (rule Inl_dep_L_combine_summand[where cmb = cmb and ctx = ctx, OF mem dep])
  with part_post_solution_depL_closed[OF pp cov] show ?thesis by blast
qed

subsection \<open>The enter edge carries no dependency: the caller is not a callee-entry dep\<close>

text \<open>
  \<^bold>\<open>The structural fact behind the \<open>cov_frame\<close> direction.\<close>  A frame entry \<open>fe\<close> whose only
  CFG predecessor is the (filtered) \<^const>\<open>EA_Enter\<close> edge --- no non-enter predecessor,
  no combine predecessor --- has an \<^emph>\<open>empty\<close> dependency set: the seeded generator drops
  the enter edge (\<^const>\<open>non_enter_predecessor_list\<close>) and replaces it with the constant
  \<^term>\<open>frame_seed ctx\<close>, which depends on nothing.  Hence the caller call node is \<^emph>\<open>not\<close> a
  dependency of the callee entry.  The caller/callee link is carried only \<^emph>\<open>backward\<close>
  through the combine at the return node (\<open>Inl_dep_L_combine_summand\<close>: the return depends
  on the caller call node and the routed callee exit), never \<^emph>\<open>forward\<close> along the enter
  edge.  So the forward \<open>cov_frame\<close> (caller source \<open>\<Longrightarrow>\<close> callee-entry solved) is not derivable
  from dependency closure at a callee-entry query; it is derivable only relative to a
  downstream query (the exit) whose backward cone reaches the callee entry through the
  return.  This is the generator's deliberate omission of the enter-edge dependency ---
  the R_read seed replaces the enter transfer, exactly the move that gains callee-local
  precision.
\<close>
lemma callee_entry_dep_L_empty:
  assumes "non_enter_predecessor_list g fe = []"
    and "combine_predecessor_list g fe = []"
  shows "dep\<^sub>L (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0)
           sg (fe, ctx) = {}"
  unfolding dep\<^sub>L_def dep_def
  by (simp add: dep_aux_side_cfg_T_eff_cmp_seed assms)

subsection \<open>Task 1: intra-dependency reachability stays in vars\<close>

text \<open>The dep-graph intra edge relation on program points: \<open>u\<close> precedes \<open>v\<close> when \<open>u\<close> is a
  non-\<^const>\<open>EA_Enter\<close> predecessor of \<open>v\<close> (the seeded RHS of \<open>(v, ctx)\<close> \<^const>\<open>QueryL\<close>s the
  local slot \<open>(u, ctx)\<close>).  Its reflexive-transitive closure is a callee body's backward
  chain from a solved exit to its entry.\<close>
definition intra_pred_rel :: "cfg \<Rightarrow> pp rel" where
  "intra_pred_rel g = {(u, v). u \<in> fst ` set (non_enter_predecessor_list g v)}"

text \<open>\<^bold>\<open>The reachability theorem (task 1).\<close>  If a solved query pins \<open>(v, ctx) \<in> vars\<close> and \<open>u\<close>
  reaches \<open>v\<close> through the intra dependency relation, then \<open>(u, ctx) \<in> vars\<close>.  Iterates the
  backward bridge \<open>intra_pred_in_vars\<close> along the closure: every intermediate
  \<open>(node, ctx)\<close> is a dependency of its (solved) successor, hence solved.  This is the callee
  body's exit-to-entry chain that carries the caller/callee link (\<open>Inl_dep_L_combine_summand\<close>
  names the callee exit; this reaches the entry) --- the concrete content of \<open>CFG reachability
  implies dependency reachability\<close> with no forward-closure invariant.\<close>
lemma intra_pred_reaches_in_vars:
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and reach: "(u, v) \<in> (intra_pred_rel g)\<^sup>*"
    and cov: "(v, ctx) \<in> vars"
  shows "(u, ctx) \<in> vars"
  using reach
proof (induction rule: converse_rtrancl_induct)
  case base show ?case by (rule cov)
next
  case (step y z)
  from step.hyps(1) obtain a where
    mem: "(y, a) \<in> set (non_enter_predecessor_list g z)"
    unfolding intra_pred_rel_def by auto
  show ?case by (rule intra_pred_in_vars[OF pp step.IH mem])
qed

text \<open>\<^bold>\<open>The unified cover (task 2).\<close>  The three dependency-membership facts together cover
  every activation rule against the query's solved dependency cone: \<open>intra_pred_in_vars\<close>
  (a non-enter predecessor of a solved node is solved --- the \<open>intra\<close> rule and the \<open>enter\<close>
  routing's continuation), \<open>combine_dep_in_vars\<close> (the caller call node and the routed
  callee exit read by a solved return node are solved --- the \<open>combine\<close> rule), and
  \<open>intra_pred_reaches_in_vars\<close> (the callee exit's backward body chain reaches the callee
  entry).  Chaining \<open>combine_dep_in_vars\<close> (return \<Longrightarrow> callee exit) into
  \<open>intra_pred_reaches_in_vars\<close> (callee exit \<Longrightarrow> callee entry) discharges the callee-frame
  membership from a solved return node, using only \<^const>\<open>part_post_solution\<close>'s dependency
  closure.\<close>

lemma combine_reaches_frame_in_vars:
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and mem: "(cc, ex, dst) \<in> set (combine_predecessor_list g v)"
    and dep: "Inl (ex, cex) \<in> dep_aux sg (cmb ctx dst cc ex)"
    and reach: "(fe, ex) \<in> (intra_pred_rel g)\<^sup>*"
  shows "(fe, cex) \<in> vars"
proof -
  have "(ex, cex) \<in> vars"
    by (rule combine_dep_in_vars[OF pp cov mem dep])
  thus ?thesis by (rule intra_pred_reaches_in_vars[OF pp reach])
qed

subsection \<open>The unified dependency-reachability theorem (task 1)\<close>

text \<open>\<open>act_reach g cmb sg q p\<close>: the unknown \<open>p\<close> is reachable from the query unknown \<open>q\<close>
  through the \<^emph>\<open>activation dependency graph\<close> of the seeded generator, folding all three
  activation rules into one relation:

    \<^item> \<^bold>\<open>intra\<close> --- a non-\<^const>\<open>EA_Enter\<close> predecessor \<open>(u, ctx)\<close> of a reached \<open>(v, ctx)\<close>;
    \<^item> \<^bold>\<open>combine\<close> --- any unknown \<open>w\<close> the combine tree \<open>cmb ctx dst cc ex\<close> of a reached return
      node \<open>(v, ctx)\<close> reads (the caller call node and the routed callee exit).

  The \<^bold>\<open>enter\<close> rule is not a separate constructor: a callee frame entry is reached by a
  \<open>combine\<close> step to the routed callee exit followed by \<open>intra\<close> steps up the callee body ---
  exactly the composition witnessed by \<open>combine_reaches_frame_in_vars\<close>.  \<^const>\<open>dep_aux\<close>
  drops \<^const>\<open>Side\<close> targets, so the callee entry is reached \<^emph>\<open>backward\<close> through the exit,
  never forward along the (seed-replaced) enter edge.\<close>

inductive act_reach ::
  "cfg \<Rightarrow> ('c \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a::bot abs_state) strategy_tree)
   \<Rightarrow> (pp \<times> 'c + 'g \<Rightarrow> 'a abs_state) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> bool"
  for g :: cfg
    and cmb :: "'c \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree"
    and sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
where
  base: "act_reach g cmb sg q q"
| intra: "act_reach g cmb sg q (v, ctx) \<Longrightarrow> (u, a) \<in> set (non_enter_predecessor_list g v)
      \<Longrightarrow> act_reach g cmb sg q (u, ctx)"
| combine: "act_reach g cmb sg q (v, ctx) \<Longrightarrow> (cc, ex, dst) \<in> set (combine_predecessor_list g v)
      \<Longrightarrow> Inl w \<in> dep_aux sg (cmb ctx dst cc ex) \<Longrightarrow> act_reach g cmb sg q w"

text \<open>\<^bold>\<open>Task 1 --- the generic dependency-reachability theorem.\<close>  Every unknown reachable
  from a solved query through the activation dependency graph is itself solved.  The proof
  is one induction on \<open>act_reach\<close>, discharging the \<open>intra\<close> step by \<open>intra_pred_in_vars\<close> and
  the \<open>combine\<close> step by \<open>combine_dep_in_vars\<close> --- both projections of
  \<^const>\<open>part_post_solution\<close>'s backward dependency closure
  (\<open>u \<in> vars \<Longrightarrow> dep\<^sub>L T sg u \<subseteq> vars\<close>).  No forward-closure invariant is added.\<close>

theorem act_reach_in_vars:
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and r: "act_reach g cmb sg q p"
    and q: "q \<in> vars"
  shows "p \<in> vars"
  using r q
proof (induction rule: act_reach.induct)
  case (base q) thus ?case by simp
next
  case (intra q v ctx u a)
  have "(v, ctx) \<in> vars" using intra.IH intra.prems by blast
  thus ?case by (rule intra_pred_in_vars[OF pp _ intra.hyps(2)])
next
  case (combine q v ctx cc ex w)
  have "(v, ctx) \<in> vars" using combine.IH combine.prems by blast
  thus ?case by (rule combine_dep_in_vars[OF pp _ combine.hyps(2,3)])
qed

subsection \<open>Task 2: the enter rule as a first-class act_reach chain\<close>

text \<open>An \<^const>\<open>intra_pred_rel\<close> step lifts to an \<open>act_reach\<close> \<open>intra\<close> step at a fixed
  context: if \<open>(z, ctx)\<close> is reachable and \<open>y\<close> is a non-enter predecessor of \<open>z\<close>, then
  \<open>(y, ctx)\<close> is reachable.  Iterating gives the callee-body backward chain inside \<open>act_reach\<close>.\<close>
lemma act_reach_intra_step:
  assumes r: "act_reach g cmb sg q (z, ctx)"
    and mem: "(y, z) \<in> intra_pred_rel g"
  shows "act_reach g cmb sg q (y, ctx)"
proof -
  from mem obtain a where "(y, a) \<in> set (non_enter_predecessor_list g z)"
    unfolding intra_pred_rel_def by auto
  thus ?thesis by (rule act_reach.intra[OF r])
qed

lemma act_reach_intra_rtrancl:
  assumes r: "act_reach g cmb sg q (z, ctx)"
    and reach: "(y, z) \<in> (intra_pred_rel g)\<^sup>*"
  shows "act_reach g cmb sg q (y, ctx)"
  using reach r
  by (induction rule: converse_rtrancl_induct) (auto intro: act_reach_intra_step)

text \<open>\<^bold>\<open>Task 2 --- the enter rule, direct.\<close>  From a reached return node \<open>(v, ctx)\<close>, a
  \<open>combine\<close> step reaches the routed callee \<^emph>\<open>exit\<close> \<open>(ex, cex)\<close>, and the callee body's
  backward \<open>intra\<close> chain reaches the callee \<^emph>\<open>entry\<close> \<open>(fe, cex)\<close> --- the exact composition
  the enter rule needs (caller continuation \<open>\<Longrightarrow>\<close> routed callee exit \<open>\<Longrightarrow>\<close> callee entry),
  now a single \<open>act_reach\<close> derivation rather than an external chaining of bridge lemmas.\<close>
lemma act_reach_enter:
  assumes r: "act_reach g cmb sg q (v, ctx)"
    and mem: "(cc, ex, dst) \<in> set (combine_predecessor_list g v)"
    and dep: "Inl (ex, cex) \<in> dep_aux sg (cmb ctx dst cc ex)"
    and body: "(fe, ex) \<in> (intra_pred_rel g)\<^sup>*"
  shows "act_reach g cmb sg q (fe, cex)"
proof -
  have "act_reach g cmb sg q (ex, cex)" by (rule act_reach.combine[OF r mem dep])
  thus ?thesis by (rule act_reach_intra_rtrancl[OF _ body])
qed

subsection \<open>Task 4: cov_edge and cov_frame derived from a solved query\<close>

text \<open>The two run-level \<open>vars\<close> obligations of the packaged activation theorem, \<^emph>\<open>derived\<close>
  from \<open>(query) \<in> vars\<close> and dependency closure rather than assumed.  \<open>cov_edge\<close> is the
  single \<open>intra\<close> dependency step (a solved node's non-enter predecessor is solved);
  \<open>cov_frame\<close> is the \<open>combine\<close>-then-body composition (a solved return node's routed callee
  exit, backward through the body, reaches the solved callee frame entry).\<close>

lemma cov_edge_from_query:
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
  shows "(u, ctx) \<in> vars"
  by (rule intra_pred_in_vars[OF pp cov mem])

lemma cov_frame_from_query:
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and mem: "(cc, ex, dst) \<in> set (combine_predecessor_list g v)"
    and dep: "Inl (ex, cex) \<in> dep_aux sg (cmb ctx dst cc ex)"
    and reach: "(fe, ex) \<in> (intra_pred_rel g)\<^sup>*"
  shows "(fe, cex) \<in> vars"
  by (rule combine_reaches_frame_in_vars[OF pp cov mem dep reach])

subsection \<open>Edge/combine forms of the vars dischargers (reusable per run)\<close>

text \<open>The \<open>q_edge\<close> / combine obligations of \<open>twfr_sound_seeded\<close> phrased directly over
  \<^const>\<open>edges\<close> / \<^const>\<open>combines\<close> membership (not the predecessor lists), so a run supplies
  only \<open>finite\<close> + the query membership.  \<open>q_edge_from_pp\<close>: a solved node's non-enter CFG
  predecessor is solved; \<open>combine_edge_dep_in_vars\<close>: any unknown the combine tree of a
  solved return node reads is solved.\<close>

lemma q_edge_from_pp:
  assumes fin: "finite (edges g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and e: "(u, a, v) \<in> edges g" and ne: "\<not> is_enter_action a"
    and cov: "(v, kc) \<in> vars"
  shows "(u, kc) \<in> vars"
proof -
  have "(u, a) \<in> predecessors g v" using e unfolding predecessors_def by blast
  hence "(u, a) \<in> set (predecessor_list g v)" using fin by simp
  hence "(u, a) \<in> set (non_enter_predecessor_list g v)"
    using ne by (rule non_enter_predecessor_list_mem)
  thus ?thesis by (rule intra_pred_in_vars[OF pp cov])
qed

lemma combine_edge_dep_in_vars:
  assumes fin: "finite (combines g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and c: "(cc, ex, v, dst) \<in> combines g"
    and dep: "Inl w \<in> dep_aux sg (cmb ctx dst cc ex)"
  shows "w \<in> vars"
proof -
  have "(cc, ex, dst) \<in> combine_predecessors g v" using c unfolding combine_predecessors_eq by blast
  hence "(cc, ex, dst) \<in> set (combine_predecessor_list g v)" using fin by simp
  thus ?thesis by (rule combine_dep_in_vars[OF pp cov _ dep])
qed

subsection \<open>Seeded-witness obstruction at recursive returns\<close>

text \<open>Every activation trace is non-empty and its \<^emph>\<open>head\<close> is an initial store: the
  \<open>entry\<close> / \<open>proc_entry\<close> base rules set it into \<open>S \<union> enter_state ` S\<close>, and \<open>intra\<close> /
  \<open>enter\<close> / \<open>combine\<close> all extend on the right, preserving the head.  This is the
  machine-checked obstruction to reusing a recursive callee suffix as an independently
  seeded \<open>trace_witness_act\<close> derivation.\<close>

lemma trace_witness_act_nonempty:
  "trace_witness_act enterc combc seedc g S v ctx tr \<Longrightarrow> tr \<noteq> []"
  by (induction rule: trace_witness_act.induct) auto

lemma trace_witness_act_hd_initial:
  assumes "trace_witness_act enterc combc seedc g S v ctx tr"
  shows "hd tr \<in> S \<union> (\<Union>xs es. edge_collect (EA_Enter xs es) S)"
  using assms
proof (induction rule: trace_witness_act.induct)
  case (entry v s) thus ?case by simp
next
  case (proc_entry xs es v s) thus ?case by auto
next
  case (intra u a v c tr s')
  have "tr \<noteq> []" using intra.hyps(3) by (rule trace_witness_act_nonempty)
  thus ?case using intra.IH by simp
next
  case (enter u xs es v c tau s')
  have "tau \<noteq> []" using enter.hyps(2) by (rule trace_witness_act_nonempty)
  thus ?case using enter.IH by simp
next
  case (combine cl ex v dst c1 tau c2 rho r)
  have "tau \<noteq> []" using combine.hyps(2) by (rule trace_witness_act_nonempty)
  thus ?case using combine.IH(1) by simp
qed

text \<open>
  \<^emph>\<open>The consequence.\<close>  The combine rule's callee sub-trace \<open>rho\<close> must satisfy
  \<open>hd rho = enter_state (last tau)\<close>.  By \<open>trace_witness_act_hd_initial\<close>,
  \<open>hd rho \<in> S \<union> enter_state ` S\<close>, so an independently seeded callee witness can be
  constructed only when the caller-derived entry store is itself an initial entry store.
  Recursive calls normally provide a callee suffix headed by \<open>enter_state (last tau)\<close>
  inside the larger execution, not a fresh derivation from \<open>S\<close>.

  \<^emph>\<open>The repair lives in the witness calculus.\<close>  \<open>Activation_Witness_From.thy\<close> introduces
  \<open>twf\<close>, whose start rule seeds a witness at any reachable node/store pair.
  The lemma \<open>twf_combine_reuses_callee_suffix\<close> consumes exactly the suffix shape that
  recursive returns provide: a frame-entry witness headed by the caller-derived
  entering store.  The concrete trace semantics, the activation trace refinement, and
  the collecting semantics stay unchanged; \<open>twf\<close> is an auxiliary proof relation for
  suffix reuse.
\<close>

end
