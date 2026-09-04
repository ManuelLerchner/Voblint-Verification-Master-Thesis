theory DG_LTR_Sound
  imports DG_Soundness "Voblint_CFG.LTR_Abstract"
begin

section \<open>Trace-native D/G collecting soundness\<close>

text \<open>
  The D/G post-solution endpoint is stated over the stack-faithful local-trace
  collector \<^const>\<open>ltr_collect\<close>. Its entry, edge, and combine closure
  obligations feed \<open>ltr_collect_semantic_postfix\<close>; matched returns are supplied
  by \<^const>\<open>valid_ltr\<close>.

  A semantic post-fixpoint is \<open>hook_postfix\<close>: it says the compiled trees'
  \<^emph>\<open>own observations\<close> -- the local value each tree answers with and the
  global contribution it publishes -- are bounded by the valuation at the
  target. Nothing here reconstructs a \<open>'G \<times> 'D\<close> pair from a transfer, so the
  argument is the same whether the specification touches the global channel
  or not.

  \<^locale>\<open>sound_dg_hooks\<close> takes those trees as parameters. A specification
  supplies them by compiling its own fields, which is what the sublocale below
  does: the trace-semantic endpoint is then \<^locale>\<open>sound_dg_spec\<close>'s three
  obligations and nothing further.
\<close>

text \<open>
  The entry tree this generator builds, as a standalone constant so the locale
  below can assume something about it. The caller unknown is read once, the
  specification's entry runs once against it, and the alternatives contribute
  their callee-entry halves; the continuation halves are dropped, because this
  generator's return equation reads the caller unknown itself rather than a
  value carried from the call. That is sound exactly when the two agree, which
  is what \<open>unrouted_enter_compatible\<close> records for a given specification.
\<close>

definition ltr_enter_tree_of ::
  "(pp \<times> unit, unit, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "ltr_enter_tree_of S u ca p =
     dg_read_at (Inl (u, ()))
       (\<lambda>d. dgs_enter S (call_info_of ca (entry_proc p)) (mk_dg_man d (\<lambda>_. ()))
              (\<lambda>pairs. sp_compile (side_rhs_fold_dg bot
                         (map (\<lambda>(_, entry). Answer (DG entry bot)) pairs))))"

text \<open>
  Every alternative resumes the caller exactly where the call left it. The
  monovariant generator needs this: it drops the continuation halves and its
  return equation reads the caller unknown instead, so a specification whose
  entry computed a different continuation would have that continuation silently
  replaced. Equality, not \<open>\<le>\<close>: the raw caller may well over-approximate a
  narrowed continuation, but using it would discard precision the call
  deliberately chose.
\<close>

definition unrouted_enter_compatible ::
  "(pp \<times> unit, unit, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> bool"
where
  "unrouted_enter_compatible S \<longleftrightarrow>
     (\<forall>ci. \<exists>f. dgs_enter S ci = local_enter_transfer f
               \<and> (\<forall>d cont entry. (cont, entry) \<in> set (f d) \<longrightarrow> cont = d))"

text \<open>
  Purity is part of the predicate rather than a separate assumption, and not by
  convenience: the alternatives of an effectful entry are unobservable from
  outside its program --- a \<^type>\<open>strategy_program\<close> answers into a tree whose
  \<^const>\<open>Answer\<close> carries the carrier, and a list of pairs does not embed there.
  So the only specifications whose continuations can be compared to the caller
  at all are those that compute them as a function of it.
\<close>

lemma unrouted_enter_compatibleI [intro]:
  assumes "\<And>ci. dgs_enter S ci = local_enter_transfer (f ci)"
    and "\<And>ci d cont entry. (cont, entry) \<in> set (f ci d) \<Longrightarrow> cont = d"
  shows "unrouted_enter_compatible S"
  using assms unfolding unrouted_enter_compatible_def by blast

text \<open>
  The alternatives reach the fold as bare answers, so the tree adds no
  publication of its own: whatever it contributes at a global slot, the entry
  program contributed already.
\<close>

lemma sides_side_rhs_fold_dg_entry_answers [simp]:
  "sides_of_rhs (sp_compile (side_rhs_fold_dg acc
       (map (\<lambda>(_, entry). Answer (DG entry bot)) pairs))) sigma = bot"
  by (induction pairs arbitrary: acc)
     (simp_all add: sp_compile_with_bind split_beta bot_fun_def)

text \<open>
  The locale's assumption, reduced to what a caller can produce: one run of the
  specification's entry against the solution, and one alternative of that run
  covering the concrete call. The tree joins the callee-entry halves of every
  alternative, so a covering one is below the join, and the global side the
  cover is taken against need only be below what the run published.
\<close>

lemma enter_sound_ltr_of_enter_runs:
  fixes S :: "(pp \<times> unit, unit, unit, 'D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and sigma :: "pp \<times> unit + unit \<Rightarrow> ('D, 'G) dg_state"
  assumes mono: "\<And>d d' g g'. \<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow> gammaDG d g \<subseteq> gammaDG d' g'"
    and runs: "enter_runs (dgs_enter S (call_info_of (CallEdge dst fs args) callee))
                 (mk_dg_man (locals (sigma (Inl (u, ())))) (\<lambda>_. ())) sigma pairs pub"
    and cov: "entry_pairs_cover (\<lambda>e. gammaDG e g) s
                (call_enter gs (CallEdge dst fs args) s) pairs"
    and gle: "g \<le> globs (pub (Inr ()))"
  shows "call_enter gs (CallEdge dst fs args) s
           \<in> gammaDG (locals (traverse_rhs (ltr_enter_tree_of S u (CallEdge dst fs args)
                                  (FunctionEntry callee)) sigma))
                     (globs (sides_of_rhs (ltr_enter_tree_of S u (CallEdge dst fs args)
                                  (FunctionEntry callee)) sigma (Inr ())))"
proof -
  let ?K = "\<lambda>ps. sp_compile (side_rhs_fold_dg bot
                    (map (\<lambda>(_, entry). Answer (DG entry bot)) ps))"
  let ?m = "mk_dg_man (locals (sigma (Inl (u, ())))) (\<lambda>_ :: unit. ())"
  let ?T = "dgs_enter S (call_info_of (CallEdge dst fs args) callee)"
  have tr: "traverse_rhs (ltr_enter_tree_of S u (CallEdge dst fs args) (FunctionEntry callee)) sigma
              = traverse_rhs (?T ?m ?K) sigma"
    and sd: "sides_of_rhs (ltr_enter_tree_of S u (CallEdge dst fs args) (FunctionEntry callee)) sigma
              = sides_of_rhs (?T ?m ?K) sigma"
    by (simp_all add: ltr_enter_tree_of_def dg_read_at_def sp_bind_def sp_read_local_def
        sp_return_def)
  obtain cont entry where mem: "(cont, entry) \<in> set pairs"
    and ein: "call_enter gs (CallEdge dst fs args) s \<in> gammaDG entry g"
    using cov by (rule entry_pairs_coverE)
  have le_d: "entry \<le> locals (traverse_rhs (?T ?m ?K) sigma)"
  proof -
    have "Answer (DG entry bot) \<in> set (map (\<lambda>(_, entry). Answer (DG entry bot)) pairs)"
      using mem by force
    then have "locals (traverse_rhs (Answer (DG entry bot)) sigma)
                 \<le> side_acc_dg bot sigma (map (\<lambda>(_, entry). Answer (DG entry bot)) pairs)"
      by (rule locals_traverse_le_side_acc_dg)
    then show ?thesis
      by (simp add: enter_runsD_traverse[OF runs]
          traverse_side_rhs_fold_dg[unfolded sp_compile_def])
  qed
  have le_g: "g \<le> globs (sides_of_rhs (?T ?m ?K) sigma (Inr ()))"
    using gle
    by (simp add: enter_runsD_sides[OF runs] sup_fun_def bot_fun_def
        sides_side_rhs_fold_dg_entry_answers[unfolded sp_compile_def]
        less_eq_dg_state_def)
  show ?thesis
    unfolding tr sd using ein mono[OF le_d le_g] by blast
qed

locale sound_dg_spec_ltr_for = sound_dg_spec S gammaDG gs
  for S :: "(pp \<times> unit, unit, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool" +
  assumes enter_sound_ltr:
    "s \<in> gammaDG (locals (sigma (Inl (u, ())))) (globs (sigma (Inr ()))) \<Longrightarrow>
       call_enter gs (CallEdge dst fs args) s
         \<in> gammaDG
             (locals (traverse_rhs
                (ltr_enter_tree_of S u (CallEdge dst fs args) (FunctionEntry callee)) sigma))
             (globs (sides_of_rhs
                (ltr_enter_tree_of S u (CallEdge dst fs args) (FunctionEntry callee))
                sigma (Inr ())))"
begin

text \<open>The specification's own compiled trees, addressed at the monovariant
  unknown \<open>(v, ())\<close> and the single global key \<open>()\<close>.\<close>

definition ltr_edge_tree ::
  "pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "ltr_edge_tree u a v = dg_spec_edge_tree S a (Inl (u, ())) (\<lambda>_. ())"

definition ltr_enter_tree ::
  "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "ltr_enter_tree u ca p = ltr_enter_tree_of S u ca p"

definition ltr_combine_tree ::
  "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "ltr_combine_tree u ca ex k =
     dg_spec_combine_tree S (call_info_of ca (result_proc ex))
       (Inl (u, ())) (Inl (ex, ())) (\<lambda>_. ())"
sublocale hooks: sound_dg_hooks gammaDG gs ltr_edge_tree ltr_combine_tree ltr_enter_tree
proof unfold_locales
  show "\<And>d d' g g'. \<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow> gammaDG d g \<subseteq> gammaDG d' g'"
    by (rule gammaDG_mono)
next
  fix sigma :: "pp \<times> unit + unit \<Rightarrow> ('D, 'G) dg_state" and source action destination
  show "edge_collect action (dg_hook_gamma gammaDG sigma source)
          \<subseteq> gammaDG
              (locals (traverse_rhs (ltr_edge_tree source action destination) sigma))
              (globs (sides_of_rhs (ltr_edge_tree source action destination)
                        sigma (Inr ())))"
    unfolding ltr_edge_tree_def dg_hook_gamma_def dg_hook_D_def dg_hook_G_def
    by (rule step_sound)
next
  fix sigma :: "pp \<times> unit + unit \<Rightarrow> ('D, 'G) dg_state"
    and caller dst fs args callee s
  assume "s \<in> dg_hook_gamma gammaDG sigma caller"
  then show "call_enter gs (CallEdge dst fs args) s
          \<in> gammaDG
              (locals (traverse_rhs
                 (ltr_enter_tree caller (CallEdge dst fs args)
                    (FunctionEntry callee)) sigma))
              (globs (sides_of_rhs
                 (ltr_enter_tree caller (CallEdge dst fs args)
                    (FunctionEntry callee)) sigma (Inr ())))"
    unfolding ltr_enter_tree_def dg_hook_gamma_def dg_hook_D_def dg_hook_G_def
    by (rule enter_sound_ltr)
next
  fix sigma :: "pp \<times> unit + unit \<Rightarrow> ('D, 'G) dg_state"
    and caller dst fs args callee continuation s t
  assume "s \<in> dg_hook_gamma gammaDG sigma caller"
    and "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult callee)"
  then show "combine_collect gs dst s t
          \<in> gammaDG
              (locals (traverse_rhs
                 (ltr_combine_tree caller (CallEdge dst fs args)
                    (FunctionResult callee) continuation) sigma))
              (globs (sides_of_rhs
                 (ltr_combine_tree caller (CallEdge dst fs args)
                    (FunctionResult callee) continuation) sigma (Inr ())))"
    unfolding ltr_combine_tree_def dg_hook_gamma_def dg_hook_D_def dg_hook_G_def
    using combine_sound_tree[where ci = "call_info_of (CallEdge dst fs args) callee"] by simp
qed

text \<open>The seed bound at the entry, in concretization terms: both projections of
  the seed are dominated, so the seed's concretization is.\<close>

lemma hook_postfix_gamma_entry:
  assumes pf: "hooks.hook_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "S0 \<subseteq> dg_hook_gamma gammaDG sigma (cfg_entry g)"
  unfolding dg_hook_gamma_def
  using sound0 gammaDG_mono[OF hooks.hook_postfix_entryD[OF pf]
                               hooks.hook_postfix_entryG[OF pf]]
  by blast

theorem dg_postfix_collect_sound_ltr_for:
  assumes pf: "hooks.hook_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_hook_gamma gammaDG sigma v"
proof (rule ltr_collect_semantic_postfix)
  show "S0 \<subseteq> dg_hook_gamma gammaDG sigma (cfg_entry g)"
    by (rule hook_postfix_gamma_entry[OF pf sound0])
next
  fix u a w s s'
  assume e: "(u, a, w) \<in> intra g" and su: "s \<in> dg_hook_gamma gammaDG sigma u"
    and st: "s' \<in> edge_step a s"
  have "s' \<in> edge_collect a (dg_hook_gamma gammaDG sigma u)"
    using su st by (auto simp: edge_collect_def)
  then show "s' \<in> dg_hook_gamma gammaDG sigma w"
    using hooks.hook_postfix_edge[OF pf e] by blast
next
  fix u dst pars args p cont s
  assume "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> dg_hook_gamma gammaDG sigma u"
  then show "call_enter gs (CallEdge dst pars args) s
               \<in> dg_hook_gamma gammaDG sigma (FunctionEntry p)"
    by (rule hooks.hook_postfix_enter[OF pf])
next
  fix cl dst pars args p cont s t
  assume "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> dg_hook_gamma gammaDG sigma cl"
    and "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)"
  then show "combine_collect gs dst s t \<in> dg_hook_gamma gammaDG sigma cont"
    by (rule hooks.hook_postfix_combine[OF pf])
qed

corollary dg_post_solution_collect_sound_ltr_for:
  assumes pp: "part_post_solution (hooks.hook_gen g bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover g vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_hook_gamma gammaDG sigma v"
proof -
  have pf: "hooks.hook_postfix g s0d s0g sigma"
    using cover[unfolded vars_cover_def]
    by (intro hooks.hook_post_solution_postfix[OF pp _ _ _ _ finI finC]) blast+
  show ?thesis by (rule dg_postfix_collect_sound_ltr_for[OF pf sound0])
qed

end

end

