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

locale sound_dg_spec_ltr_for = sound_dg_spec S gammaDG gs
  for S :: "(pp \<times> unit, unit, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
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
  "ltr_enter_tree u ca p =
     transfer_tree (dgs_enter S (call_info_of ca (entry_proc p))) (Inl (u, ())) (\<lambda>_. ())"

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
    using enter_sound[where ci = "call_info_of (CallEdge dst fs args) callee"] by simp
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
    using combine_sound[where ci = "call_info_of (CallEdge dst fs args) callee"] by simp
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

