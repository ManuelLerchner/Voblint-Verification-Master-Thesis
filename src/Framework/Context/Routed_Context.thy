theory Routed_Context
  imports DG_Ctx_Activation DG_Local_State_Spec "Voblint_Solver.Strategy_Tree_Program"
    "Voblint_CFG.LTR_Def" Activation_Backbone
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

subsection \<open>The routed key space\<close>

datatype ('v,'c) routed_gk =
  Analysis_Global 'v
| Activation_Seed (seed_pp: pp) (seed_ctx: 'c)

text \<open>
  What the solver's global unknowns are, once an analysis is routed. Two kinds,
  and they belong to different owners. \<^const>\<open>Analysis_Global\<close> wraps a name of
  the analysis's own type \<open>'v\<close> --- Goblint's \<open>V\<close> --- and is the only kind an
  analysis can reach, through \<^const>\<open>man_global\<close>/\<^const>\<open>man_sideg\<close>.
  \<^const>\<open>Activation_Seed\<close> holds the entry state published at a callee's
  activation, keyed by the callee entry point and the routed context.

  The two names record who owns which. \<open>Analysis_Global\<close> embeds this
  development's analogue of Goblint's \<open>Spec.V\<close> into the solver's global-key
  space --- the namespace itself is \<open>'v\<close>, and this constructor is the address
  around it. Goblint's own Base analysis supplies a non-trivial one
  (privatization globals, thread-return globals) rather than a single global
  cell. \<open>Activation_Seed\<close> is not Goblint's --- their
  framework records reachable contexts on a separate global whose value is a
  set of contexts, keyed by function. It is this development's device for
  activating a local unknown through the vendored side-effecting solver, and is
  named to say so, so that no later reader takes it for a Goblint correspondence.

  The types keep the two apart. A transfer names a global as a \<open>'v\<close> and never
  builds a key, because \<^const>\<open>mk_dg_man\<close> holds the embedding; only the routing
  and generator layers apply \<^const>\<open>Activation_Seed\<close>. Every routed context
  instantiates \<open>'c\<close> (call strings at \<^typ>\<open>cfg_node list\<close>, entry states at a
  value list, context-insensitive at \<^typ>\<open>unit\<close> --- which is exactly Goblint's
  own \<open>C = Printable.Unit\<close>), and an analysis with one global takes \<open>'v = unit\<close>.
\<close>

lemma activation_seed_ne_analysis_global [simp]:
  "Activation_Seed u c \<noteq> Analysis_Global v"
  "Analysis_Global v \<noteq> Activation_Seed u c"
  by simp_all

text \<open>Which routed keys are seeds. A seed is the join of the entry states its callers
  publish and is never widened; the solver bridge's key-selected update rule
  \<open>update_global_keyed\<close> takes this predicate so the analysis global keeps
  the widening policy the analysis configured while every seed is joined.\<close>
fun is_activation_seed :: "('v, 'c) routed_gk \<Rightarrow> bool" where
  "is_activation_seed (Activation_Seed _ _) = True"
| "is_activation_seed (Analysis_Global _) = False"

subsection \<open>The canonical routed entry-seed publication and return combine\<close>

text \<open>
  The routing combine reads the caller under its own context, the callee exit under the
  context \<open>route\<close> selects from the caller's local value and the exact matched
  \<^typ>\<open>call_action\<close> (from \<^const>\<open>return_call_action_list\<close>, never re-derived from
  the call site's outgoing edges). The spec's own enter and combine transfers run as
  compiled manager programs over the caller value, so whether the global slot \<open>gk0\<close>
  is read or published at all is the specification's business: a Base-style spec's
  transfers touch no global and the routed tree then carries no \<open>gk0\<close> effect either,
  while an effectful spec's own \<open>man_global\<close>/\<open>man_sideg\<close> calls ride inside the
  compiled subtrees.

  Parameter order matches \<^locale>\<open>dg_ctx_activation_base\<close>'s \<open>cmb\<close> calling
  convention: the generator supplies \<open>route\<close> as \<open>cmb\<close>'s own first argument
  (\<open>cmb route c ca cc ex\<close> in \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>), so
  \<open>routed_cmb_g S gk0 seed_key\<close>, closing over the spec, the shared slot, and the
  seed-key injection, is the value that instantiates \<open>cmb\<close>.

  This tree owns the whole call lifecycle for one call action: it reads the caller once,
  routes the callee context once (\<open>ctx'\<close>), and shares that one \<open>ctx'\<close> between the
  entry-seed publication and the combine's callee-exit read. The callee is therefore
  activated as a side effect of whichever equation combines its result, discharging
  \<open>enter#\<close> exactly once per call action rather than once per hook. The caller
  continuation is not reconstructed here: \<^const>\<open>dg_spec_combine_transfer\<close>'s own
  pipeline runs \<open>caller_cont\<close>, \<open>combine_env\<close>, and \<open>combine_assign\<close> in sequence,
  so this layer only chooses addresses and keys. Only the half that
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
\<close>

text \<open>
  One resolved callee: enter the frame through the spec's compiled enter transfer,
  key the entered state, publish it at the routed seed, read that activation's exit
  back and run the spec's composed combine. The caller's local state is passed in
  rather than read here, because the call site reads it once and every target it
  resolves to is entered from that same value.
\<close>

text \<open>
  What one call alternative contributes. The continuation and the callee-entry
  value arrive together, from a single run of the specification's entry, and
  this is where they are used together: the entry half chooses the context and
  is published at that context's seed, and the continuation half is the local
  value the return combine runs against. Neither is recoverable from the other,
  which is why the pair travels this far intact.

  Naming it separately is what lets the bounds below speak about \<^emph>\<open>one\<close>
  alternative: the tree the generator builds is a fold over these, so every
  obligation about a selected alternative is a statement about one element of
  that fold rather than about the fold itself.
\<close>

definition routed_cmb_g_alt ::
  "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ('D \<Rightarrow> bool)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pname \<Rightarrow> 'D enter_result
   \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p alt =
     (case alt of (cont, entry) \<Rightarrow>
        (if is_bot entry
         then sp_compile_with (\<lambda>d. DG d bot)
                (dg_spec_combine_transfer S (call_info_of ca p)
                  (mk_dg_man cont (\<lambda>_. gk0)) bot)
         else
           (let ctx' = route cc ctx entry ca
            in Side (seed_key (FunctionEntry p) ctx') (DG entry bot)
                 (QueryL (FunctionResult p, ctx')
                    (\<lambda>callee_state.
                       sp_compile_with (\<lambda>d. DG d bot)
                         (dg_spec_combine_transfer S (call_info_of ca p)
                           (mk_dg_man cont (\<lambda>_. gk0))
                           (locals callee_state)))))))"

text \<open>
  Deliberately not a \<open>simp\<close> rule: it expands into a \<^const>\<open>Side\<close> over a
  \<^const>\<open>QueryL\<close> over a compiled combine, and letting that fire everywhere
  would put a whole call boundary into every goal mentioning the constant.
  The observation lemmas below cite it where they need it.
\<close>

lemma routed_cmb_g_alt_bot [simp]:
  assumes "is_bot entry"
  shows "routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p (cont, entry)
           = sp_compile_with (\<lambda>d. DG d bot)
               (dg_spec_combine_transfer S (call_info_of ca p)
                 (mk_dg_man cont (\<lambda>_. gk0)) bot)"
  using assms by (simp add: routed_cmb_g_alt_def)

lemma routed_cmb_g_alt_nonbot [simp]:
  assumes "\<not> is_bot entry"
  shows "routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p (cont, entry)
     = Side (seed_key (FunctionEntry p) (route cc ctx entry ca)) (DG entry bot)
         (QueryL (FunctionResult p, route cc ctx entry ca)
            (\<lambda>callee_state.
               sp_compile_with (\<lambda>d. DG d bot)
                 (dg_spec_combine_transfer S (call_info_of ca p)
                   (mk_dg_man cont (\<lambda>_. gk0))
                   (locals callee_state))))"
  unfolding routed_cmb_g_alt_def using assms by (simp add: Let_def)

definition routed_cmb_g_at ::
  "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ('D \<Rightarrow> bool)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> 'D \<Rightarrow> pname
   \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p =
     enter\<^sup># S (call_info_of ca p) (mk_dg_man caller (\<lambda>_. gk0))
       (\<lambda>pairs.
          sp_compile (side_rhs_fold_dg bot
            (map (routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p) pairs)))"

text \<open>
  The call site's own contribution: read the caller state, ask
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
  "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'D \<Rightarrow> pname list)
   \<Rightarrow> ('D \<Rightarrow> bool)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_cmb_g S gk0 seed_key resolve is_bot route ctx ca cc v =
     sp_lift_tree (QueryL (cc, ctx) Answer)
       (\<lambda>caller_state.
          sp_compile (side_rhs_fold_dg bot
            (map (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc
                    (locals caller_state))
                 (resolve v cc ca (locals caller_state)))))"


text \<open>The seed read-back hook: at a callee entry it reads the seed out of the
  \<open>locals\<close> half, matching \<open>routed_cmb_g\<close>'s write.\<close>
definition routed_extra_g ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D::bounded_semilattice_sup_bot \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G::bounded_semilattice_sup_bot) dg_state) strategy_tree list"
where
  "routed_extra_g seed_key gk0 route ctx v =
     (case v of FunctionEntry _ \<Rightarrow>
        [sp_lift_tree (QueryG (seed_key v ctx) Answer) (\<lambda>seed_state. Answer (DG (locals seed_state) bot))]
       | _ \<Rightarrow> [])"

lemma routed_extra_g_free:
  "x \<in> set (routed_extra_g seed_key gk0 route ctx v) \<Longrightarrow> sides_of_rhs x tau z = bot"
  unfolding routed_extra_g_def by (cases v) (auto simp: bot_fun_def)

lemma routed_extra_g_local_only:
  "x \<in> set (routed_extra_g seed_key gk0 route ctx v) \<Longrightarrow> globs (traverse_rhs x tau) = bot"
  unfolding routed_extra_g_def by (cases v) auto

text \<open>
  How a routed per-target tree relates to its parts under a solution. Each bound
  is stated for \<^emph>\<open>one\<close> alternative of the list a single run of the entry
  produced, because the tree is a fold over exactly those. These are the only
  facts CALL and COMB below need about the tree's body.
\<close>


lemma routed_cmb_g_at_sides_ge_seed:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    and mem: "(cont, entry) \<in> set pairs"
    and nb: "\<not> is_bot entry"
  shows "DG entry bot
           \<le> sides_of_rhs (routed_cmb_g_at S gk0 seed_key route is_bot ctx
                (CallEdge dst pars args) cc caller p) \<sigma>
                (Inr (seed_key (FunctionEntry p)
                   (route cc ctx entry (CallEdge dst pars args))))"
proof -
  let ?F = "routed_cmb_g_alt S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc p"
  let ?k = "Inr (seed_key (FunctionEntry p) (route cc ctx entry (CallEdge dst pars args)))"
  have "DG entry bot \<le> sides_of_rhs (?F (cont, entry)) \<sigma> ?k"
    unfolding routed_cmb_g_alt_def using nb by (simp add: Let_def)
  also have "\<dots> \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg bot (map ?F pairs))) \<sigma> ?k"
    by (rule sides_le_side_rhs_fold_dg) (use mem in force)
  also have "\<dots> \<le> sides_of_rhs (routed_cmb_g_at S gk0 seed_key route is_bot ctx
                     (CallEdge dst pars args) cc caller p) \<sigma> ?k"
    unfolding routed_cmb_g_at_def
    by (simp add: enter_runsD_sides[OF R] sup_fun_def)
  finally show ?thesis .
qed

text \<open>
  The entry program's own publications survive into the call's, whatever the
  alternatives turn out to be --- this is the half a specification with an
  effectful entry needs, and it holds without selecting an alternative at all.
\<close>

lemma routed_cmb_g_at_sides_ge_prefix:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
  shows "pub \<le> sides_of_rhs
                 (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma>"
  unfolding routed_cmb_g_at_def
  by (simp add: enter_runsD_sides[OF R])

text \<open>
  One rung further out: one resolved target's contribution survives the fold
  over the site's targets. Stated without a locale so a proof that must place a
  publication inside the solution --- one whose concretization reads the global
  channel --- can walk outwards from a call site it has not yet routed.
\<close>

lemma routed_cmb_g_sides_ge_at:
  assumes mem: "p \<in> set (resolve v cc ca (locals (\<sigma> (Inl (cc, ctx)))))"
  shows "sides_of_rhs (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc
             (locals (\<sigma> (Inl (cc, ctx)))) p) \<sigma> z
           \<le> sides_of_rhs (routed_cmb_g S gk0 seed_key resolve is_bot route ctx ca cc v) \<sigma> z"
proof -
  have "routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc (locals (\<sigma> (Inl (cc, ctx)))) p
          \<in> set (map (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc
                        (locals (\<sigma> (Inl (cc, ctx)))))
                  (resolve v cc ca (locals (\<sigma> (Inl (cc, ctx))))))"
    using mem by simp
  from sides_le_side_rhs_fold_dg[OF this, where acc = bot and k = z] show ?thesis
    by (simp add: routed_cmb_g_def)
qed

lemma routed_cmb_g_at_sides_ge_combine:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    and mem: "(cont, entry) \<in> set pairs"
  shows "sides_of_rhs
           (routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p (cont, entry)) \<sigma> z
           \<le> sides_of_rhs
                (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> z"
proof -
  let ?F = "routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p"
  have "sides_of_rhs (?F (cont, entry)) \<sigma> z
          \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg bot (map ?F pairs))) \<sigma> z"
    by (rule sides_le_side_rhs_fold_dg) (use mem in force)
  also have "\<dots> \<le> sides_of_rhs
                    (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> z"
    unfolding routed_cmb_g_at_def
    by (simp add: enter_runsD_sides[OF R] sup_fun_def)
  finally show ?thesis .
qed

text \<open>
  And the answer: the value a selected alternative's return combine produces is
  below what the call answers, because the call answers the join over every
  alternative. This is the bound COMB needs --- one alternative's combine is
  covered, not all of them jointly. It holds for a bottom alternative too, whose
  combine runs against \<^const>\<open>bot\<close>.
\<close>

lemma routed_cmb_g_at_traverse_ge:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    and mem: "(cont, entry) \<in> set pairs"
  shows "locals (traverse_rhs
             (routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p (cont, entry)) \<sigma>)
           \<le> locals (traverse_rhs
                (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma>)"
proof -
  let ?F = "routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p"
  have "locals (traverse_rhs (?F (cont, entry)) \<sigma>)
          \<le> side_acc_dg bot \<sigma> (map ?F pairs)"
    by (rule locals_traverse_le_side_acc_dg) (use mem in force)
  also have "\<dots> = locals (traverse_rhs
                     (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma>)"
    unfolding routed_cmb_g_at_def
    by (simp add: enter_runsD_traverse[OF R]
        traverse_side_rhs_fold_dg[unfolded sp_compile_def])
  finally show ?thesis .
qed


subsection \<open>When a routed combine publishes nothing at the analysis global\<close>

text \<open>
  Whether a tree needs reshaping before the buffered generator can consume it is a
  property of that tree, not of the analysis that produced it. The two facts below
  say when a routed combine needs none.

  \<^item> Its answer always carries \<open>bot\<close> on the globals half: the per-call-site fold
    accumulates only \<open>locals\<close>.
  \<^item> It publishes nothing at \<open>gk0\<close> as soon as the spec's own enter and combine
    sub-programs publish nothing there --- the only side the routed tree adds is
    the seed, and a seed key is never \<open>gk0\<close>.

  A tree with both properties is already its own contribution analogue, so the
  buffered generator's \<open>cmb_c\<close> hook can be the tree itself. A spec whose transfers
  do publish at \<open>gk0\<close> fails the second and must supply a reshaped hook instead.
\<close>

lemma sides_side_rhs_fold_dg_bot:
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> sides_of_rhs t \<sigma> z = bot"
  shows "sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) \<sigma> z = bot"
  using assms by (induction ts arbitrary: acc) (simp_all add: sp_compile_with_bind)

lemma routed_cmb_g_global_free:
  "globs (traverse_rhs (routed_cmb_g S gk0 seed_key resolve is_bot route ctx ca cc v) \<sigma>) = bot"
  by (simp add: routed_cmb_g_def traverse_side_rhs_fold_dg[unfolded sp_compile_def])

text \<open>
  The entry half of the condition is now stated through \<^const>\<open>enter_runs\<close>: an
  entry program publishes nothing at \<open>gk0\<close> exactly when the \<open>pub\<close> it runs to is
  \<^const>\<open>bot\<close> there. The compiled-tree phrasing this replaces could not be
  written any more --- an entry program answers a list, so it has no compiled
  tree of its own.
\<close>

lemma routed_cmb_g_at_side_free_at_gk0:
  assumes enter_free: "\<And>ci d pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub \<Longrightarrow> pub (Inr gk0) = bot"
    and enter_runs_ex: "\<And>ci d. \<exists>pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub"
    and comb_free: "\<And>ci d de z. sides_of_rhs (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer S ci (mk_dg_man d (\<lambda>_. gk0)) de)) \<sigma> z = bot"
    and ne: "\<And>p ctx'. seed_key (FunctionEntry p) ctx' \<noteq> gk0"
  shows "sides_of_rhs
           (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> (Inr gk0) = bot"
proof -
  obtain pairs pub
    where R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    using enter_runs_ex by blast
  have alts: "\<And>t. t \<in> set (map (routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p) pairs)
                 \<Longrightarrow> sides_of_rhs t \<sigma> (Inr gk0) = bot"
    by (auto simp: routed_cmb_g_alt_def Let_def comb_free ne[THEN not_sym]
        split: if_splits)
  have "sides_of_rhs
          (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> (Inr gk0)
        = pub (Inr gk0)
          \<squnion> sides_of_rhs (sp_compile (side_rhs_fold_dg bot
                (map (routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p) pairs)))
              \<sigma> (Inr gk0)"
    unfolding routed_cmb_g_at_def by (simp add: enter_runsD_sides[OF R] sup_fun_def)
  also have "\<dots> = bot"
  proof -
    have "sides_of_rhs (sp_compile (side_rhs_fold_dg bot
            (map (routed_cmb_g_alt S gk0 seed_key route is_bot ctx ca cc p) pairs)))
            \<sigma> (Inr gk0) = bot"
      by (rule sides_side_rhs_fold_dg_bot) (rule alts)
    then show ?thesis using enter_free[OF R] by simp
  qed
  finally show ?thesis .
qed

lemma routed_cmb_g_side_free_at_gk0:
  assumes enter_free: "\<And>ci d pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub \<Longrightarrow> pub (Inr gk0) = bot"
    and enter_runs_ex: "\<And>ci d. \<exists>pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub"
    and comb_free: "\<And>ci d de z. sides_of_rhs (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer S ci (mk_dg_man d (\<lambda>_. gk0)) de)) \<sigma> z = bot"
    and ne: "\<And>p ctx'. seed_key (FunctionEntry p) ctx' \<noteq> gk0"
  shows "sides_of_rhs (routed_cmb_g S gk0 seed_key resolve is_bot route ctx ca cc v)
           \<sigma> (Inr gk0) = bot"
proof -
  have at_free: "\<And>caller p.
      sides_of_rhs (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc caller p)
        \<sigma> (Inr gk0) = bot"
    by (rule routed_cmb_g_at_side_free_at_gk0)
       (rule enter_free enter_runs_ex comb_free ne, assumption?)+
  have "sides_of_rhs (sp_compile (side_rhs_fold_dg bot
          (map (routed_cmb_g_at S gk0 seed_key route is_bot ctx ca cc
                  (locals (\<sigma> (Inl (cc, ctx)))))
             (resolve v cc ca (locals (\<sigma> (Inl (cc, ctx)))))))) \<sigma> (Inr gk0) = bot"
    by (rule sides_side_rhs_fold_dg_bot) (auto simp: at_free)
  then show ?thesis by (simp add: routed_cmb_g_def)
qed

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
    "routed_cmb_g S gk0 seed_key resolve is_bot" "routed_extra_g seed_key gk0"
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
  shows "routed_cmb_g S gk0 seed_key resolve is_bot route ctx (CallEdge dst pars args) cc cont
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
  shows "routed_cmb_g_at S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
             (locals (sigma (Inl (cc, ctx)))) p
           \<in> set (map (routed_cmb_g_at S gk0 seed_key route is_bot ctx
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
           (routed_cmb_g_at S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma)
         \<le> side_acc_dg (acc0 cont) sigma (trees cont ctx)"
proof -
  have "locals (traverse_rhs
           (routed_cmb_g_at S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma)
      \<le> locals (traverse_rhs
           (routed_cmb_g S gk0 seed_key resolve is_bot route ctx
              (CallEdge dst pars args) cc cont)
           sigma)"
    using locals_traverse_le_side_acc_dg[OF resolved_target_mem[OF covV ce sin], where acc = bot]
    by (simp add: routed_cmb_g_def traverse_side_rhs_fold_dg[unfolded sp_compile_def])
  also have "\<dots> \<le> side_acc_dg (acc0 cont) sigma (trees cont ctx)"
    by (rule locals_traverse_le_side_acc_dg[OF resolved_site_mem[OF ce]])
  finally show ?thesis .
qed

lemma resolved_at_le_site_sides:
  assumes covV: "(cc, ctx) \<in> vars"
    and ce: "(cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (cc, ctx)))) (globs (sigma (Inr gk0)))"
  shows "sides_of_rhs
           (routed_cmb_g_at S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma z
         \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg (acc0 cont) (trees cont ctx))) sigma z"
proof -
  have "sides_of_rhs
           (routed_cmb_g_at S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc
              (locals (sigma (Inl (cc, ctx)))) p) sigma z
      \<le> sides_of_rhs
           (routed_cmb_g S gk0 seed_key resolve is_bot route ctx
              (CallEdge dst pars args) cc cont)
           sigma z"
    by (rule routed_cmb_g_sides_ge_at
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
  let ?t = "routed_cmb_g_at S gk0 seed_key route is_bot ctx (CallEdge dst pars args) u
              (locals (sigma (Inl (u, ctx)))) p"
  have seedb: "DG entry bot \<le> sides_of_rhs ?t sigma ?k"
    using R mem nb by (rule routed_cmb_g_at_sides_ge_seed)
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
  hence "gammaM (sg (Inl (u, ctx))) = {}" by (rule sg_uncovered_empty)
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
           (routed_cmb_g_alt S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma)
         \<le> locals (sigma (Inl (cont, c1)))"
proof -
  have "locals (traverse_rhs
           (routed_cmb_g_alt S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma)
      \<le> locals (traverse_rhs
           (routed_cmb_g_at S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl
              (locals (sigma (Inl (cl, c1)))) p) sigma)"
    by (rule routed_cmb_g_at_traverse_ge[OF R mem])
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
    and R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
              (mk_dg_man (locals (sigma (Inl (cl, c1)))) (\<lambda>_. gk0)) sigma pairs pub"
    and mem: "(cont', entry) \<in> set pairs"
  shows "globs (sides_of_rhs
           (routed_cmb_g_alt S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma (Inr gk0))
         \<le> globs (sigma (Inr gk0))"
proof -
  have "globs (sides_of_rhs
           (routed_cmb_g_alt S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
              (cont', entry)) sigma (Inr gk0))
      \<le> globs (sides_of_rhs
           (routed_cmb_g_at S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl
              (locals (sigma (Inl (cl, c1)))) p) sigma (Inr gk0))"
    by (rule le_dg_state_globsD[OF routed_cmb_g_at_sides_ge_combine[OF R mem]])
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
  hence "gammaM (sg (Inl (cl, c1))) = {}" by (rule sg_uncovered_empty)
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
  let ?alt = "routed_cmb_g_alt S gk0 seed_key route is_bot c1 (CallEdge dst pars args) cl p
                (cont', entry)"
  have nb: "\<not> is_bot entry" using ecov by (rule entry_cover_not_bot)
  have route_agree: "?ex_ctx = enterc cl c1 es" using req es_eq by simp
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
  \<^typ>\<open>vname \<Rightarrow> 'a\<close>, so this is just \<^const>\<open>map\<close>), and the routing functions
  below apply it to the state they are handed. That state is already the
  \<^emph>\<open>entered\<close> callee frame:
  \<^const>\<open>routed_cmb_g_at\<close> runs the specification's own enter transfer first and
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
