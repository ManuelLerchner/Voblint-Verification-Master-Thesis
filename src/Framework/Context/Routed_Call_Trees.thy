theory Routed_Call_Trees
  imports DG_Spec_Sound DG_Keyed_Generator State_Restriction
    "Voblint_Domain.Nonrelational_State" "Voblint_Solver.Strategy_Tree_Post_Solution"
    "Voblint_Solver.Strategy_Tree_Program"
begin

section \<open>The equations one call action generates\<close>

text \<open>
  What a routed call is, as solver input, before anything is claimed about its
  soundness. Each callee a call action resolves to becomes one strategy tree:
  it runs the specification's entry transfer on the caller's local value,
  chooses the callee's context from the entry half of the alternative that
  produced, publishes that entered state at a global proxy key --- an
  \<^emph>\<open>activation seed\<close>, which is what makes the callee's own unknown
  reachable at all --- reads the callee's exit back at that same context, and
  runs the specification's combine against the alternative's continuation half.
  The other half of the protocol is the callee's own entry equation reading its
  seed slot back: that is \<open>routed_entry_seed_tree\<close>.

  This theory is construction and observation only: which unknowns a tree
  reads, which keys it publishes to, and lower bounds on what it contributes
  at each. Whether those contributions are sound is \<open>Routed_Context\<close>'s
  question, which fixes the shape built here as \<open>cmb\<close> and \<open>extra\<close> and
  discharges CALL and COMB against it once.
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
  set of contexts, keyed by function. It is a solver adapter, not the
  translation of any Goblint constraint constructor: the vendored solver
  publishes to global keys only, so the one way to activate a callee's local
  unknown is to publish at a global proxy the callee reads back. It is named to
  say so, so that no later reader takes it for a Goblint correspondence.

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
  context \<open>route\<close> selects from the callee's entered value --- the alternative's own
  second component, after \<open>enter\<^sup>#\<close> has run --- and the exact matched
  \<^typ>\<open>call_action\<close> (from \<^const>\<open>return_call_action_list\<close>, never re-derived from
  the call site's outgoing edges). The spec's own enter and combine transfers run as
  compiled manager programs over the caller value, so whether the global slot \<open>gk0\<close>
  is read or published at all is the specification's business: a Base-style spec's
  transfers touch no global and the routed tree then carries no \<open>gk0\<close> effect either,
  while an effectful spec's own \<open>man_global\<close>/\<open>man_sideg\<close> calls ride inside the
  compiled subtrees.

  Parameter order matches \<open>dg_ctx_activation_base\<close>'s \<open>cmb\<close> calling
  convention: the generator supplies \<open>route\<close> as \<open>cmb\<close>'s own first argument
  (\<open>cmb route c ca cc ex\<close> in \<^const>\<open>routed_node_rhs\<close>), so
  \<open>routed_call_tree S gk0 seed_key\<close>, closing over the spec, the shared slot, and the
  seed-key injection, is the value that instantiates \<open>cmb\<close>.

  This tree owns the whole call lifecycle for one call action: it reads the caller once,
  routes the callee context once (\<open>ctx'\<close>), and shares that one \<open>ctx'\<close> between the
  entry-seed publication and the combine's callee-exit read. The callee is therefore
  activated as a side effect of whichever equation combines its result, discharging
  \<open>enter#\<close> exactly once per call action rather than once per hook. The caller
  continuation is not reconstructed here: it is handed to
  \<^const>\<open>dg_spec_combine_transfer\<close> as the manager's own local value, and that
  pipeline runs \<open>combine_env\<^sup>#\<close> and \<open>combine_assign\<^sup>#\<close> over it,
  so this layer only chooses addresses and keys. Only the half that
  cannot move stays with \<open>routed_entry_seed_tree\<close>: a callee's own entry equation is the one
  place that can read its own seed slot back. \<open>route\<close> is kept as a parameter of that
  hook purely to match \<open>dg_ctx_activation_base\<close>'s \<open>extra\<close> calling
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

definition routed_call_alternative_tree ::
  "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ('D \<Rightarrow> bool)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pname \<Rightarrow> 'D enter_result
   \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p alt =
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

lemma routed_call_alternative_tree_bot [simp]:
  assumes "is_bot entry"
  shows "routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p (cont, entry)
           = sp_compile_with (\<lambda>d. DG d bot)
               (dg_spec_combine_transfer S (call_info_of ca p)
                 (mk_dg_man cont (\<lambda>_. gk0)) bot)"
  using assms by (simp add: routed_call_alternative_tree_def)

lemma routed_call_alternative_tree_nonbot [simp]:
  assumes "\<not> is_bot entry"
  shows "routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p (cont, entry)
     = Side (seed_key (FunctionEntry p) (route cc ctx entry ca)) (DG entry bot)
         (QueryL (FunctionResult p, route cc ctx entry ca)
            (\<lambda>callee_state.
               sp_compile_with (\<lambda>d. DG d bot)
                 (dg_spec_combine_transfer S (call_info_of ca p)
                   (mk_dg_man cont (\<lambda>_. gk0))
                   (locals callee_state))))"
  unfolding routed_call_alternative_tree_def using assms by (simp add: Let_def)

definition routed_callee_call_tree ::
  "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ('D \<Rightarrow> bool)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> 'D \<Rightarrow> pname
   \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p =
     enter\<^sup># S (call_info_of ca p) (mk_dg_man caller (\<lambda>_. gk0))
       (\<lambda>pairs.
          sp_compile (side_rhs_fold_dg bot
            (map (routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p) pairs)))"

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

definition routed_call_tree ::
  "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'D \<Rightarrow> pname list)
   \<Rightarrow> ('D \<Rightarrow> bool)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
where
  "routed_call_tree S gk0 seed_key resolve is_bot route ctx ca cc v =
     sp_lift_tree (QueryL (cc, ctx) Answer)
       (\<lambda>caller_state.
          sp_compile (side_rhs_fold_dg bot
            (map (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc
                    (locals caller_state))
                 (resolve v cc ca (locals caller_state)))))"


text \<open>The seed read-back hook: at a callee entry it reads the seed out of the
  \<open>locals\<close> half, matching \<open>routed_call_tree\<close>'s write.\<close>
definition routed_entry_seed_tree ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> 'k
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'D::bounded_semilattice_sup_bot \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G::bounded_semilattice_sup_bot) dg_state) strategy_tree list"
where
  "routed_entry_seed_tree seed_key gk0 route ctx v =
     (case v of FunctionEntry _ \<Rightarrow>
        [sp_lift_tree (QueryG (seed_key v ctx) Answer) (\<lambda>seed_state. Answer (DG (locals seed_state) bot))]
       | _ \<Rightarrow> [])"

lemma routed_entry_seed_tree_free:
  "x \<in> set (routed_entry_seed_tree seed_key gk0 route ctx v) \<Longrightarrow> sides_of_rhs x tau z = bot"
  unfolding routed_entry_seed_tree_def by (cases v) (auto simp: bot_fun_def)

lemma routed_entry_seed_tree_local_only:
  "x \<in> set (routed_entry_seed_tree seed_key gk0 route ctx v) \<Longrightarrow> globs (traverse_rhs x tau) = bot"
  unfolding routed_entry_seed_tree_def by (cases v) auto

text \<open>
  How a routed per-target tree relates to its parts under a solution. Each bound
  is stated for \<^emph>\<open>one\<close> alternative of the list a single run of the entry
  produced, because the tree is a fold over exactly those. These are the only
  facts CALL and COMB below need about the tree's body.
\<close>


lemma routed_callee_call_tree_sides_ge_seed:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    and mem: "(cont, entry) \<in> set pairs"
    and nb: "\<not> is_bot entry"
  shows "DG entry bot
           \<le> sides_of_rhs (routed_callee_call_tree S gk0 seed_key route is_bot ctx
                (CallEdge dst pars args) cc caller p) \<sigma>
                (Inr (seed_key (FunctionEntry p)
                   (route cc ctx entry (CallEdge dst pars args))))"
proof -
  let ?F = "routed_call_alternative_tree S gk0 seed_key route is_bot ctx (CallEdge dst pars args) cc p"
  let ?k = "Inr (seed_key (FunctionEntry p) (route cc ctx entry (CallEdge dst pars args)))"
  have "DG entry bot \<le> sides_of_rhs (?F (cont, entry)) \<sigma> ?k"
    unfolding routed_call_alternative_tree_def using nb by (simp add: Let_def)
  also have "\<dots> \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg bot (map ?F pairs))) \<sigma> ?k"
    by (rule sides_le_side_rhs_fold_dg) (use mem in force)
  also have "\<dots> \<le> sides_of_rhs (routed_callee_call_tree S gk0 seed_key route is_bot ctx
                     (CallEdge dst pars args) cc caller p) \<sigma> ?k"
    unfolding routed_callee_call_tree_def
    by (simp add: enter_runsD_sides[OF R] sup_fun_def)
  finally show ?thesis .
qed

text \<open>
  The entry program's own publications survive into the call's, whatever the
  alternatives turn out to be --- this is the half a specification with an
  effectful entry needs, and it holds without selecting an alternative at all.
\<close>

lemma routed_callee_call_tree_sides_ge_prefix:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
  shows "pub \<le> sides_of_rhs
                 (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma>"
  unfolding routed_callee_call_tree_def
  by (simp add: enter_runsD_sides[OF R])

text \<open>
  One rung further out: one resolved target's contribution survives the fold
  over the site's targets. Stated without a locale so a proof that must place a
  publication inside the solution --- one whose concretization reads the global
  channel --- can walk outwards from a call site it has not yet routed.
\<close>

lemma routed_call_tree_sides_ge_at:
  assumes mem: "p \<in> set (resolve v cc ca (locals (\<sigma> (Inl (cc, ctx)))))"
  shows "sides_of_rhs (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc
             (locals (\<sigma> (Inl (cc, ctx)))) p) \<sigma> z
           \<le> sides_of_rhs (routed_call_tree S gk0 seed_key resolve is_bot route ctx ca cc v) \<sigma> z"
proof -
  have "routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc (locals (\<sigma> (Inl (cc, ctx)))) p
          \<in> set (map (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc
                        (locals (\<sigma> (Inl (cc, ctx)))))
                  (resolve v cc ca (locals (\<sigma> (Inl (cc, ctx))))))"
    using mem by simp
  from sides_le_side_rhs_fold_dg[OF this, where acc = bot and k = z] show ?thesis
    by (simp add: routed_call_tree_def)
qed

lemma routed_callee_call_tree_sides_ge_combine:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    and mem: "(cont, entry) \<in> set pairs"
  shows "sides_of_rhs
           (routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p (cont, entry)) \<sigma> z
           \<le> sides_of_rhs
                (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> z"
proof -
  let ?F = "routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p"
  have "sides_of_rhs (?F (cont, entry)) \<sigma> z
          \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg bot (map ?F pairs))) \<sigma> z"
    by (rule sides_le_side_rhs_fold_dg) (use mem in force)
  also have "\<dots> \<le> sides_of_rhs
                    (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> z"
    unfolding routed_callee_call_tree_def
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

lemma routed_callee_call_tree_traverse_ge:
  assumes R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    and mem: "(cont, entry) \<in> set pairs"
  shows "locals (traverse_rhs
             (routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p (cont, entry)) \<sigma>)
           \<le> locals (traverse_rhs
                (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma>)"
proof -
  let ?F = "routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p"
  have "locals (traverse_rhs (?F (cont, entry)) \<sigma>)
          \<le> side_acc_dg bot \<sigma> (map ?F pairs)"
    by (rule locals_traverse_le_side_acc_dg) (use mem in force)
  also have "\<dots> = locals (traverse_rhs
                     (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma>)"
    unfolding routed_callee_call_tree_def
    by (simp add: enter_runsD_traverse[OF R] traverse_side_rhs_fold_dg)
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
  using assms
  by (simp add: sides_of_rhs_side_rhs_fold_dg_char foldr_sup_bot_of_all_bot)

lemma routed_call_tree_global_free:
  "globs (traverse_rhs (routed_call_tree S gk0 seed_key resolve is_bot route ctx ca cc v) \<sigma>) = bot"
  by (simp add: routed_call_tree_def traverse_side_rhs_fold_dg)

text \<open>
  The entry half of the condition is now stated through \<^const>\<open>enter_runs\<close>: an
  entry program publishes nothing at \<open>gk0\<close> exactly when the \<open>pub\<close> it runs to is
  \<^const>\<open>bot\<close> there. The compiled-tree phrasing this replaces could not be
  written any more --- an entry program answers a list, so it has no compiled
  tree of its own.
\<close>

lemma routed_callee_call_tree_side_free_at_gk0:
  assumes enter_free: "\<And>ci d pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub \<Longrightarrow> pub (Inr gk0) = bot"
    and enter_runs_ex: "\<And>ci d. \<exists>pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub"
    and comb_free: "\<And>ci d de z. sides_of_rhs (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer S ci (mk_dg_man d (\<lambda>_. gk0)) de)) \<sigma> z = bot"
    and ne: "\<And>p ctx'. seed_key (FunctionEntry p) ctx' \<noteq> gk0"
  shows "sides_of_rhs
           (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> (Inr gk0) = bot"
proof -
  obtain pairs pub
    where R: "enter_runs (enter\<^sup># S (call_info_of ca p))
                (mk_dg_man caller (\<lambda>_. gk0)) \<sigma> pairs pub"
    using enter_runs_ex by blast
  have alts: "\<And>t. t \<in> set (map (routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p) pairs)
                 \<Longrightarrow> sides_of_rhs t \<sigma> (Inr gk0) = bot"
    by (auto simp: routed_call_alternative_tree_def Let_def comb_free ne[THEN not_sym]
        split: if_splits)
  have "sides_of_rhs
          (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p) \<sigma> (Inr gk0)
        = pub (Inr gk0)
          \<squnion> sides_of_rhs (sp_compile (side_rhs_fold_dg bot
                (map (routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p) pairs)))
              \<sigma> (Inr gk0)"
    unfolding routed_callee_call_tree_def by (simp add: enter_runsD_sides[OF R] sup_fun_def)
  also have "\<dots> = bot"
  proof -
    have "sides_of_rhs (sp_compile (side_rhs_fold_dg bot
            (map (routed_call_alternative_tree S gk0 seed_key route is_bot ctx ca cc p) pairs)))
            \<sigma> (Inr gk0) = bot"
      by (rule sides_side_rhs_fold_dg_bot) (rule alts)
    then show ?thesis using enter_free[OF R] by simp
  qed
  finally show ?thesis .
qed

lemma routed_call_tree_side_free_at_gk0:
  assumes enter_free: "\<And>ci d pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub \<Longrightarrow> pub (Inr gk0) = bot"
    and enter_runs_ex: "\<And>ci d. \<exists>pairs pub.
        enter_runs (enter\<^sup># S ci) (mk_dg_man d (\<lambda>_. gk0)) \<sigma> pairs pub"
    and comb_free: "\<And>ci d de z. sides_of_rhs (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer S ci (mk_dg_man d (\<lambda>_. gk0)) de)) \<sigma> z = bot"
    and ne: "\<And>p ctx'. seed_key (FunctionEntry p) ctx' \<noteq> gk0"
  shows "sides_of_rhs (routed_call_tree S gk0 seed_key resolve is_bot route ctx ca cc v)
           \<sigma> (Inr gk0) = bot"
proof -
  have at_free: "\<And>caller p.
      sides_of_rhs (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc caller p)
        \<sigma> (Inr gk0) = bot"
    by (rule routed_callee_call_tree_side_free_at_gk0)
       (rule enter_free enter_runs_ex comb_free ne, assumption?)+
  have "sides_of_rhs (sp_compile (side_rhs_fold_dg bot
          (map (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc
                  (locals (\<sigma> (Inl (cc, ctx)))))
             (resolve v cc ca (locals (\<sigma> (Inl (cc, ctx)))))))) \<sigma> (Inr gk0) = bot"
    by (rule sides_side_rhs_fold_dg_bot) (auto simp: at_free)
  then show ?thesis by (simp add: routed_call_tree_def)
qed


end
