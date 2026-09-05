theory DG_Spec_Sound
  imports DG_Spec "Voblint_CFG.CFG_Transfer"
begin

section \<open>What a manager-native specification owes a concretization\<close>

text \<open>
  Soundness of a manager-native \<open>dg_spec\<close> is stated against the compiled
  trees' own observations: an assumption's input is what the tree reads
  (\<open>\<tau>\<close> at the source and the routed slot), its output is the returned local
  value together with the contribution the tree actually publishes at that
  slot. There is no reconstructed \<open>'dg \<times> 'dl\<close> pair anywhere: a transfer
  that publishes nothing is judged against \<open>bot\<close>, and a concretization
  that ignores its global argument (every Base-style domain) discharges
  that side vacuously. \<open>sound_local_dg_spec\<close> below is exactly that
  collapse: for a specification built from pure local functions, all
  global obligations vanish and the locale's assumptions are the plain
  pure-transfer inclusions an existing domain already proves.
\<close>

text \<open>
  This locale is stated for a \<^emph>\<open>single\<close> global: \<open>gammaDG\<close> takes one \<open>'G\<close>, read at
  the one slot \<open>Inr gk\<close>, so a specification publishing at two distinct global
  names would have contributions this concretization never sees. The global-name
  type is therefore pinned at \<^typ>\<open>unit\<close> here and the manager is built from the
  constant embedding, rather than stating an obligation over a namespace the
  conclusion cannot account for. Every analysis in this tree has one global, so
  nothing is lost today; a second global needs \<open>gammaDG\<close> over a global
  \<^emph>\<open>environment\<close> first, and that is what would generalize this locale.
\<close>

text \<open>
  What a call's alternatives must establish. The coverage contract is the part
  that does not mention a tree: \<open>enter_runs\<close> and \<open>enter_deps\<close> below do describe
  an entry program and the continuations it is handed, but what an alternative
  \<^emph>\<open>means\<close> is settled here, before any of that.
  \<open>pairs\<close> covers a concrete caller when \<^emph>\<open>some\<close> alternative accounts for it: the
  caller store lies in the continuation half and the store the callee starts
  from lies in the entry half, in the same pair. The quantifier is existential
  because alternatives are a disjunction --- a call that splits into two of them
  has each covering the concrete runs it was computed for, and demanding that
  every alternative cover every caller would defeat the splitting the list
  exists to express.

  Keeping it separate from any particular tree is what lets an entry
  obligation be discharged once and reused: a proof about how alternatives are
  folded never has to restate what an alternative means.
\<close>

definition entry_pairs_cover ::
  "('D \<Rightarrow> 's set) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'D enter_result list \<Rightarrow> bool"
where
  "entry_pairs_cover gammaD caller entered pairs \<longleftrightarrow>
     (\<exists>cont entry. (cont, entry) \<in> set pairs
        \<and> caller \<in> gammaD cont \<and> entered \<in> gammaD entry)"

lemma entry_pairs_coverI [intro]:
  assumes "(cont, entry) \<in> set pairs"
    and "caller \<in> gammaD cont" and "entered \<in> gammaD entry"
  shows "entry_pairs_cover gammaD caller entered pairs"
  using assms unfolding entry_pairs_cover_def by blast

lemma entry_pairs_coverE [elim]:
  assumes "entry_pairs_cover gammaD caller entered pairs"
  obtains cont entry
    where "(cont, entry) \<in> set pairs"
      and "caller \<in> gammaD cont" and "entered \<in> gammaD entry"
  using assms unfolding entry_pairs_cover_def by blast

lemma entry_pairs_cover_Nil [simp]:
  "\<not> entry_pairs_cover gammaD caller entered []"
  by (simp add: entry_pairs_cover_def)

text \<open>
  An entry transfer is a program, so its alternatives cannot be read back out of
  it: the tree it builds answers into the solver's carrier, and a list of pairs
  does not live there. What \<^emph>\<open>can\<close> be said is how it behaves under a fixed
  solution. \<open>enter_runs T m sigma pairs pub\<close> says that under \<open>sigma\<close> the program
  hands its continuation exactly \<open>pairs\<close> and publishes exactly \<open>pub\<close> on the way,
  whatever the continuation then does --- the reads resolve against \<open>sigma\<close>, so
  both are determined before any continuation is chosen.

  This is what lets a proof name an alternative. Rather than extracting the list
  after the fact, a caller fixes the \<open>pairs\<close> the continuation receives and
  reasons under that, which is the ordinary way to reason about a
  continuation-passing program. \<open>pub\<close> is carried separately because the prefix's
  own publications are part of what the call establishes: an entry that reads a
  global and republishes it has those contributions in \<open>pub\<close>, not in anything
  the continuation returns.
\<close>

definition enter_runs ::
  "('x,'k,'v,'D::bounded_semilattice_sup_bot,'G::bounded_semilattice_sup_bot) man_enter_transfer
   \<Rightarrow> ('x,'k,'v,'D,'G) man \<Rightarrow> ('x + 'k \<Rightarrow> ('D,'G) dg_state)
   \<Rightarrow> 'D enter_result list \<Rightarrow> ('x + 'k \<Rightarrow> ('D,'G) dg_state) \<Rightarrow> bool"
where
  "enter_runs T m sigma pairs pub \<longleftrightarrow>
     (\<forall>K. traverse_rhs (T m K) sigma = traverse_rhs (K pairs) sigma
          \<and> sides_of_rhs (T m K) sigma = pub \<squnion> sides_of_rhs (K pairs) sigma)"

lemma enter_runsD_traverse:
  assumes "enter_runs T m sigma pairs pub"
  shows "traverse_rhs (T m K) sigma = traverse_rhs (K pairs) sigma"
  using assms unfolding enter_runs_def by blast

lemma enter_runsD_sides:
  assumes "enter_runs T m sigma pairs pub"
  shows "sides_of_rhs (T m K) sigma = pub \<squnion> sides_of_rhs (K pairs) sigma"
  using assms unfolding enter_runs_def by blast

text \<open>A pure entry hands over its alternatives directly and publishes nothing.\<close>

lemma enter_runs_local_enter_transfer [intro]:
  "enter_runs (local_enter_transfer f) m sigma (f (man_local m)) bot"
  by (simp add: enter_runs_def local_enter_transfer_def sp_return_def
      sup_fun_def bot_fun_def)

text \<open>The same at a built manager, where \<^const>\<open>man_local\<close> has already been
  read off. A caller whose alternatives are written out as a list --- which is
  how every routed instance states its entry obligation --- matches this one by
  ordinary unification, where the rule above would first have to reduce
  \<open>man_local (mk_dg_man d key)\<close> under a higher-order variable.\<close>

lemma enter_runs_local_enter_transfer_mk_dg_man [intro]:
  "enter_runs (local_enter_transfer f) (mk_dg_man d key) sigma (f d) bot"
  using enter_runs_local_enter_transfer[of f "mk_dg_man d key" sigma] by simp

text \<open>The converse direction, which a consumer needs when it has an arbitrary run
  in hand rather than the one above: a pure entry's publication is pinned, so no
  case analysis on the run is possible.\<close>

lemma enter_runs_local_pub_bot:
  assumes "enter_runs (local_enter_transfer f) m sigma pairs pub"
  shows "pub = bot"
proof -
  have "sides_of_rhs (local_enter_transfer f m (\<lambda>_. Answer bot)) sigma
          = pub \<squnion> sides_of_rhs (Answer bot) sigma"
    using assms by (rule enter_runsD_sides)
  then show ?thesis
    by (simp add: local_enter_transfer_def sp_return_def fun_eq_iff sup_fun_def bot_fun_def)
qed

text \<open>
  Values and publications are not everything the generator needs to know about
  an entry program: what it \<^emph>\<open>reads\<close> matters too, and reading is invisible in
  both. An entry that consults a global depends on that unknown even when it
  publishes \<open>bot\<close> there, and the solver's admissibility arguments are stated
  over dependencies, not over answers.

  \<open>enter_deps\<close> is deliberately a separate relation over the \<^emph>\<open>same\<close> \<open>pairs\<close>: a
  proof that obtained its alternatives from \<^const>\<open>enter_runs\<close> and its
  dependencies from an independently quantified list would be talking about two
  different executions. Packaging the two together, with
  \<^const>\<open>entry_pairs_cover\<close>, is what keeps one call's story single.
\<close>

definition enter_deps ::
  "('x,'k,'v,'D::bounded_semilattice_sup_bot,'G::bounded_semilattice_sup_bot) man_enter_transfer
   \<Rightarrow> ('x,'k,'v,'D,'G) man \<Rightarrow> ('x + 'k \<Rightarrow> ('D,'G) dg_state)
   \<Rightarrow> 'D enter_result list \<Rightarrow> ('x + 'k) set \<Rightarrow> bool"
where
  "enter_deps T m sigma pairs deps \<longleftrightarrow>
     (\<forall>K. dep_aux sigma (T m K) = deps \<union> dep_aux sigma (K pairs))"

lemma enter_depsD:
  assumes "enter_deps T m sigma pairs deps"
  shows "dep_aux sigma (T m K) = deps \<union> dep_aux sigma (K pairs)"
  using assms unfolding enter_deps_def by blast

text \<open>A pure entry reads nothing of its own.\<close>

lemma enter_deps_local_enter_transfer [intro]:
  "enter_deps (local_enter_transfer f) m sigma (f (man_local m)) {}"
  by (simp add: enter_deps_def local_enter_transfer_def sp_return_def)

lemma enter_deps_local_enter_transfer_mk_dg_man [intro]:
  "enter_deps (local_enter_transfer f) (mk_dg_man d key) sigma (f d) {}"
  using enter_deps_local_enter_transfer[of f "mk_dg_man d key" sigma] by simp

text \<open>
  The core carries everything that is independent of how a call is compiled:
  the ordinary edge transfers and the return combine. Entry is not here. A
  \<^const>\<open>dgs_enter\<close> answers a list, which is not an equation's answer, so what
  makes it sound is a property of the tree the routed generator builds from
  it, stated through \<^const>\<open>entry_pairs_cover\<close> against the routed alternative
  the solved system actually selects --- a property this locale alone cannot
  state, since it never mentions how a call compiles.

  So \<open>sound_dg_spec_core\<close> is the common core and not a complete soundness statement:
  interpreting it alone leaves a call's entry entirely unconstrained.
  \<open>dg_ctx_activation_base\<close> (\<open>Routed_Context\<close>, downstream in this session) is
  the complete statement, extending this core with that entry obligation for
  the routed equation shape, and is what an analysis should be asked to
  establish.
\<close>

subsection \<open>Proof-level compiled combine form\<close>

text \<open>
  A return combine compiled the way an edge transfer is: read the caller
  continuation and the callee exit from two unknowns, and run the composed
  combine against them. No generator builds this. The routed call tree already
  holds the alternative's own continuation, so it runs
  \<^const>\<open>dg_spec_combine_transfer\<close> against that value directly and never reads
  a caller unknown a second time.

  It lives here, ahead of the locale that consumes it, because \<^emph>\<open>stating\<close>
  the return obligation at a pair of addresses is all it is for: a proof that
  quantifies over the pair needs a tree to quantify over. Reading it in
  \<^theory>\<open>Voblint_Framework.DG_Spec\<close>, among the formers a generator really
  does build, invited exactly the wrong conclusion.

  Both levels earn their place, which is why there are two of them.
  \<open>combine_transfer_tree\<close> is used at an arbitrary
  \<^type>\<open>man_combine_transfer\<close> --- by the ownership-split observation
  equations here, and by the relational domain's --- while
  \<open>dg_spec_combine_tree\<close> is used at a selected specification, by
  \<open>DG_Ctx_Activation\<close>'s own \<open>dg_ctx_act_comb_covered\<close> downstream, whose two
  bounds are assumptions about this tree at two \<^emph>\<open>solver addresses\<close>.
  That last part is what the value form cannot express: the caller
  supplies those bounds from a post-solution at \<open>Inl (cl, c1)\<close> and
  \<open>Inl (ex, c2)\<close>, so the obligation has to name the addresses, not the values
  they hold. \<open>combine_program_at\<close> is the one internal step, kept for symmetry
  with the edge driver rather than for a second consumer.
\<close>

definition combine_program_at ::
  "('x,'k,'v,'dl,'dg) man_combine_transfer
   \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl::bot,'dg) dg_state,'dl) strategy_program"
where
  "combine_program_at transfer src_cc src_ex key =
     do {
       dc \<leftarrow> dg_read_at src_cc;
       de \<leftarrow> dg_read_at src_ex;
       transfer (mk_dg_man dc key) de
     }"

definition combine_transfer_tree ::
  "('x,'k,'v,'dl::bot,'dg::bot) man_combine_transfer \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state) strategy_tree"
where
  "combine_transfer_tree T src_cc src_ex key =
     sp_compile_with (\<lambda>d. DG d bot) (combine_program_at T src_cc src_ex key)"

definition dg_spec_combine_tree ::
  "('x,'k,'v,'dl::bot,'dg::bot) dg_spec \<Rightarrow> call_info \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state) strategy_tree"
where
  "dg_spec_combine_tree S ci src_cc src_ex key =
     combine_transfer_tree (dg_spec_combine_transfer S ci) src_cc src_ex key"

text \<open>
  What compilation costs an observation here: the two source reads, and then
  the composed combine run at the values they produced. The counterpart of
  \<^theory>\<open>Voblint_Framework.DG_Spec\<close>'s edge bridges, and untagged for the same
  reason.
\<close>

lemma traverse_combine_transfer_tree:
  "traverse_rhs (combine_transfer_tree T src_cc src_ex key) \<tau>
     = traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
         (T (mk_dg_man (locals (\<tau> src_cc)) key) (locals (\<tau> src_ex)))) \<tau>"
  by (simp add: combine_transfer_tree_def combine_program_at_def sp_compile_with_def
      sp_bind_def)

lemma sides_combine_transfer_tree:
  "sides_of_rhs (combine_transfer_tree T src_cc src_ex key) \<tau>
     = sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
         (T (mk_dg_man (locals (\<tau> src_cc)) key) (locals (\<tau> src_ex)))) \<tau>"
  by (simp add: combine_transfer_tree_def combine_program_at_def sp_compile_with_def
      sp_bind_def)

lemma dep_aux_combine_transfer_tree:
  "dep_aux \<tau> (combine_transfer_tree T src_cc src_ex key)
     = insert src_cc (insert src_ex
         (dep_aux \<tau> (sp_compile_with (\<lambda>d. DG d bot)
            (T (mk_dg_man (locals (\<tau> src_cc)) key) (locals (\<tau> src_ex))))))"
  by (simp add: combine_transfer_tree_def combine_program_at_def sp_compile_with_def
      sp_bind_def)

text \<open>What the compiled form observes when both stages are local, and the two
  reads it always makes --- the combine counterparts of the edge-tree facts in
  \<^theory>\<open>Voblint_Framework.DG_Spec\<close>.\<close>

lemma traverse_local_combine_tree [simp]:
  "traverse_rhs (combine_transfer_tree (local_combine_transfer h) src_cc src_ex gk) \<tau>
     = DG (h (locals (\<tau> src_cc)) (locals (\<tau> src_ex))) bot"
  by (simp add: traverse_combine_transfer_tree local_combine_transfer_def
      sp_compile_with_def sp_return_def)

lemma sides_local_combine_tree [simp]:
  "sides_of_rhs (combine_transfer_tree (local_combine_transfer h) src_cc src_ex gk) \<tau> k
     = bot"
  by (simp add: sides_combine_transfer_tree local_combine_transfer_def
      sp_compile_with_def sp_return_def)

lemma dep_aux_local_combine_tree [simp]:
  "dep_aux \<tau> (combine_transfer_tree (local_combine_transfer h) src_cc src_ex gk)
     = {src_cc, src_ex}"
  by (simp add: dep_aux_combine_transfer_tree local_combine_transfer_def
      sp_compile_with_def sp_return_def)

lemma dep_aux_combine_transfer_tree_sources:
  "{src_cc, src_ex} \<subseteq> dep_aux \<tau> (combine_transfer_tree T src_cc src_ex gk)"
  by (simp add: dep_aux_combine_transfer_tree)

lemma dep_aux_dg_spec_combine_tree_sources:
  "{src_cc, src_ex} \<subseteq> dep_aux \<tau> (dg_spec_combine_tree S ci src_cc src_ex gk)"
  unfolding dg_spec_combine_tree_def by (rule dep_aux_combine_transfer_tree_sources)

subsection \<open>What a manager-native specification owes\<close>

locale sound_dg_spec_core =
  fixes S :: "('x,'k,unit,'D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
  assumes gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow> gammaDG d g \<subseteq> gammaDG d' g'"
    and step_sound:
      "edge_collect a (gammaDG (locals (\<tau> src)) (globs (\<tau> (Inr gk))))
         \<subseteq> gammaDG (locals (traverse_rhs (dg_spec_edge_tree S a src (\<lambda>_. gk)) \<tau>))
                   (globs (sides_of_rhs (dg_spec_edge_tree S a src (\<lambda>_. gk)) \<tau> (Inr gk)))"
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG dc (globs (\<tau> (Inr gk)));
        t \<in> gammaDG de (globs (\<tau> (Inr gk)))\<rbrakk> \<Longrightarrow>
        combine_collect gs (ci_dst ci) s t
          \<in> gammaDG (locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
                  (dg_spec_combine_transfer S ci (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>))
                    (globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
                  (dg_spec_combine_transfer S ci (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk)))"

text \<open>
  The obligation is stated at \<^emph>\<open>values\<close> rather than at two unknown reads,
  because the routed call boundary applies combine at the continuation the
  entry produced, which is not in general what any unknown holds. Where the
  continuation \<^emph>\<open>is\<close> the caller's own solved value --- the monovariant call
  shape --- the tree form below is the instance at that value, so nothing is
  lost for a generator that reads both sides from unknowns.
\<close>

lemma (in sound_dg_spec_core) combine_sound_tree:
  assumes sc: "s \<in> gammaDG (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk)))"
    and se: "t \<in> gammaDG (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk)))"
  shows "combine_collect gs (ci_dst ci) s t
          \<in> gammaDG (locals (traverse_rhs
                (dg_spec_combine_tree S ci src_cc src_ex (\<lambda>_. gk)) \<tau>))
                    (globs (sides_of_rhs (dg_spec_combine_tree S ci src_cc src_ex (\<lambda>_. gk))
                                          \<tau> (Inr gk)))"
  using combine_sound[where dc = "locals (\<tau> src_cc)" and de = "locals (\<tau> src_ex)"
      and \<tau> = \<tau> and gk = gk and ci = ci, OF sc se]
  by (simp add: dg_spec_combine_tree_def traverse_combine_transfer_tree
      sides_combine_transfer_tree)

section \<open>The collapsed obligations of a local-only specification\<close>

locale sound_local_dg_spec =
  fixes sk :: "'D::bounded_semilattice_sup_bot \<Rightarrow> 'D"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'D \<Rightarrow> 'D"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'D \<Rightarrow> 'D"
    and bd :: "pname \<Rightarrow> 'D \<Rightarrow> 'D"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D"
    and en :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D enter_result list"
    and ev :: "analysis_event \<Rightarrow> 'D \<Rightarrow> 'D"
    and ce :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D"
    and ca :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D"
    and gammaD :: "'D \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
  assumes gammaD_mono: "d \<le> d' \<Longrightarrow> gammaD d \<subseteq> gammaD d'"
    and step_sound_local:
      "edge_collect a (gammaD d) \<subseteq> gammaD (local_spec_step sk asn sp br bd rt ev a d)"
    and enter_sound_local:
      "s \<in> gammaD d \<Longrightarrow>
         entry_pairs_cover gammaD s
           (call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           (en ci d)"
    and combine_sound_local:
      "\<lbrakk>s \<in> gammaD dc; t \<in> gammaD de\<rbrakk> \<Longrightarrow>
        combine_collect gs (ci_dst ci) s t \<in> gammaD (ca ci (ce ci dc de) de)"
begin

theorem local_spec_sound:
  "sound_dg_spec_core (local_dg_spec sk asn sp br bd rt en ev ce ca) (\<lambda>d g. gammaD d) gs"
proof (unfold_locales, goal_cases mono step comb)
  case mono
  then show ?case by (meson gammaD_mono)
next
  case step
  then show ?case
    by (simp add: dg_spec_edge_tree_def step_sound_local)
next
  case comb
  then show ?case
    by (simp add: local_combine_transfer_def combine_sound_local)
qed

end

end

