theory Analysis_Result
  imports "Voblint_Domain.Nonrelational_Reachability" "Voblint_CFG.CFG_Def"
begin

section \<open>Solved analysis results\<close>

text \<open>
  The canonical, domain-generic shape of a finished analysis: a set of covered
  @{typ "pp \<times> 'ctx"} keys together with a total lookup into a per-point
  abstract state. Checks, reports, and rendering are downstream consumers of
  this table, not siblings of it.

  The datatype constrains neither the key set nor the payloads. What the rest
  of this text describes --- finitely many keys, and canonical payloads --- is
  \<open>wf_analysis_result\<close>, stated at the end of this theory. Its two halves are
  not established alike: an adapter canonicalizes every payload it publishes,
  so canonicality is unconditional, while finiteness holds only for those
  context policies whose whole context space is bounded in advance, and is
  carried as a hypothesis everywhere else.

  \<^const>\<open>Bot\<close> means ``the solver's canonical result at this key is an
  outer \<^const>\<open>Bot\<close>'', or the key is absent from \<open>result_keys\<close> altogether;
  \<open>Lifted a\<close> means ``the canonical result is \<^const>\<open>Lifted\<close>'', with the
  local unknown projected to the abstract state \<open>a\<close>. This is a structural
  reading, not a semantic-emptiness test: raw solver values are
  canonicalized -- a witness-bottom \<^const>\<open>Lifted\<close> payload collapsed to
  \<^const>\<open>Bot\<close> -- \<^emph>\<open>before\<close> they reach this boundary (every public result
  adapter routes through \<open>canonicalize_lift\<close>), so by the time a value
  reaches \<open>lookup_context\<close> here, \<^const>\<open>Bot\<close> and \<^const>\<open>Lifted\<close> already
  agree with concrete emptiness and non-emptiness respectively.
\<close>

subsection \<open>Per-point reachability\<close>

text \<open>
  Per-point reachability is \<^typ>\<open>'a lifted\<close> itself
  (\<^theory>\<open>Voblint_Domain.Reachability_Lift\<close>), not a nominal copy of it: the
  reachability reading is fixed by \<open>gamma_point\<close> below rather than
  left to the caller, and every operation on it (\<open>is_reachable_point\<close>,
  \<open>join_point_with\<close>, ...) is stated directly in terms of \<^const>\<open>Bot\<close>/
  \<^const>\<open>Lifted\<close>.
\<close>

text \<open>
  Reachability is read off the constructor, never by comparing against
  \<^const>\<open>Bot\<close> with \<open>=\<close>: an equality test would force an \<open>equal\<close>
  instance on the payload, which nothing else about the result table needs.
  \<^const>\<open>map_lift\<close> (\<^theory>\<open>Voblint_Domain.Reachability_Lift\<close>) is the
  functorial map (payload rewriting that leaves reachability alone).
\<close>

fun is_reachable_point :: "'a lifted \<Rightarrow> bool" where
  "is_reachable_point Bot = False"
| "is_reachable_point (Lifted _) = True"

lemma is_reachable_point_iff: "is_reachable_point p \<longleftrightarrow> p \<noteq> Bot"
  by (cases p) simp_all

definition gamma_point :: "'a::sound_domain abs_state lifted \<Rightarrow> store set" where
  "gamma_point p = (case p of Bot \<Rightarrow> {} | Lifted st \<Rightarrow> \<lbrakk>st\<rbrakk>)"

lemma gamma_point_Bot [simp]: "gamma_point Bot = {}"
  unfolding gamma_point_def by simp

lemma gamma_point_Lifted [simp]: "gamma_point (Lifted st) = \<lbrakk>st\<rbrakk>"
  unfolding gamma_point_def by simp

text \<open>
  The shape every migrated report's per-node environment reads a
  \<^typ>\<open>'a lifted\<close> point through (\<open>Bot \<Rightarrow> bot\<close>, \<open>Lifted st \<Rightarrow> st\<close>)
  concretizes to exactly \<^const>\<open>gamma_point\<close>, so a soundness proof against
  that environment never needs to re-case-split the point state by hand.
\<close>

lemma gamma_state_of_reachable_env [simp]:
  "\<lbrakk>case p of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk> = gamma_point p"
  for p :: "'a::sound_domain abs_state lifted"
  by (cases p) simp_all

subsection \<open>The result table\<close>

text \<open>
  \<open>result_keys\<close> is the authoritative coverage surface --- the keys the
  solver actually reached --- while \<open>result_at\<close> is merely a total
  lookup function, defined everywhere but meaningful only on the key set.
  \<open>lookup_context\<close> keeps that distinction explicit rather than trusting
  \<open>result_at\<close> to answer sensibly off the key set.

  \<open>lookup_context\<close> (per context) is canonical. The per-node views ---
  liveness and the joined state --- are derived projections over the contexts
  covered at a node, and both live below.

  \<^typ>\<open>'ctx\<close> carries no ordering or enumeration constraint: real context
  types include interval-vector and call-string contexts, which have
  neither.
\<close>

datatype (plugins del: quickcheck_narrowing) ('ctx, 'a) analysis_result =
  Analysis_Result
    (result_keys: "(pp \<times> 'ctx) set")
    (result_at: "pp \<Rightarrow> 'ctx \<Rightarrow> 'a lifted")

definition contexts_at :: "('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> 'ctx set" where
  "contexts_at r v = snd ` Set.filter (\<lambda>(v', ctx). v' = v) (result_keys r)"

definition lookup_context ::
  "('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> 'ctx \<Rightarrow> 'a lifted" where
  "lookup_context r v ctx =
     (if (v, ctx) \<in> result_keys r then result_at r v ctx else Bot)"

lemma contexts_at_iff [simp]: "ctx \<in> contexts_at r v \<longleftrightarrow> (v, ctx) \<in> result_keys r"
  unfolding contexts_at_def by force

lemma lookup_context_absent [simp]:
  "(v, ctx) \<notin> result_keys r \<Longrightarrow> lookup_context r v ctx = Bot"
  unfolding lookup_context_def by simp

subsection \<open>Telling ``analysed and dead'' from ``never analysed''\<close>

text \<open>
  \<^const>\<open>lookup_context\<close> answers \<^const>\<open>Bot\<close> for two unrelated reasons: the
  solver covered the key and stored \<^const>\<open>Bot\<close> there, or it never covered the
  key at all. The first is a proved statement about the program; the second is
  the absence of one. A reader of the answer alone cannot tell which happened,
  so a claim about concrete unreachability must not be stated over it.
\<close>

datatype (plugins del: quickcheck_narrowing) 'a context_result =
    Uncovered
  | Covered "'a lifted"

text \<open>
  \<^typ>\<open>'a context_result\<close> keeps the two apart at the lookup, rather than
  pushing the distinction into \<^typ>\<open>'a lifted\<close>: making non-coverage a lattice
  element would put solver bookkeeping into the abstract domain and raise
  questions -- how it orders against \<^const>\<open>Bot\<close>, what a join with it means --
  that have no semantic answer. Coverage is metadata about a solve; \<^const>\<open>Bot\<close>
  is a statement about a program.
\<close>

definition lookup_context_result ::
  "('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> 'ctx \<Rightarrow> 'a context_result" where
  "lookup_context_result r v ctx =
     (if (v, ctx) \<in> result_keys r then Covered (result_at r v ctx) else Uncovered)"

lemma lookup_context_result_covered [simp]:
  "(v, ctx) \<in> result_keys r \<Longrightarrow>
     lookup_context_result r v ctx = Covered (result_at r v ctx)"
  unfolding lookup_context_result_def by simp

lemma lookup_context_result_uncovered [simp]:
  "(v, ctx) \<notin> result_keys r \<Longrightarrow> lookup_context_result r v ctx = Uncovered"
  unfolding lookup_context_result_def by simp

lemma lookup_context_result_eq_Uncovered_iff:
  "lookup_context_result r v ctx = Uncovered \<longleftrightarrow> (v, ctx) \<notin> result_keys r"
  unfolding lookup_context_result_def by simp

lemma lookup_context_result_eq_Covered_iff:
  "lookup_context_result r v ctx = Covered x \<longleftrightarrow>
     (v, ctx) \<in> result_keys r \<and> result_at r v ctx = x"
  unfolding lookup_context_result_def by auto

text \<open>
  Where the information is lost, named so that losing it is a visible step.
  \<^const>\<open>lookup_context\<close> is exactly this totalization, which is why it is safe
  to keep for callers that only ever read a covered key -- and why a soundness
  claim may not be stated over it directly.
\<close>

fun context_result_or_bot :: "'a context_result \<Rightarrow> 'a lifted" where
  "context_result_or_bot Uncovered = Bot"
| "context_result_or_bot (Covered x) = x"

lemma lookup_context_eq_or_bot:
  "lookup_context r v ctx =
     context_result_or_bot (lookup_context_result r v ctx)"
  unfolding lookup_context_def lookup_context_result_def by simp

text \<open>
  The logical core of every ``the reported point is unreachable'' claim, stated
  once here rather than per domain. It starts from \<^term>\<open>Covered Bot\<close>, so an
  uncovered node cannot satisfy it however the caller obtained its inclusion.
\<close>

lemma reported_covered_unreachable_empty:
  assumes lookup: "lookup_context_result r v ctx = Covered Bot"
    and sound: "C \<subseteq> gamma_lift gam (lookup_context r v ctx)"
  shows "C = {}"
  using sound unfolding lookup_context_eq_or_bot lookup by simp

text \<open>
  The node-level reading, quantifying over the contexts at \<open>v\<close>. It asks only
  that every \<^emph>\<open>stored\<close> result there is \<^const>\<open>Bot\<close>; an uncovered context is
  permitted rather than required to be absent, since whatever an uncovered
  context contributes is a question for the solve that produced the table, not
  for this predicate. A single \<^term>\<open>Covered (Lifted s)\<close> at any context defeats
  it, which is the whole point: that context may still carry executions.

  Read the vacuous case before using this: a node with \<^emph>\<open>no\<close> stored context
  satisfies it, since there is nothing to be non-\<^const>\<open>Bot\<close>. On its own that
  would be a hole --- ``never analysed'' passing as ``proved dead''. It is not
  one only where a caller separately knows that an unstored context contributes
  nothing, which is a property of the solve, not of this table. Do not lift this
  predicate out of a setting that establishes it.
\<close>

definition result_node_is_bottom ::
  "('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> bool" where
  "result_node_is_bottom r v \<longleftrightarrow>
     (\<forall>ctx a. lookup_context_result r v ctx = Covered a \<longrightarrow> a = Bot)"

lemma result_node_is_bottomI:
  assumes "\<And>ctx a. lookup_context_result r v ctx = Covered a \<Longrightarrow> a = Bot"
  shows "result_node_is_bottom r v"
  unfolding result_node_is_bottom_def using assms by blast

lemma result_node_is_bottomD:
  assumes bot: "result_node_is_bottom r v"
    and covered: "(v, ctx) \<in> result_keys r"
  shows "lookup_context_result r v ctx = Covered Bot"
proof -
  have eq: "lookup_context_result r v ctx = Covered (result_at r v ctx)"
    using covered by simp
  have "result_at r v ctx = Bot"
    using bot eq unfolding result_node_is_bottom_def by blast
  with eq show ?thesis by simp
qed

lemma result_node_is_bottom_iff_keys:
  "result_node_is_bottom r v \<longleftrightarrow>
     (\<forall>ctx. (v, ctx) \<in> result_keys r \<longrightarrow> result_at r v ctx = Bot)"
  unfolding result_node_is_bottom_def
  by (auto simp: lookup_context_result_eq_Covered_iff)

lemma gamma_point_eq_gamma_lift:
  "gamma_point p = gamma_lift (\<lambda>st. \<lbrakk>st\<rbrakk>) p"
  unfolding gamma_point_def gamma_lift_def ..

lemma reported_covered_unreachable_empty_point:
  assumes lookup: "lookup_context_result r v ctx = Covered Bot"
    and sound: "C \<subseteq> gamma_point (lookup_context r v ctx)"
  shows "C = {}"
  using sound unfolding gamma_point_eq_gamma_lift
  by (rule reported_covered_unreachable_empty[OF lookup])

text \<open>
  What the report's own flag is worth: with coverage in hand it identifies
  \<^term>\<open>Covered Bot\<close>, and without it, nothing. This is the intended way to
  reach @{thm [source] reported_covered_unreachable_empty} from a report entry.
\<close>

text \<open>
  For a context-insensitive result there is only one context to quantify over,
  so the report's own flag already gives the node predicate --- no coverage
  side condition, because the uncovered case is the vacuous one the predicate
  permits. This is what connects a printed \<open>unreachable\<close> column to the
  node-level theorems: the flag is what the CLI computes, and
  \<^const>\<open>result_node_is_bottom\<close> is what they assume.
\<close>

lemma report_flag_imp_result_node_is_bottom:
  fixes r :: "(unit, 'a::bot) analysis_result"
  assumes flag: "fst (report_lifted_state (lookup_context r v ()))"
  shows "result_node_is_bottom r v"
proof (rule result_node_is_bottomI)
  fix ctx :: unit and a
  assume cov: "lookup_context_result r v ctx = Covered a"
  then have keys: "(v, ctx) \<in> result_keys r" and val: "result_at r v ctx = a"
    by (simp_all add: lookup_context_result_eq_Covered_iff)
  have unit_bot: "lookup_context r v () = Bot"
    using flag by (simp add: report_lifted_state_unreachable_iff)
  then have "lookup_context r v ctx = Bot"
    by (cases ctx) simp
  then show "a = Bot"
    using keys val unfolding lookup_context_def by simp
qed

lemma report_flag_covered_eq_Covered_Bot:
  fixes r :: "('ctx, 'a::bot) analysis_result"
  assumes covered: "(v, ctx) \<in> result_keys r"
    and flag: "fst (report_lifted_state (lookup_context r v ctx))"
  shows "lookup_context_result r v ctx = Covered Bot"
  using covered flag
  by (simp add: report_lifted_state_unreachable_iff lookup_context_def)

lemma lookup_context_LiftedD [dest]:
  "lookup_context r v ctx = Lifted st \<Longrightarrow> ctx \<in> contexts_at r v"
  using lookup_context_absent by fastforce

text \<open>
  Liveness of a node needs no join at all: a node is live exactly when some
  context covered there is reachable. Stated this way it constrains nothing
  beyond what \<^const>\<open>contexts_at\<close> already needs --- no order, no lattice, and
  in particular nothing at all about the state payload.
\<close>

definition node_live_ex :: "('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> bool" where
  "node_live_ex r v =
     (\<exists>ctx\<in>contexts_at r v. is_reachable_point (lookup_context r v ctx))"

lemma node_live_ex_absent [simp]:
  "contexts_at r v = {} \<Longrightarrow> \<not> node_live_ex r v"
  unfolding node_live_ex_def by simp

subsection \<open>Joining the contexts at a node\<close>

text \<open>
  The per-node view joins the states of every context covered at that node.
  The join arrives as an explicit function argument rather than through a
  \<^class>\<open>semilattice_sup\<close> instance on the payload, because the production
  payload is \<^typ>\<open>'a abs_state\<close>: its \<open>\<le>\<close> quantifies over all of \<^typ>\<open>vname\<close>,
  so that instance has no executable realization even though the domain
  \<^typ>\<open>'a\<close> underneath it has one. Passing the join keeps every class
  constraint that reaches code generation on the domain, never on the state.

  \<^const>\<open>Bot\<close> is the fold's unit, so the empty-context case needs no
  separate guard: a node the solver never covered folds to \<^const>\<open>Bot\<close>
  on its own.
\<close>

fun join_point_with ::
  "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted"
where
  "join_point_with j Bot y = y"
| "join_point_with j x Bot = x"
| "join_point_with j (Lifted a) (Lifted b) = Lifted (j a b)"

definition join_abs_state_with ::
  "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "join_abs_state_with j a b = (\<lambda>x. j (a x) (b x))"

text \<open>
  Instantiating the join with the domain's own \<open>\<squnion>\<close> recovers exactly the
  lattice join of the payloads, variable by variable: the explicit argument is
  a way around the missing dictionary, not a different operation.
\<close>

lemma join_abs_state_with_sup [simp]:
  "join_abs_state_with (\<squnion>) a (b :: 'a::semilattice_sup abs_state) = a \<squnion> b"
  unfolding join_abs_state_with_def by (simp add: sup_fun_def)

lemma join_point_with_sup [simp]:
  "join_point_with (join_abs_state_with (\<squnion>)) x
     (y :: 'a::semilattice_sup abs_state lifted) = x \<squnion> y"
  by (cases x; cases y) simp_all

lemma comp_fun_idem_join_lifted:
  "comp_fun_idem
     (\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>))
              (g ctx :: 'a::semilattice_sup abs_state lifted))"
  by unfold_locales (auto simp: sup_left_commute)

text \<open>
  Folding over a context set is the one place code generation needs a concrete
  join, so it is the one place the domain's \<open>\<squnion>\<close> is baked in. A fold parametric
  in an arbitrary join has no executable equation at all: over an unordered set
  the fold's value is only well defined for a commutative idempotent operation,
  and the fold below is where that instance is supplied, once.
\<close>

definition join_states_over ::
  "('ctx \<Rightarrow> 'a::semilattice_sup abs_state lifted) \<Rightarrow> 'ctx set \<Rightarrow>
   'a abs_state lifted" where
  "join_states_over g cs =
     Finite_Set.fold (\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>)) (g ctx))
       Bot cs"

lemma join_states_over_code [code]:
  "join_states_over g (set cs) =
     List.fold (\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>)) (g ctx)) cs Bot"
proof -
  interpret ci: comp_fun_idem
    "\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>)) (g ctx)"
    by (rule comp_fun_idem_join_lifted)
  show ?thesis unfolding join_states_over_def by (rule ci.fold_set_fold)
qed

lemma join_states_over_empty [simp]: "join_states_over g {} = Bot"
  unfolding join_states_over_def by simp

lemma join_states_over_insert [simp]:
  assumes "finite cs"
  shows "join_states_over g (insert ctx cs) = g ctx \<squnion> join_states_over g cs"
proof -
  interpret ci: comp_fun_idem
    "\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>)) (g ctx)"
    by (rule comp_fun_idem_join_lifted)
  show ?thesis unfolding join_states_over_def using assms by simp
qed

text \<open>Every context folded in sits below the result. This is the property that
  makes the join a join, and it is exactly what fails on an infinite carrier:
  \<^const>\<open>Finite_Set.fold\<close> returns its unit there, so an unrestricted key set
  would let a covered, reachable context sit above the node's own joined
  state.\<close>

lemma join_states_over_member_le:
  assumes "finite cs" and "ctx \<in> cs"
  shows "g ctx \<le> join_states_over g cs"
  using assms by (induction cs rule: finite_induct) (auto intro: order_trans sup_ge2)

definition lookup_joined_state ::
  "('ctx, 'a::semilattice_sup abs_state) analysis_result \<Rightarrow> pp \<Rightarrow>
   'a abs_state lifted" where
  "lookup_joined_state r v = join_states_over (lookup_context r v) (contexts_at r v)"

lemma lookup_joined_state_absent [simp]:
  "contexts_at r v = {} \<Longrightarrow> lookup_joined_state r v = Bot"
  unfolding lookup_joined_state_def by simp

subsection \<open>Well-formed results\<close>

text \<open>
  \<^const>\<open>Analysis_Result\<close> is an ordinary constructor, so the two properties the
  opening text describes are not enforced by the type and have to be stated.

  Finiteness is the load-bearing one, and its failure is silent rather than
  loud: \<^const>\<open>join_states_over\<close> folds with \<^const>\<open>Finite_Set.fold\<close>, which
  answers with its unit on an infinite carrier. A node whose key set is
  infinite therefore reports \<^const>\<open>Bot\<close> as its joined state --- reading as
  dead, while \<^const>\<open>node_live_ex\<close>, which never folds, still reports it live.

  Canonicality is what licenses reading \<^const>\<open>Bot\<close> and \<^const>\<open>Lifted\<close> as
  concrete emptiness and non-emptiness rather than as the solver's own
  structural answer. It is stated against a supplied emptiness predicate, the
  same way the normalization operations upstream are, so this layer keeps its
  freedom from any class constraint on the payload.
\<close>

definition finite_analysis_result :: "('ctx, 'a) analysis_result \<Rightarrow> bool" where
  "finite_analysis_result r \<longleftrightarrow> finite (result_keys r)"

definition wf_analysis_result ::
  "('a \<Rightarrow> bool) \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> bool" where
  "wf_analysis_result empty_pred r \<longleftrightarrow>
     finite_analysis_result r
   \<and> (\<forall>v ctx st. lookup_context r v ctx = Lifted st \<longrightarrow> \<not> empty_pred st)"

lemma wf_analysis_result_finite [dest]:
  "wf_analysis_result empty_pred r \<Longrightarrow> finite_analysis_result r"
  unfolding wf_analysis_result_def by simp

lemma wf_analysis_result_LiftedD [dest]:
  "\<lbrakk>wf_analysis_result empty_pred r; lookup_context r v ctx = Lifted st\<rbrakk>
     \<Longrightarrow> \<not> empty_pred st"
  unfolding wf_analysis_result_def by blast

lemma finite_contexts_at:
  assumes "finite_analysis_result r"
  shows "finite (contexts_at r v)"
  using assms unfolding finite_analysis_result_def contexts_at_def by simp

text \<open>What finiteness buys: the per-node view really is an upper bound of the
  contexts it covers.\<close>

lemma lookup_context_le_lookup_joined_state:
  assumes fin: "finite_analysis_result r" and cov: "ctx \<in> contexts_at r v"
  shows "lookup_context r v ctx \<le> lookup_joined_state r v"
  unfolding lookup_joined_state_def
  by (rule join_states_over_member_le[OF finite_contexts_at[OF fin] cov])

text \<open>And what canonicality buys: on a well-formed result the structural
  reading and the concrete one coincide, provided the supplied predicate is
  the exact emptiness test its adapters use.\<close>

lemma wf_analysis_result_gamma_point_eq_empty_iff:
  fixes r :: "('ctx, 'a::sound_domain abs_state) analysis_result"
    and empty_pred :: "'a abs_state \<Rightarrow> bool"
  assumes wf: "wf_analysis_result empty_pred r"
    and exact: "\<And>st. empty_pred st \<longleftrightarrow> \<lbrakk>st\<rbrakk> = {}"
  shows "gamma_point (lookup_context r v ctx) = {} \<longleftrightarrow> lookup_context r v ctx = Bot"
proof (cases "lookup_context r v ctx")
  case Bot
  then show ?thesis by simp
next
  case (Lifted st)
  have "\<not> empty_pred st" using wf Lifted by blast
  with exact Lifted show ?thesis by simp
qed

end

