theory Solved_Table
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
  \<open>wf_solved_table\<close>, stated at the end of this theory. Its two halves are
  not established alike: an adapter canonicalizes every payload it publishes,
  so canonicality is unconditional, while finiteness holds only for those
  context policies whose whole context space is bounded in advance, and is
  carried as a hypothesis everywhere else.

  \<^const>\<open>Bot\<close> means ``the solver's canonical result at this key is an
  outer \<^const>\<open>Bot\<close>'', or the key is absent from \<open>covered_keys\<close> altogether;
  \<open>Lifted a\<close> means ``the canonical result is \<^const>\<open>Lifted\<close>'', with the
  local unknown projected to the abstract state \<open>a\<close>. This is a structural
  reading, not a semantic-emptiness test: raw solver values are
  canonicalized -- a witness-bottom \<^const>\<open>Lifted\<close> payload collapsed to
  \<^const>\<open>Bot\<close> -- \<^emph>\<open>before\<close> they reach this boundary (every public result
  adapter routes through \<open>canonicalize_lift\<close>), so by the time a value
  reaches \<open>lookup_table\<close> here, \<^const>\<open>Bot\<close> denotes no store. The converse
  does not hold: the emptiness test is sound and need not be complete, so a
  \<^const>\<open>Lifted\<close> state may still denote no store (a product whose interval
  field says \<open>x = 2\<close> and whose parity field says \<open>x\<close> is odd stays
  \<^const>\<open>Lifted\<close>).
\<close>

subsection \<open>Per-point reachability\<close>

text \<open>
  Per-point reachability is \<^typ>\<open>'a lifted\<close> itself
  (\<^theory>\<open>Voblint_Domain.Reachability_Lift\<close>), not a nominal copy of it: the
  reachability reading is fixed below rather than
  left to the caller, and stated directly in terms of \<^const>\<open>Bot\<close>/
  \<^const>\<open>Lifted\<close>. \<^const>\<open>map_lift\<close> is the functorial map (payload
  rewriting that leaves reachability alone).
\<close>

text \<open>
  A point of an abstract-store table concretizes through the reachability
  lift: \<^const>\<open>Bot\<close> to nothing, a \<^const>\<open>Lifted\<close> store to its concretization.
  It is the lift at \<^const>\<open>gamma_state\<close>, so a result generic in its published
  value reads back to exactly this at an abstract-store instance.
\<close>

lemma gamma_state_of_reachable_env [simp]:
  "\<lbrakk>case p of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk> = \<lbrakk>p\<rbrakk>\<^sub>\<bottom>"
  for p :: "'a::numeric_domain abs_state lifted"
  by (cases p) simp_all

subsection \<open>The result table\<close>

text \<open>
  \<open>covered_keys\<close> is the authoritative coverage surface --- the keys the
  solver actually reached --- while \<open>table_at\<close> is merely a total
  lookup function, defined everywhere but meaningful only on the key set.
  \<open>lookup_table\<close> keeps that distinction explicit rather than trusting
  \<open>table_at\<close> to answer sensibly off the key set.

  \<^typ>\<open>'ctx\<close> carries no ordering or enumeration constraint: real context
  types include interval-vector and call-string contexts, which have
  neither.
\<close>

datatype (plugins del: quickcheck_narrowing) ('ctx, 'a) solved_table =
  Solved_Table
    (covered_keys: "(pp \<times> 'ctx) set")
    (table_at: "pp \<Rightarrow> 'ctx \<Rightarrow> 'a lifted")

definition table_contexts :: "('ctx, 'a) solved_table \<Rightarrow> pp \<Rightarrow> 'ctx set" where
  "table_contexts r v = snd ` Set.filter (\<lambda>(v', ctx). v' = v) (covered_keys r)"

definition lookup_table ::
  "('ctx, 'a) solved_table \<Rightarrow> pp \<Rightarrow> 'ctx \<Rightarrow> 'a lifted" where
  "lookup_table r v ctx =
     (if (v, ctx) \<in> covered_keys r then table_at r v ctx else Bot)"

lemma table_contexts_iff [simp]: "ctx \<in> table_contexts r v \<longleftrightarrow> (v, ctx) \<in> covered_keys r"
  unfolding table_contexts_def by force

lemma lookup_table_absent [simp]:
  "(v, ctx) \<notin> covered_keys r \<Longrightarrow> lookup_table r v ctx = Bot"
  unfolding lookup_table_def by simp

subsection \<open>Telling ``analysed and dead'' from ``never analysed''\<close>

text \<open>
  \<^const>\<open>lookup_table\<close> answers \<^const>\<open>Bot\<close> for two unrelated reasons: the
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

definition lookup_coverage ::
  "('ctx, 'a) solved_table \<Rightarrow> pp \<Rightarrow> 'ctx \<Rightarrow> 'a context_result" where
  "lookup_coverage r v ctx =
     (if (v, ctx) \<in> covered_keys r then Covered (table_at r v ctx) else Uncovered)"

lemma lookup_coverage_covered [simp]:
  "(v, ctx) \<in> covered_keys r \<Longrightarrow>
     lookup_coverage r v ctx = Covered (table_at r v ctx)"
  unfolding lookup_coverage_def by simp

lemma lookup_coverage_uncovered [simp]:
  "(v, ctx) \<notin> covered_keys r \<Longrightarrow> lookup_coverage r v ctx = Uncovered"
  unfolding lookup_coverage_def by simp

lemma lookup_coverage_eq_Uncovered_iff:
  "lookup_coverage r v ctx = Uncovered \<longleftrightarrow> (v, ctx) \<notin> covered_keys r"
  unfolding lookup_coverage_def by simp

lemma lookup_coverage_eq_Covered_iff:
  "lookup_coverage r v ctx = Covered x \<longleftrightarrow>
     (v, ctx) \<in> covered_keys r \<and> table_at r v ctx = x"
  unfolding lookup_coverage_def by auto

text \<open>
  Where the information is lost, named so that losing it is a visible step.
  \<^const>\<open>lookup_table\<close> is exactly this totalization, which is why it is safe
  to keep for callers that only ever read a covered key -- and why a soundness
  claim may not be stated over it directly.
\<close>

fun context_result_or_bot :: "'a context_result \<Rightarrow> 'a lifted" where
  "context_result_or_bot Uncovered = Bot"
| "context_result_or_bot (Covered x) = x"

lemma lookup_table_eq_or_bot:
  "lookup_table r v ctx =
     context_result_or_bot (lookup_coverage r v ctx)"
  unfolding lookup_table_def lookup_coverage_def by simp

text \<open>
  The logical core of every ``the reported point is unreachable'' claim, stated
  once here rather than per domain. It starts from \<^term>\<open>Covered Bot\<close>, so an
  uncovered node cannot satisfy it however the caller obtained its inclusion.
\<close>

lemma reported_covered_unreachable_empty:
  assumes lookup: "lookup_coverage r v ctx = Covered Bot"
    and sound: "C \<subseteq> gamma_lift gam (lookup_table r v ctx)"
  shows "C = {}"
  using sound unfolding lookup_table_eq_or_bot lookup by simp

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
  "('ctx, 'a) solved_table \<Rightarrow> pp \<Rightarrow> bool" where
  "result_node_is_bottom r v \<longleftrightarrow>
     (\<forall>ctx a. lookup_coverage r v ctx = Covered a \<longrightarrow> a = Bot)"

lemma result_node_is_bottomI:
  assumes "\<And>ctx a. lookup_coverage r v ctx = Covered a \<Longrightarrow> a = Bot"
  shows "result_node_is_bottom r v"
  unfolding result_node_is_bottom_def using assms by blast

lemma result_node_is_bottomD:
  assumes bot: "result_node_is_bottom r v"
    and covered: "(v, ctx) \<in> covered_keys r"
  shows "lookup_coverage r v ctx = Covered Bot"
proof -
  have eq: "lookup_coverage r v ctx = Covered (table_at r v ctx)"
    using covered by simp
  have "table_at r v ctx = Bot"
    using bot eq unfolding result_node_is_bottom_def by blast
  with eq show ?thesis by simp
qed

lemma lookup_table_LiftedD [dest]:
  "lookup_table r v ctx = Lifted st \<Longrightarrow> ctx \<in> table_contexts r v"
  using lookup_table_absent by fastforce

subsection \<open>Well-formed results\<close>

text \<open>
  \<^const>\<open>Solved_Table\<close> is an ordinary constructor, so the two properties the
  opening text describes are not enforced by the type and have to be stated.

  Finiteness is the load-bearing one, and its failure is silent rather than
  loud: a per-node aggregate over \<^const>\<open>table_contexts\<close> folds with
  \<^const>\<open>Finite_Set.fold\<close>, which answers with its unit on an infinite carrier.
  The contextual check report's verdict aggregate is one such fold: over an
  infinite key set it reports a check dead whatever its contexts say.

  Canonicality is what licenses reading \<^const>\<open>Bot\<close> as concrete emptiness
  rather than as the solver's own structural answer. \<^const>\<open>Lifted\<close> gets no
  such reading: the supplied emptiness predicate is sound, not complete. It is stated against a supplied emptiness predicate, the
  same way the normalization operations upstream are, so this layer keeps its
  freedom from any class constraint on the payload.
\<close>

definition finite_solved_table :: "('ctx, 'a) solved_table \<Rightarrow> bool" where
  "finite_solved_table r \<longleftrightarrow> finite (covered_keys r)"

definition wf_solved_table ::
  "('a \<Rightarrow> bool) \<Rightarrow> ('ctx, 'a) solved_table \<Rightarrow> bool" where
  "wf_solved_table empty_pred r \<longleftrightarrow>
     finite_solved_table r
   \<and> (\<forall>v ctx st. lookup_table r v ctx = Lifted st \<longrightarrow> \<not> empty_pred st)"

lemma wf_solved_table_finite [dest]:
  "wf_solved_table empty_pred r \<Longrightarrow> finite_solved_table r"
  unfolding wf_solved_table_def by simp

lemma wf_solved_table_LiftedD [dest]:
  "\<lbrakk>wf_solved_table empty_pred r; lookup_table r v ctx = Lifted st\<rbrakk>
     \<Longrightarrow> \<not> empty_pred st"
  unfolding wf_solved_table_def by blast

lemma finite_table_contexts:
  assumes "finite_solved_table r"
  shows "finite (table_contexts r v)"
  using assms unfolding finite_solved_table_def table_contexts_def by simp

text \<open>What canonicality buys: on a well-formed result the structural
  reading and the concrete one coincide, provided the supplied predicate is
  the exact emptiness test its adapters use.\<close>

lemma wf_solved_table_gamma_point_eq_empty_iff:
  fixes r :: "('ctx, 'a::numeric_domain abs_state) solved_table"
    and empty_pred :: "'a abs_state \<Rightarrow> bool"
  assumes wf: "wf_solved_table empty_pred r"
    and exact: "\<And>st. empty_pred st \<longleftrightarrow> \<lbrakk>st\<rbrakk> = {}"
  shows "\<lbrakk>lookup_table r v ctx\<rbrakk>\<^sub>\<bottom> = {} \<longleftrightarrow> lookup_table r v ctx = Bot"
proof (cases "lookup_table r v ctx")
  case Bot
  then show ?thesis by simp
next
  case (Lifted st)
  have "\<not> empty_pred st" using wf Lifted by blast
  with exact Lifted show ?thesis by simp
qed

end
