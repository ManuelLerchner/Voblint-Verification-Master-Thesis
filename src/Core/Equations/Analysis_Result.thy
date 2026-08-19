theory Analysis_Result
  imports Exec_St
begin

section \<open>Solved analysis results\<close>

text \<open>
  The canonical, domain-generic shape of a finished analysis: a finite set of
  covered @{typ "pp \<times> 'ctx"} keys together with a total lookup into a
  per-point abstract state. Checks, reports, and rendering are downstream
  consumers of this table, not siblings of it.

  \<open>Unreachable\<close> means ``the represented concrete state set is empty'',
  i.e. \<open>gamma = {}\<close> --- it does \<^emph>\<open>not\<close> mean ``the solver returned an outer
  \<^const>\<open>Bot\<close>''. Both a solver-level \<^const>\<open>Bot\<close> local unknown \<^emph>\<open>and\<close> a
  \<^const>\<open>Lifted\<close> one whose payload is already componentwise witness-bottom
  normalize to \<open>Unreachable\<close>: the two are indistinguishable in the
  concrete semantics, and \<open>normalize_point_correct\<close> below is exactly the
  statement that this normalization loses nothing --- the normalized
  \<open>point_state\<close> concretizes to the same store set as the raw lifted
  state it came from.
\<close>

subsection \<open>Per-point reachability\<close>

text \<open>
  \<open>point_state\<close> is \<^typ>\<open>'a lifted\<close>'s shape at the result boundary, with the
  reachability reading fixed by \<open>gamma_point\<close> rather than left to the
  caller. It is a separate type, not a reuse of \<^typ>\<open>'a lifted\<close>, so that a
  result-level \<open>Unreachable\<close> cannot be confused with the solver-level
  \<^const>\<open>Bot\<close> it may or may not have come from. The order, \<^const>\<open>bot\<close>, and
  \<^const>\<open>sup\<close> instances mirror \<^typ>\<open>'a lifted\<close>'s own: \<open>Unreachable\<close>
  is least and neutral for \<^const>\<open>sup\<close>, and two reachable points join
  payloadwise. The \<open>quickcheck_narrowing\<close> plugin is disabled for the same
  reason it is on \<^typ>\<open>'a lifted\<close>: the vendored solver's \<open>narrowing\<close> class
  collides with Quickcheck's arity of the same base name.
\<close>

datatype (plugins del: quickcheck_narrowing) 'a point_state =
  Unreachable | Reachable 'a

instantiation point_state :: (order) order
begin

fun less_eq_point_state :: "'a point_state \<Rightarrow> 'a point_state \<Rightarrow> bool" where
  "less_eq_point_state Unreachable _ = True"
| "less_eq_point_state (Reachable _) Unreachable = False"
| "less_eq_point_state (Reachable a) (Reachable b) = (a \<le> b)"

definition less_point_state :: "'a point_state \<Rightarrow> 'a point_state \<Rightarrow> bool" where
  "less_point_state x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a point_state"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_point_state_def by (rule refl)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) simp_all
qed

end

instantiation point_state :: (type) bot
begin
definition bot_point_state :: "'a point_state" where "bot_point_state = Unreachable"
instance ..
end

lemma bot_point_state_eq [simp]: "(bot :: 'a point_state) = Unreachable"
  unfolding bot_point_state_def by (rule refl)

instance point_state :: (order) order_bot
  by standard (simp add: bot_point_state_def)

instantiation point_state :: (semilattice_sup) semilattice_sup
begin

fun sup_point_state :: "'a point_state \<Rightarrow> 'a point_state \<Rightarrow> 'a point_state" where
  "sup_point_state Unreachable y = y"
| "sup_point_state x Unreachable = x"
| "sup_point_state (Reachable a) (Reachable b) = Reachable (a \<squnion> b)"

instance
proof
  fix x y z :: "'a point_state"
  show "x \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" by (cases x; cases y; cases z) simp_all
qed

end

text \<open>
  Reachability is read off the constructor, never by comparing against
  \<^const>\<open>Unreachable\<close> with \<open>=\<close>: an equality test would force an \<open>equal\<close>
  instance on the payload, which nothing else about the result table needs.
  The datatype's own \<^const>\<open>map_point_state\<close> is the functorial map (payload
  rewriting that leaves reachability alone); it is generated with the
  datatype, so no separate definition restates it.
\<close>

fun is_reachable_point :: "'a point_state \<Rightarrow> bool" where
  "is_reachable_point Unreachable = False"
| "is_reachable_point (Reachable _) = True"

lemma is_reachable_point_iff: "is_reachable_point p \<longleftrightarrow> p \<noteq> Unreachable"
  by (cases p) simp_all

definition gamma_point :: "'a::sound_domain abs_state point_state \<Rightarrow> store set" where
  "gamma_point p = (case p of Unreachable \<Rightarrow> {} | Reachable st \<Rightarrow> gamma_state st)"

lemma gamma_point_Unreachable [simp]: "gamma_point Unreachable = {}"
  unfolding gamma_point_def by simp

lemma gamma_point_Reachable [simp]: "gamma_point (Reachable st) = gamma_state st"
  unfolding gamma_point_def by simp

subsection \<open>Normalizing a solved local unknown\<close>

text \<open>
  \<open>normalize_point\<close> is the sole entry point from the executable solver
  substrate into the result boundary: it takes the local unknown exactly as
  the solver stores it (an \<^typ>\<open>'a resolved_st_q lifted\<close>) and decides
  reachability with \<^const>\<open>resolved_st_q_is_bot_for\<close>, the executable
  witness-bottom test, rather than with the outer \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close>
  constructor alone. Its two arguments are the declared globals in both
  shapes the substrate uses --- as a list for the executable test, as a
  predicate for \<^const>\<open>fun_of_resolved_st_q_for\<close>'s location split.

  It is constrained at \<^class>\<open>computable_domain\<close>, not \<^class>\<open>sound_domain\<close>:
  the stronger class carries \<^const>\<open>gamma\<close>, and code generation would then
  have to materialize a dictionary field for a constant with no code
  equation. \<open>normalize_point_correct\<close> below states the soundness at
  \<^class>\<open>sound_domain\<close>, where \<^const>\<open>gamma\<close> is available, without the
  executable definition ever depending on it.
\<close>

fun normalize_point ::
  "vname list \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> ('a::computable_domain) resolved_st_q lifted \<Rightarrow>
   'a abs_state point_state"
where
  "normalize_point gl gs Bot = Unreachable"
| "normalize_point gl gs (Lifted s) =
     (if resolved_st_q_is_bot_for gl s then Unreachable
      else Reachable (fun_of_resolved_st_q_for gs s))"

text \<open>
  Normalization is exact, not merely sound: the concretization of the
  normalized point is the concretization of the raw lifted state it came
  from. Composing \<open>resolved_st_q_lifted_is_bot_for_iff\<close> (the executable
  witness-bottom test agrees with \<^const>\<open>is_bot_state_lift\<close>) with
  \<open>is_bot_state_lift_iff\<close> (\<^const>\<open>is_bot_state_lift\<close> agrees with emptiness of
  \<^const>\<open>gamma_state_lift\<close>), both from \<^theory>\<open>Voblint_Core.Exec_St\<close> and
  \<^theory>\<open>Voblint_Core.Abstract_Domain\<close>, is all it takes: collapsing a
  witness-bottom \<^const>\<open>Lifted\<close> state to \<^const>\<open>Unreachable\<close> discards no
  concrete store, because there was none.
\<close>

lemma normalize_point_correct:
  assumes globals: "\<And>x. gs x = (x \<in> set gl)"
  shows "gamma_point (normalize_point gl gs s) =
         gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) s)"
proof (cases s)
  case Bot
  then show ?thesis by simp
next
  case (Lifted t)
  show ?thesis
  proof (cases "resolved_st_q_lifted_is_bot_for gl s")
    case True
    then have "is_bot_state_lift (map_lift (fun_of_resolved_st_q_for gs) s)"
      by (simp add: resolved_st_q_lifted_is_bot_for_iff[OF globals])
    then have empty: "gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) s) = {}"
      by (simp add: is_bot_state_lift_iff)
    from True Lifted have "normalize_point gl gs s = Unreachable" by simp
    with empty show ?thesis by simp
  next
    case False
    with Lifted show ?thesis by simp
  qed
qed

text \<open>
  The other direction of the same normalization, in the shape a consumer of a
  \<^const>\<open>Reachable\<close> point needs: the payload it hands out is literally the
  reader's image of the solved local unknown, so a fact proved about the raw
  lifted state transports to the normalized one without re-deciding
  reachability. \<^const>\<open>Unreachable\<close> carries no payload and so has no such
  transport --- which is exactly why it is the caller's job to case-split
  before using a normalized state.
\<close>

lemma normalize_point_Reachable_map_lift:
  assumes "normalize_point gl gs s = Reachable st"
  shows "map_lift (fun_of_resolved_st_q_for gs) s = Lifted st"
  using assms by (cases s) (auto split: if_splits)

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
    (result_at: "pp \<Rightarrow> 'ctx \<Rightarrow> 'a point_state")

definition contexts_at :: "('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> 'ctx set" where
  "contexts_at r v = snd ` Set.filter (\<lambda>(v', ctx). v' = v) (result_keys r)"

definition lookup_context ::
  "('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> 'ctx \<Rightarrow> 'a point_state" where
  "lookup_context r v ctx =
     (if (v, ctx) \<in> result_keys r then result_at r v ctx else Unreachable)"

lemma contexts_at_iff [simp]: "ctx \<in> contexts_at r v \<longleftrightarrow> (v, ctx) \<in> result_keys r"
  unfolding contexts_at_def by force

lemma lookup_context_absent [simp]:
  "(v, ctx) \<notin> result_keys r \<Longrightarrow> lookup_context r v ctx = Unreachable"
  unfolding lookup_context_def by simp

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

  \<^const>\<open>Unreachable\<close> is the fold's unit, so the empty-context case needs no
  separate guard: a node the solver never covered folds to \<^const>\<open>Unreachable\<close>
  on its own.
\<close>

fun join_point_with ::
  "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a point_state \<Rightarrow> 'a point_state \<Rightarrow> 'a point_state"
where
  "join_point_with j Unreachable y = y"
| "join_point_with j x Unreachable = x"
| "join_point_with j (Reachable a) (Reachable b) = Reachable (j a b)"

definition join_abs_state_with ::
  "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "join_abs_state_with j a b = (\<lambda>x. j (a x) (b x))"

definition lookup_joined_with ::
  "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> pp \<Rightarrow> 'a point_state" where
  "lookup_joined_with j r v =
     Finite_Set.fold (\<lambda>ctx. join_point_with j (lookup_context r v ctx)) Unreachable
       (contexts_at r v)"

lemma lookup_joined_with_absent [simp]:
  "contexts_at r v = {} \<Longrightarrow> lookup_joined_with j r v = Unreachable"
  unfolding lookup_joined_with_def by simp

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
     (y :: 'a::semilattice_sup abs_state point_state) = x \<squnion> y"
  by (cases x; cases y) simp_all

lemma comp_fun_idem_join_point_state:
  "comp_fun_idem
     (\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>))
              (g ctx :: 'a::semilattice_sup abs_state point_state))"
  by unfold_locales (auto simp: sup_left_commute)

text \<open>
  Folding over a context set is the one place code generation needs a concrete
  join, so it is the one place the domain's \<open>\<squnion>\<close> is baked in. A fold parametric
  in an arbitrary join has no executable equation at all: over an unordered set
  the fold's value is only well defined for a commutative idempotent operation,
  and the fold below is where that instance is supplied, once.
\<close>

definition join_states_over ::
  "('ctx \<Rightarrow> 'a::semilattice_sup abs_state point_state) \<Rightarrow> 'ctx set \<Rightarrow>
   'a abs_state point_state" where
  "join_states_over g cs =
     Finite_Set.fold (\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>)) (g ctx))
       Unreachable cs"

declare join_states_over_def [code del]

lemma join_states_over_code [code]:
  "join_states_over g (set cs) =
     List.fold (\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>)) (g ctx)) cs Unreachable"
proof -
  interpret ci: comp_fun_idem
    "\<lambda>ctx. join_point_with (join_abs_state_with (\<squnion>)) (g ctx)"
    by (rule comp_fun_idem_join_point_state)
  show ?thesis unfolding join_states_over_def by (rule ci.fold_set_fold)
qed

definition lookup_joined_state ::
  "('ctx, 'a::semilattice_sup abs_state) analysis_result \<Rightarrow> pp \<Rightarrow>
   'a abs_state point_state" where
  "lookup_joined_state r v = join_states_over (lookup_context r v) (contexts_at r v)"

lemma lookup_joined_state_eq_with:
  "lookup_joined_state r v = lookup_joined_with (join_abs_state_with (\<squnion>)) r v"
  unfolding lookup_joined_state_def join_states_over_def lookup_joined_with_def
  by (rule refl)

lemma lookup_joined_state_absent [simp]:
  "contexts_at r v = {} \<Longrightarrow> lookup_joined_state r v = Unreachable"
  unfolding lookup_joined_state_def join_states_over_def by simp

end
