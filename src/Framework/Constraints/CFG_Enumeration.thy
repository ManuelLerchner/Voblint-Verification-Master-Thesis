theory CFG_Enumeration
  imports "Voblint_CFG.CFG_Def" "Voblint_VIMP.VIMP_Proc"
begin

section \<open>Solver-facing CFG enumeration\<close>

text \<open>
  Backward predecessor relations and deterministic edge enumeration over a compiled
  two-relation CFG.  These are the equation-generation and code-generation views the TD
  solver reads to build and evaluate the constraint system; they are not part of the
  concrete CFG semantics --- \<open>valid_ltr\<close> never refers to them.  Ordinary control flow is
  enumerated over \<^const>\<open>intra\<close>; procedure calls --- entry routing and return combining ---
  over \<^const>\<open>calls\<close>.  There is no unified edge set and no separate combine relation: a
  return is recovered from the same \<^const>\<open>calls\<close> tuple that created the activation.

  Every enumeration appears twice: as a set, which the proofs reason over, and as a list,
  which code generation and the solver's folds consume, identified by a \<open>set_..._list\<close>
  lemma whenever the edge set is finite.  On the return side there is one of each ---
  the set \<open>call_targets\<close> and the list \<open>call_target_list\<close> --- and every other return view
  is an image or a \<open>map\<close> of those, so the views cannot come to disagree about which edges
  they enumerate.
\<close>

subsection \<open>Intra predecessors\<close>

text \<open>The ordinary incoming transitions of a node: an intra edge is a total store
  transformer within one activation, so this is the transfer fold the equation system runs
  at every node --- including the \<^term>\<open>EA_Ret e p\<close> edges into \<^term>\<open>FunctionResult p\<close>, by
  which return values are summarised as ordinary predecessor folding.\<close>

definition intra_predecessors :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> edge_action) set" where
  "intra_predecessors g v = {(u, a). (u, a, v) \<in> intra g}"

lemma intra_predecessors_iff [simp]:
  "(u, a) \<in> intra_predecessors g v \<longleftrightarrow> (u, a, v) \<in> intra g"
  by (simp add: intra_predecessors_def)

lemma finite_intra_predecessors [intro]:
  assumes "finite (intra g)"
  shows "finite (intra_predecessors g v)"
proof -
  have "intra_predecessors g v
          \<subseteq> (\<lambda>e :: cfg_node \<times> edge_action \<times> cfg_node. (fst e, fst (snd e))) ` intra g"
    unfolding intra_predecessors_def by force
  then show ?thesis using assms finite_subset finite_imageI by blast
qed

definition intra_predecessor_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> edge_action) list" where
  "intra_predecessor_list g v =
     map (\<lambda>(u, a, w). (u, a)) (filter (\<lambda>(u, a, w). w = v) (cfg_intra_list g))"

lemma set_intra_predecessor_list [simp]:
  assumes "finite (intra g)"
  shows "set (intra_predecessor_list g v) = intra_predecessors g v"
  unfolding intra_predecessor_list_def intra_predecessors_def
  using set_cfg_intra_list[OF assms] by (force simp: image_iff)

subsection \<open>Call-entry enumeration\<close>

text \<open>The call tuples whose callee entry is the queried node \<open>v\<close> (a \<^term>\<open>FunctionEntry p\<close>).
  The continuation does not affect the callee-entry state, so it is projected away; the
  entry contribution is the caller state routed through the call action's parameter
  binding, which is what an analysis's entry operation computes.\<close>

definition entry_calls :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action) set" where
  "entry_calls g v = {(c, ca). \<exists>k. (c, ca, v, k) \<in> calls g}"

lemma entry_calls_iff [simp]:
  "(c, ca) \<in> entry_calls g v \<longleftrightarrow> (\<exists>k. (c, ca, v, k) \<in> calls g)"
  by (simp add: entry_calls_def)

lemma finite_entry_calls [intro]:
  assumes "finite (calls g)"
  shows "finite (entry_calls g v)"
proof -
  have "entry_calls g v
          \<subseteq> (\<lambda>e :: cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node. (fst e, fst (snd e))) ` calls g"
    unfolding entry_calls_def by force
  then show ?thesis using assms finite_subset finite_imageI by blast
qed

definition entry_call_list :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action) list" where
  "entry_call_list g v =
     map (\<lambda>(c, ca, ce, k). (c, ca)) (filter (\<lambda>(c, ca, ce, k). ce = v) (cfg_calls_list g))"

lemma set_entry_call_list [simp]:
  assumes "finite (calls g)"
  shows "set (entry_call_list g v) = entry_calls g v"
  unfolding entry_call_list_def entry_calls_def
  using set_cfg_calls_list[OF assms] by (force simp: image_iff)

subsection \<open>Outgoing call enumeration (caller perspective)\<close>

text \<open>The call tuples whose call site is the queried node \<open>v\<close>: the entry, action, and
  continuation of every call \<open>v\<close> makes. This is the caller-side counterpart of
  \<^const>\<open>entry_calls\<close> (callee-indexed) --- routing a call-entry seed publication at its call
  site needs the callee entry and the whole \<^typ>\<open>call_action\<close> together, which the
  continuation-indexed enumerations below do not expose.\<close>

definition call_successors ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) set" where
  "call_successors g v = {(ce, ca, k). (v, ca, ce, k) \<in> calls g}"

lemma call_successors_iff [simp]:
  "(ce, ca, k) \<in> call_successors g v \<longleftrightarrow> (v, ca, ce, k) \<in> calls g"
  by (simp add: call_successors_def)

lemma finite_call_successors [intro]:
  assumes "finite (calls g)"
  shows "finite (call_successors g v)"
proof -
  have "call_successors g v
          \<subseteq> (\<lambda>(c, ca, ce, k). (ce, ca, k)) ` calls g"
    unfolding call_successors_def by force
  then show ?thesis using assms finite_subset finite_imageI by blast
qed

definition call_successor_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) list" where
  "call_successor_list g v =
     map (\<lambda>(c, ca, ce, k). (ce, ca, k)) (filter (\<lambda>(c, ca, ce, k). c = v) (cfg_calls_list g))"

lemma set_call_successor_list [simp]:
  assumes "finite (calls g)"
  shows "set (call_successor_list g v) = call_successors g v"
  unfolding call_successor_list_def call_successors_def
  using set_cfg_calls_list[OF assms] by (force simp: image_iff)


subsection \<open>Call targets at a continuation\<close>

text \<open>
  The call edges whose continuation is \<open>v\<close>, each paired with the procedure its callee entry
  names.  This is the one continuation-indexed enumeration that reads \<^const>\<open>calls\<close>
  directly; every return-side view below is an image or a map of it.

  \<open>call_target_at\<close> decodes a single call edge, selecting on the continuation and reading the
  callee's procedure off \<^term>\<open>FunctionEntry p\<close> in one total function, so there is no
  unreachable-but-present branch and no later definition has to re-establish that the node
  it is looking at really is a callee entry.

  Naming the callee by its procedure rather than by the \<^term>\<open>FunctionResult p\<close> node its
  result is read at keeps the call site's own data --- where the call is, what it passes,
  where it returns to --- separate from the callee, which is what lets a resolver choose
  among candidates rather than read a callee the enumeration already fixed.  The result
  node is then \<open>FunctionResult p\<close> at the point of use.
\<close>

definition call_targets ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> pname) set" where
  "call_targets g v = {(c, ca, p). (c, ca, FunctionEntry p, v) \<in> calls g}"

lemma call_targets_iff [simp]:
  "(c, ca, p) \<in> call_targets g v \<longleftrightarrow> (c, ca, FunctionEntry p, v) \<in> calls g"
  by (simp add: call_targets_def)

fun call_target_at ::
    "cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node)
       \<Rightarrow> (cfg_node \<times> call_action \<times> pname) option" where
  "call_target_at v (c, ca, FunctionEntry p, k) =
     (if k = v then Some (c, ca, p) else None)"
| "call_target_at v _ = None"

definition call_target_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> pname) list" where
  "call_target_list g v = List.map_filter (call_target_at v) (cfg_calls_list g)"

lemma set_map_filter_call_target_at:
  "set (List.map_filter (call_target_at v) es)
     = {(c, ca, p). (c, ca, FunctionEntry p, v) \<in> set es}"
proof (induction es)
  case Nil
  show ?case by simp
next
  case (Cons e es)
  obtain c ca ce k where e: "e = (c, ca, ce, k)" by (cases e) auto
  show ?case by (cases ce) (auto simp: e Cons.IH)
qed

text \<open>Membership, in the form a call-site obligation states it: the enumeration lists
  exactly the call edges of \<open>g\<close> whose continuation is \<open>v\<close>, each paired with the
  procedure its callee entry names.\<close>

lemma set_call_target_list [simp]:
  assumes "finite (calls g)"
  shows "set (call_target_list g v) = call_targets g v"
  unfolding call_target_list_def call_targets_def
  by (simp add: set_map_filter_call_target_at set_cfg_calls_list[OF assms])

lemma finite_call_targets [intro]:
  assumes "finite (calls g)"
  shows "finite (call_targets g v)"
proof -
  have "call_targets g v = set (call_target_list g v)"
    using set_call_target_list[OF assms] by simp
  then show ?thesis by simp
qed

text \<open>The enumeration lists each call edge once: \<^const>\<open>cfg_calls_list\<close> is duplicate-free
  and \<^const>\<open>call_target_at\<close> discards exactly the components a decoded entry does not
  determine.  This is what makes the site and target lists below duplicate-free too, so
  the generator builds one contribution per site-target pair rather than one per pair of
  co-listed callees.\<close>

lemma distinct_map_filter_call_target_at:
  assumes "distinct es"
  shows "distinct (List.map_filter (call_target_at v) es)"
  using assms
proof (induction es)
  case Nil
  show ?case by simp
next
  case (Cons e es)
  obtain c ca ce k where e: "e = (c, ca, ce, k)" by (cases e) auto
  show ?case
    using Cons by (cases ce) (auto simp: e set_map_filter_call_target_at)
qed

lemma distinct_call_target_list [simp]:
  assumes "finite (calls g)"
  shows "distinct (call_target_list g v)"
  unfolding call_target_list_def
  by (rule distinct_map_filter_call_target_at) (simp add: cfg_calls_list_def assms)

lemma call_target_list_iff:
  assumes "finite (calls g)"
  shows "(c, ca, p) \<in> set (call_target_list g v)
           \<longleftrightarrow> (c, ca, FunctionEntry p, v) \<in> calls g"
  by (simp add: set_call_target_list[OF assms])


subsection \<open>Return enumeration\<close>

text \<open>Two views of the same return edges, both images of \<^const>\<open>call_targets\<close>: one keeping
  the triggering \<^typ>\<open>call_action\<close> whole, one replacing it with the call's
  \<^typ>\<open>call_info\<close>.  The return contribution is the caller state and the callee-exit state
  assembled by \<open>combine\<^sup>#\<close>.  Both hand back the callee's \<^term>\<open>FunctionResult p\<close> node
  directly --- recovered from the callee entry \<^term>\<open>FunctionEntry p\<close>, so no separate
  combine relation is needed and no client has to rebuild the result node.\<close>

definition return_call_actions ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) set" where
  "return_call_actions g v =
     (\<lambda>(c, ca, p). (c, ca, FunctionResult p)) ` call_targets g v"

lemma return_call_actions_iff [simp]:
  "(c, ca, r) \<in> return_call_actions g v
     \<longleftrightarrow> (\<exists>p. r = FunctionResult p \<and> (c, ca, FunctionEntry p, v) \<in> calls g)"
  by (auto simp: return_call_actions_def image_iff Bex_def)

lemma finite_return_call_actions [intro]:
  assumes "finite (calls g)"
  shows "finite (return_call_actions g v)"
  using finite_call_targets[OF assms] by (simp add: return_call_actions_def)

definition return_call_action_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) list" where
  "return_call_action_list g v =
     map (\<lambda>(c, ca, p). (c, ca, FunctionResult p)) (call_target_list g v)"

lemma set_return_call_action_list [simp]:
  assumes "finite (calls g)"
  shows "set (return_call_action_list g v) = return_call_actions g v"
  unfolding return_call_action_list_def return_call_actions_def
  by (simp add: set_call_target_list[OF assms])

text \<open>The packaged view carries the call's own \<^typ>\<open>call_info\<close> --- callee, formals and
  actual arguments --- rather than a bare destination, because that is what an
  interprocedural transfer sees at the return point, matching what Goblint's
  \<open>combine_env\<close>/\<open>combine_assign\<close> receive.  The enumeration is the only layer holding the
  \<^const>\<open>calls\<close> relation, so the metadata is projected here; a combine tree never sees the
  CFG, and \<^const>\<open>wf_cfg\<close> does not force a call site's outgoing call edge to be unique, so
  there is no well-defined downstream lookup that could recover it instead.

  The flat, context-insensitive combine (\<open>combine_collect_abs\<close>, \<open>combine\<^sup>#\<close>) needs no more
  than this.  The context-sensitive DG generator uses \<^const>\<open>return_call_action_list\<close>
  instead, because it must route the callee-entry seed publication and the return-side
  context read from the \<^emph>\<open>same\<close> call action, exactly as \<^const>\<open>entry_call_list\<close> keeps \<open>ca\<close>
  whole on the entry side.\<close>

definition return_calls ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_info \<times> cfg_node) set" where
  "return_calls g v =
     (\<lambda>(c, ca, p). (c, call_info_of ca p, FunctionResult p)) ` call_targets g v"

lemma return_calls_iff [simp]:
  "(c, ci, r) \<in> return_calls g v
     \<longleftrightarrow> (\<exists>ca p. r = FunctionResult p \<and> ci = call_info_of ca p
             \<and> (c, ca, FunctionEntry p, v) \<in> calls g)"
  by (auto simp: return_calls_def image_iff Bex_def)

lemma finite_return_calls [intro]:
  assumes "finite (calls g)"
  shows "finite (return_calls g v)"
  using finite_call_targets[OF assms] by (simp add: return_calls_def)

definition return_call_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_info \<times> cfg_node) list" where
  "return_call_list g v =
     map (\<lambda>(c, ca, p). (c, call_info_of ca p, FunctionResult p)) (call_target_list g v)"

lemma set_return_call_list [simp]:
  assumes "finite (calls g)"
  shows "set (return_call_list g v) = return_calls g v"
  unfolding return_call_list_def return_calls_def
  by (simp add: set_call_target_list[OF assms])

text \<open>The three lists carry the same call sites in the same order; only the callee's
  spelling differs.  This is what justifies calling them return enumerations for the same
  edge rather than unrelated relations --- and, since two of them are maps over the third,
  it holds by construction and cannot lapse.\<close>

lemma return_call_action_list_eq_call_target_list:
  "return_call_action_list g v
     = map (\<lambda>(c, ca, p). (c, ca, FunctionResult p)) (call_target_list g v)"
  by (simp add: return_call_action_list_def)

subsection \<open>Call sites and the resolver adapter\<close>

text \<open>
  The call site alone, with no callee: what a call-site-owned resolver is given.  The list
  is duplicate-free, so a site with several statically known callees is listed once; with
  \<open>distinct_static_targets\<close> below, resolving every listed site therefore visits each
  site-target pair exactly once.

  \<open>static_targets\<close> below is the resolver that answers from the CFG and ignores the caller's
  abstract state --- the behaviour a statically enumerated generator already has.  A
  resolver reading that state instead is what makes an indirect call expressible, and the
  shape of the equation does not change when it does.  Two limits are worth stating,
  because the resolver type \<open>cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> call_action \<Rightarrow> 'd \<Rightarrow> pname list\<close>
  does not: a resolver may answer with any procedures at all, so a sound instance needs an
  explicit coverage assumption relating its answer to the concrete callees reachable at the
  site; and the sites themselves come from \<^const>\<open>call_target_list\<close>, so a call with no
  statically enumerated target is not listed and no resolver is consulted for it.  What
  this supports is therefore state-dependent choice among enumerated candidates, not a
  fully late-bound call whose site exists independently of any known target.
\<close>

definition call_site_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action) list" where
  "call_site_list g v = remdups (map (\<lambda>(c, ca, p). (c, ca)) (call_target_list g v))"

lemma distinct_call_site_list [simp]:
  "distinct (call_site_list g v)"
  by (simp add: call_site_list_def)

lemma set_call_site_list [simp]:
  assumes "finite (calls g)"
  shows "set (call_site_list g v)
           = {(c, ca) | c ca. \<exists>p. (c, ca, FunctionEntry p, v) \<in> calls g}"
  unfolding call_site_list_def
  by (force simp: set_call_target_list[OF assms] call_targets_def image_iff)

definition static_targets ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> call_action \<Rightarrow> pname list" where
  "static_targets g v cc ca =
     map (\<lambda>(c, a, p). p)
       (filter (\<lambda>(c, a, p). c = cc \<and> a = ca) (call_target_list g v))"

lemma static_targets_iff [simp]:
  assumes "finite (calls g)"
  shows "p \<in> set (static_targets g v cc ca)
           \<longleftrightarrow> (cc, ca, FunctionEntry p, v) \<in> calls g"
  unfolding static_targets_def
  by (force simp: call_target_list_iff[OF assms, symmetric] image_iff)

lemma distinct_static_targets [simp]:
  assumes "finite (calls g)"
  shows "distinct (static_targets g v cc ca)"
proof -
  let ?es = "filter (\<lambda>(c, a, p). c = cc \<and> a = ca) (call_target_list g v)"
  have "inj_on (\<lambda>(c, a, p). p) (set ?es)" by (auto simp: inj_on_def)
  moreover have "distinct ?es" using distinct_call_target_list[OF assms] by simp
  ultimately show ?thesis unfolding static_targets_def by (simp add: distinct_map)
qed

text \<open>Exactly when a site has a statically known callee, which is the form a coverage
  obligation stated over the enumeration needs.\<close>

lemma static_targets_neq_Nil_iff [simp]:
  assumes "finite (calls g)"
  shows "static_targets g v cc ca \<noteq> []
           \<longleftrightarrow> (\<exists>p. (cc, ca, FunctionEntry p, v) \<in> calls g)"
proof -
  have "static_targets g v cc ca \<noteq> [] \<longleftrightarrow> (\<exists>p. p \<in> set (static_targets g v cc ca))"
    by (cases "static_targets g v cc ca") auto
  thus ?thesis using static_targets_iff[OF assms] by blast
qed

definition static_resolve ::
  "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> call_action \<Rightarrow> 'd \<Rightarrow> pname list" where
  "static_resolve g v cc ca d = static_targets g v cc ca"

lemma static_resolve_iff [simp]:
  assumes "finite (calls g)"
  shows "p \<in> set (static_resolve g v cc ca d)
           \<longleftrightarrow> (cc, ca, FunctionEntry p, v) \<in> calls g"
  unfolding static_resolve_def by (rule static_targets_iff[OF assms])

text \<open>Resolving each listed site loses nothing: the sites' resolved targets, concatenated,
  carry exactly the pairs \<^const>\<open>call_target_list\<close> lists.  Order is not preserved --- one
  site's targets are gathered together --- so this is a set equality.  That is enough for
  the commutative, idempotent join folds the constraint generator runs over these entries,
  and only for those; a fold that could observe order or multiplicity would need more.\<close>

lemma set_concat_call_site_static_targets:
  "set (concat (map (\<lambda>(cc, ca). map (h cc ca) (static_targets g v cc ca))
                    (call_site_list g v)))
     = set (map (\<lambda>(c, ca, p). h c ca p) (call_target_list g v))"
  by (force simp: call_site_list_def static_targets_def image_iff)

section \<open>Which unknowns a run has to have solved\<close>

text \<open>
  \<open>vars_cover g vars\<close> is the one recurring premise every post-solution
  soundness theorem here needs: the solved key set \<open>vars\<close> contains the CFG
  entry, the target of every \<open>intra\<close> edge, and both halves of every call ---
  the callee's entry and the caller's continuation.

  Read it as a statement about a solver run, not about the graph. It
  quantifies over every edge \<open>g\<close> has, so a graph carrying a call the run never
  activated does not satisfy it: in a routed system a callee's entry unknown is
  solved only once some caller publishes its seed, and an unreachable call site
  publishes nothing. That is why a run establishes it by deciding
  \<open>vars_cover_exec\<close> against the keys it actually solved, on a graph
  \<^emph>\<open>pruned\<close> to what it can reach, rather than by an argument about
  connectivity.

  The four components travel together, so callers state and discharge one
  premise instead of four positional ones. Global, not locale-local: every
  analysis instance and the executable pipeline cite it under this name.
\<close>

definition vars_cover :: "cfg \<Rightarrow> (cfg_node \<times> unit) set \<Rightarrow> bool" where
  "vars_cover g vars \<longleftrightarrow>
     (cfg_entry g, ()) \<in> vars
   \<and> (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow> (v, ()) \<in> vars)
   \<and> (\<forall>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
        \<longrightarrow> (FunctionEntry q, ()) \<in> vars \<and> (k, ()) \<in> vars)"

lemma vars_coverI [intro]:
  assumes "(cfg_entry g, ()) \<in> vars"
    and "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
    and "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
           \<Longrightarrow> (FunctionEntry q, ()) \<in> vars"
    and "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
           \<Longrightarrow> (k, ()) \<in> vars"
  shows "vars_cover g vars"
  unfolding vars_cover_def using assms by blast

lemma vars_cover_entryD [dest]: "vars_cover g vars \<Longrightarrow> (cfg_entry g, ()) \<in> vars"
  unfolding vars_cover_def by blast

lemma vars_cover_edgeD [dest]:
  "vars_cover g vars \<Longrightarrow> (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
  unfolding vars_cover_def by blast

lemma vars_cover_enterD [dest]:
  assumes cover: "vars_cover g vars"
  shows "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
     \<Longrightarrow> (FunctionEntry q, ()) \<in> vars"
  using cover unfolding vars_cover_def by blast

lemma vars_cover_combineD [dest]:
  assumes cover: "vars_cover g vars"
  shows "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
     \<Longrightarrow> (k, ()) \<in> vars"
  using cover unfolding vars_cover_def by blast

text \<open>
  Coverage of a finite graph is testable: walk the two edge enumerations and
  test membership. The test is sufficient, not equivalent, and deliberately so.
  \<^const>\<open>vars_cover\<close> asks only about calls of the shape
  \<open>(c, CallEdge dst fs as, FunctionEntry q, k)\<close>, while the test asks about
  every tuple the enumeration yields, so it is the stronger of the two: it also
  covers a \<open>calls\<close> entry whose action or target has some other shape. Turning
  it into an equivalence would mean assuming that \<open>g\<close> has no such entry, which
  is a well-formedness fact about the graph and not something a coverage check
  should carry.
\<close>

definition vars_cover_exec :: "cfg \<Rightarrow> (cfg_node \<times> unit) set \<Rightarrow> bool" where
  "vars_cover_exec g vars \<longleftrightarrow>
     (cfg_entry g, ()) \<in> vars
   \<and> list_all (\<lambda>(u, a, v). (v, ()) \<in> vars) (cfg_intra_list g)
   \<and> list_all (\<lambda>(c, ca, ce, k). (ce, ()) \<in> vars \<and> (k, ()) \<in> vars) (cfg_calls_list g)"

lemma vars_cover_of_exec:
  assumes finE: "finite (intra g)" and finC: "finite (calls g)"
    and cover: "vars_cover_exec g vars"
  shows "vars_cover g vars"
  using cover unfolding vars_cover_exec_def vars_cover_def
  by (auto simp: list_all_iff set_cfg_intra_list[OF finE] set_cfg_calls_list[OF finC])

end

