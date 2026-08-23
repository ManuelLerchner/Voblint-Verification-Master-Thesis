theory CFG_Enumeration
  imports "Voblint_CFG.VIMP_Proc_to_CFG"
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
\<close>

subsection \<open>Executable orders\<close>

text \<open>Structural orders make @{const sorted_list_of_set} a deterministic executable
  enumeration of intra and call relations. They affect only solver representation, not
  CFG semantics. \<open>exp\<close> already derives \<open>linorder\<close> in \<^theory>\<open>Voblint_VIMP.VIMP_Syntax\<close>.\<close>
derive linorder special_call
derive linorder edge_action
derive linorder call_action
derive linorder cfg_node

subsection \<open>Intra predecessors\<close>

text \<open>The ordinary incoming transitions of a node: an intra edge is a total store
  transformer within one activation, so this is the transfer fold the equation system runs
  at every node --- including the \<^term>\<open>EA_Ret e p\<close> edges into \<^term>\<open>FunctionResult p\<close>, by
  which return values are summarised as ordinary predecessor folding.\<close>

definition intra_predecessors :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> edge_action) set" where
  "intra_predecessors g v = {(u, a). (u, a, v) \<in> intra g}"

lemma intra_predecessors_iff:
  "(u, a) \<in> intra_predecessors g v \<longleftrightarrow> (u, a, v) \<in> intra g"
  by (simp add: intra_predecessors_def)

lemma finite_intra_predecessors:
  assumes "finite (intra g)"
  shows "finite (intra_predecessors g v)"
proof -
  have "intra_predecessors g v
          \<subseteq> (\<lambda>e :: cfg_node \<times> edge_action \<times> cfg_node. (fst e, fst (snd e))) ` intra g"
    unfolding intra_predecessors_def by force
  then show ?thesis using assms finite_subset finite_imageI by blast
qed

subsection \<open>Call-entry enumeration\<close>

text \<open>The call tuples whose callee entry is the queried node \<open>v\<close> (a \<^term>\<open>FunctionEntry p\<close>).
  The continuation does not affect the callee-entry state, so it is projected away; the
  entry contribution is the caller state routed through the call action's parameter
  binding (\<open>enter\<^sup>#\<close>).\<close>

definition entry_calls :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action) set" where
  "entry_calls g v = {(c, ca). \<exists>k. (c, ca, v, k) \<in> calls g}"

lemma entry_calls_iff:
  "(c, ca) \<in> entry_calls g v \<longleftrightarrow> (\<exists>k. (c, ca, v, k) \<in> calls g)"
  by (simp add: entry_calls_def)

lemma finite_entry_calls:
  assumes "finite (calls g)"
  shows "finite (entry_calls g v)"
proof -
  have "entry_calls g v
          \<subseteq> (\<lambda>e :: cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node. (fst e, fst (snd e))) ` calls g"
    unfolding entry_calls_def by force
  then show ?thesis using assms finite_subset finite_imageI by blast
qed

subsection \<open>Return enumeration\<close>

text \<open>The call tuples whose continuation is the queried node \<open>v\<close>, each paired with the
  caller destination and the callee's \<^term>\<open>FunctionResult p\<close> exit node --- recovered from
  the callee entry \<^term>\<open>FunctionEntry p\<close>, so no separate combine relation is needed.  The
  return contribution is the caller state and the callee-exit state assembled by
  \<open>combine\<^sup>#\<close>.  The final component is returned directly so clients need not
  rebuild the result node.\<close>

text \<open>The middle component is the call's own @{typ call_info}, not just its destination: an
  interprocedural transfer sees the callee, its formals and the actual arguments at the return
  point, matching what Goblint's \<open>combine_env\<close>/\<open>combine_assign\<close> receive.  The enumeration is the
  only layer holding the \<^const>\<open>calls\<close> relation, so the metadata is projected here; a combine
  tree never sees the CFG, and \<^const>\<open>wf_cfg\<close> does not force a call site's outgoing call edge
  to be unique, so there is no well-defined downstream lookup that could recover it instead.\<close>
definition return_calls ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_info \<times> cfg_node) set" where
  "return_calls g v =
     {(c, call_info_of ca p, FunctionResult p) | c ca p.
        (c, ca, FunctionEntry p, v) \<in> calls g}"

lemma return_calls_iff:
  "(c, ci, r) \<in> return_calls g v
     \<longleftrightarrow> (\<exists>ca p. r = FunctionResult p \<and> ci = call_info_of ca p
             \<and> (c, ca, FunctionEntry p, v) \<in> calls g)"
  by (auto simp: return_calls_def)

lemma finite_return_calls:
  assumes "finite (calls g)"
  shows "finite (return_calls g v)"
proof -
  have "return_calls g v
          \<subseteq> (\<lambda>(c, ca, ce, k).
                (c, call_info_of ca (case ce of FunctionEntry p \<Rightarrow> p | _ \<Rightarrow> undefined),
                    case ce of FunctionEntry p \<Rightarrow> FunctionResult p | _ \<Rightarrow> ce)) ` calls g"
    unfolding return_calls_def by (force split: prod.splits)
  then show ?thesis using assms finite_subset finite_imageI by blast
qed

subsection \<open>Executable enumeration\<close>

text \<open>Stable list views for the TD bridge: the intra and call edge sets sorted by their
  structural order, and the queried-node projections built by filtering.\<close>

definition cfg_intra_list :: "cfg \<Rightarrow> (cfg_node \<times> edge_action \<times> cfg_node) list" where
  "cfg_intra_list g =
     (if finite (intra g) then sorted_list_of_set (intra g) else [])"

lemma cfg_intra_list_code [code]:
  "cfg_intra_list g = sorted_list_of_set (intra g)"
  unfolding cfg_intra_list_def by (cases "finite (intra g)") auto

definition cfg_calls_list ::
    "cfg \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) list" where
  "cfg_calls_list g =
     (if finite (calls g) then sorted_list_of_set (calls g) else [])"

lemma cfg_calls_list_code [code]:
  "cfg_calls_list g = sorted_list_of_set (calls g)"
  unfolding cfg_calls_list_def by (cases "finite (calls g)") auto

lemma set_cfg_intra_list [simp]:
  "finite (intra g) \<Longrightarrow> set (cfg_intra_list g) = intra g"
  unfolding cfg_intra_list_def by simp

lemma set_cfg_calls_list [simp]:
  "finite (calls g) \<Longrightarrow> set (cfg_calls_list g) = calls g"
  unfolding cfg_calls_list_def by simp

definition intra_predecessor_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> edge_action) list" where
  "intra_predecessor_list g v =
     map (\<lambda>(u, a, w). (u, a)) (filter (\<lambda>(u, a, w). w = v) (cfg_intra_list g))"

lemma set_intra_predecessor_list [simp]:
  assumes "finite (intra g)"
  shows "set (intra_predecessor_list g v) = intra_predecessors g v"
  unfolding intra_predecessor_list_def intra_predecessors_def
  using set_cfg_intra_list[OF assms] by (force simp: image_iff)

definition entry_call_list :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action) list" where
  "entry_call_list g v =
     map (\<lambda>(c, ca, ce, k). (c, ca)) (filter (\<lambda>(c, ca, ce, k). ce = v) (cfg_calls_list g))"

lemma set_entry_call_list [simp]:
  assumes "finite (calls g)"
  shows "set (entry_call_list g v) = entry_calls g v"
  unfolding entry_call_list_def entry_calls_def
  using set_cfg_calls_list[OF assms] by (force simp: image_iff)

definition return_call_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_info \<times> cfg_node) list" where
  "return_call_list g v =
     map (\<lambda>(c, ca, ce, k).
            (c, call_info_of ca (case ce of FunctionEntry p \<Rightarrow> p | _ \<Rightarrow> undefined),
                              case ce of FunctionEntry p \<Rightarrow> FunctionResult p | _ \<Rightarrow> ce))
       (filter (\<lambda>(c, ca, ce, k).
          k = v \<and> (case ce of FunctionEntry _ \<Rightarrow> True | _ \<Rightarrow> False))
         (cfg_calls_list g))"

lemma set_return_call_list [simp]:
  assumes "finite (calls g)"
  shows "set (return_call_list g v) = return_calls g v"
  unfolding return_call_list_def return_calls_def
  using set_cfg_calls_list[OF assms]
  by (auto simp: image_iff split: call_action.splits cfg_node.splits) blast+

subsection \<open>Return enumeration with the triggering call action\<close>

text \<open>\<^const>\<open>return_call_list\<close> keeps only the caller destination projected from the
  triggering \<^typ>\<open>call_action\<close>, which is all the flat/context-insensitive combine
  (\<open>combine\<^sup>#\<close>, via \<open>Constraint_System.rhs_combine_sources\<close>) needs.
  The context-sensitive DG generator needs more: it must route both the callee-entry seed
  publication and the return-side context read from the \<^emph>\<open>same\<close> call action, and
  \<^const>\<open>entry_call_list\<close> already keeps \<open>ca\<close> whole on the entry side.  This is the return-side
  counterpart that does the same --- kept as a separate enumeration rather than widening
  \<^const>\<open>return_call_list\<close> itself, since that function and its \<^typ>\<open>vname option\<close> shape are
  also relied on by the context-free constraint system, which is out of scope for context
  routing.\<close>

definition return_call_actions ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) set" where
  "return_call_actions g v =
     {(c, ca, FunctionResult p) | c ca p. (c, ca, FunctionEntry p, v) \<in> calls g}"

lemma return_call_actions_iff:
  "(c, ca, r) \<in> return_call_actions g v
     \<longleftrightarrow> (\<exists>p. r = FunctionResult p \<and> (c, ca, FunctionEntry p, v) \<in> calls g)"
  by (auto simp: return_call_actions_def)

lemma finite_return_call_actions:
  assumes "finite (calls g)"
  shows "finite (return_call_actions g v)"
proof -
  have "return_call_actions g v
          \<subseteq> (\<lambda>(c, ca, ce, k).
                (c, ca, case ce of FunctionEntry p \<Rightarrow> FunctionResult p | _ \<Rightarrow> ce)) ` calls g"
    unfolding return_call_actions_def by (force split: prod.splits)
  then show ?thesis using assms finite_subset finite_imageI by blast
qed

definition return_call_action_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) list" where
  "return_call_action_list g v =
     map (\<lambda>(c, ca, ce, k). (c, ca,
                              case ce of FunctionEntry p \<Rightarrow> FunctionResult p | _ \<Rightarrow> ce))
       (filter (\<lambda>(c, ca, ce, k).
          k = v \<and> (case ce of FunctionEntry _ \<Rightarrow> True | _ \<Rightarrow> False))
         (cfg_calls_list g))"

lemma set_return_call_action_list [simp]:
  assumes "finite (calls g)"
  shows "set (return_call_action_list g v) = return_call_actions g v"
  unfolding return_call_action_list_def return_call_actions_def
  using set_cfg_calls_list[OF assms]
  by (auto simp: image_iff split: cfg_node.splits)

text \<open>The two enumerations agree on the call metadata they can both see: packaging the call
  action together with the callee read off the result node recovers the flat-side list exactly.
  This is the fact that justifies calling both "the return enumeration for the same edge" rather
  than two unrelated relations.\<close>

lemma return_call_action_list_call_info:
  "map (\<lambda>(c, ca, ce).
          (c, call_info_of ca (case ce of FunctionResult p \<Rightarrow> p | _ \<Rightarrow> undefined), ce))
       (return_call_action_list g v)
     = return_call_list g v"
  unfolding return_call_action_list_def return_call_list_def
  by (induction "cfg_calls_list g") (auto split: cfg_node.splits)


subsection \<open>Call sites, named by callee procedure\<close>

text \<open>
  \<^const>\<open>return_call_action_list\<close> names a callee by the node its result is read at.
  That node is derived data: the enumeration built it by mapping \<open>FunctionEntry p\<close> to
  \<open>FunctionResult p\<close> in the first place. Naming the callee by its procedure instead
  keeps the call site's own data (where the call is, what it passes, where it returns to)
  separate from anything a resolver would decide, which is what lets the callee stop
  being fixed at enumeration time. The result node is then \<open>FunctionResult p\<close> at the
  point of use.
\<close>

definition call_target_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> pname) list" where
  "call_target_list g v =
     map (\<lambda>(c, ca, ce, k). (c, ca, case ce of FunctionEntry p \<Rightarrow> p | _ \<Rightarrow> undefined))
       (filter (\<lambda>(c, ca, ce, k).
          k = v \<and> (case ce of FunctionEntry _ \<Rightarrow> True | _ \<Rightarrow> False))
         (cfg_calls_list g))"

text \<open>The two enumerations carry the same call sites in the same order; only the callee's
  spelling differs.\<close>

lemma return_call_action_list_eq_call_target_list:
  "return_call_action_list g v
     = map (\<lambda>(c, ca, p). (c, ca, FunctionResult p)) (call_target_list g v)"
  unfolding return_call_action_list_def call_target_list_def
  by (induction "cfg_calls_list g") (auto split: cfg_node.splits)

lemma call_target_list_eq_return_call_action_list:
  "call_target_list g v
     = map (\<lambda>(c, ca, ex). (c, ca, result_proc ex)) (return_call_action_list g v)"
  unfolding return_call_action_list_def call_target_list_def
  by (induction "cfg_calls_list g") (auto split: cfg_node.splits)

text \<open>Membership, in the form a call-site obligation states it: the enumeration lists
  exactly the call edges of \<open>g\<close> whose continuation is \<open>v\<close>, each paired with the
  procedure its callee entry names.\<close>

lemma set_call_target_list [simp]:
  assumes "finite (calls g)"
  shows "set (call_target_list g v)
           = {(c, ca, p) | c ca p. (c, ca, FunctionEntry p, v) \<in> calls g}"
  unfolding call_target_list_def using set_cfg_calls_list[OF assms]
  by (auto simp: image_iff split: cfg_node.splits)

lemma call_target_list_iff:
  assumes "finite (calls g)"
  shows "(c, ca, p) \<in> set (call_target_list g v)
           \<longleftrightarrow> (c, ca, FunctionEntry p, v) \<in> calls g"
  by (simp add: set_call_target_list[OF assms])

text \<open>
  The call site alone, with no callee: what a call-site-owned resolver is given.
  \<open>static_targets\<close> is the resolver that answers from the CFG, ignoring the
  caller's abstract state -- the behaviour a statically enumerated generator already
  has. A resolver reading that state instead is what makes an indirect call
  expressible; the shape of the equation does not change when it does.
\<close>

definition call_site_list ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action) list" where
  "call_site_list g v = map (\<lambda>(c, ca, p). (c, ca)) (call_target_list g v)"

definition static_targets ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> call_action \<Rightarrow> pname list" where
  "static_targets g v cc ca =
     map (\<lambda>(c, a, p). p)
       (filter (\<lambda>(c, a, p). c = cc \<and> a = ca) (call_target_list g v))"

lemma set_call_site_list [simp]:
  assumes "finite (calls g)"
  shows "set (call_site_list g v)
           = {(c, ca) | c ca. \<exists>p. (c, ca, FunctionEntry p, v) \<in> calls g}"
  unfolding call_site_list_def
  by (force simp: set_call_target_list[OF assms] image_iff)

lemma static_targets_iff:
  assumes "finite (calls g)"
  shows "p \<in> set (static_targets g v cc ca)
           \<longleftrightarrow> (cc, ca, FunctionEntry p, v) \<in> calls g"
  unfolding static_targets_def
  by (force simp: call_target_list_iff[OF assms, symmetric] image_iff)

text \<open>Every listed call site resolves to at least its own callee, which is what a
  coverage obligation stated over the enumeration needs.\<close>

lemma static_targets_nonempty:
  assumes "finite (calls g)" and "(cc, ca, FunctionEntry p, v) \<in> calls g"
  shows "static_targets g v cc ca \<noteq> []"
proof -
  have "p \<in> set (static_targets g v cc ca)"
    using static_targets_iff[OF assms(1)] assms(2) by simp
  thus ?thesis by auto
qed


subsection \<open>Full node enumeration\<close>

text \<open>Every \<^const>\<open>cfg_nodes\<close> element, listed once: the intra endpoints, the call-site/
  callee-entry/continuation triples, and the distinguished entry, deduplicated. This is the
  canonical finite node enumeration a public per-node result table draws its key domain from,
  distinct from \<^const>\<open>cfg_intra_list\<close>'s edge-indexed view.\<close>

definition cfg_node_list :: "cfg \<Rightarrow> cfg_node list" where
  "cfg_node_list g =
     remdups
       (concat (map (\<lambda>(u, a, v). [u, v]) (cfg_intra_list g)) @
        concat (map (\<lambda>(u, act, ce, after). [u, ce, after]) (cfg_calls_list g)) @
        [cfg_entry g])"

lemma set_cfg_node_list [simp]:
  assumes "finite (intra g)" and "finite (calls g)"
  shows "set (cfg_node_list g) = cfg_nodes g"
  unfolding cfg_node_list_def cfg_nodes_def
  using set_cfg_intra_list[OF assms(1)] set_cfg_calls_list[OF assms(2)]
  by force

subsection \<open>Outgoing call enumeration (caller perspective)\<close>

text \<open>The call tuples whose call site is the queried node \<open>v\<close>: the entry, action, and
  continuation of every call \<open>v\<close> makes. This is the caller-side counterpart of
  \<^const>\<open>entry_calls\<close> (callee-indexed) and \<^const>\<open>return_call_actions\<close>
  (continuation-indexed) --- routing a call-entry seed publication at its call site needs
  the callee entry and the whole \<^typ>\<open>call_action\<close> together, which neither of those two
  enumerations exposes.\<close>

definition call_successors ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) set" where
  "call_successors g v = {(ce, ca, k). (v, ca, ce, k) \<in> calls g}"

lemma call_successors_iff:
  "(ce, ca, k) \<in> call_successors g v \<longleftrightarrow> (v, ca, ce, k) \<in> calls g"
  by (simp add: call_successors_def)

lemma finite_call_successors:
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

end
