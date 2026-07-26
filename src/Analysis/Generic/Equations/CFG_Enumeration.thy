theory CFG_Enumeration
  imports "Voblint_CFG.IMP2_Proc_to_CFG"
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
  CFG semantics.\<close>
derive linorder bexp
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
  binding (\<open>tf_enter\<close>).\<close>

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
  \<open>combine_collect_abs\<close>.  The final component is returned directly so clients need not
  rebuild the result node.\<close>

definition return_calls ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> vname option \<times> cfg_node) set" where
  "return_calls g v =
     {(c, dst, FunctionResult p) | c dst formals actuals p.
        (c, CallEdge dst formals actuals, FunctionEntry p, v) \<in> calls g}"

lemma return_calls_iff:
  "(c, dst, r) \<in> return_calls g v
     \<longleftrightarrow> (\<exists>formals actuals p. r = FunctionResult p
             \<and> (c, CallEdge dst formals actuals, FunctionEntry p, v) \<in> calls g)"
  by (auto simp: return_calls_def)

lemma finite_return_calls:
  assumes "finite (calls g)"
  shows "finite (return_calls g v)"
proof -
  have "return_calls g v
          \<subseteq> (\<lambda>(c, ca, ce, k).
                (c, case ca of CallEdge dst _ _ \<Rightarrow> dst,
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
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> vname option \<times> cfg_node) list" where
  "return_call_list g v =
     map (\<lambda>(c, ca, ce, k). (c, case ca of CallEdge dst _ _ \<Rightarrow> dst,
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

end
