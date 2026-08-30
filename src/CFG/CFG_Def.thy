theory CFG_Def
  imports "Voblint_VIMP.VIMP_Proc" "HOL-Library.Countable"
begin

section \<open>Procedure-aware control-flow graph\<close>

text \<open>
  A \<open>cfg\<close> is an interprocedural control-flow graph over two disjoint transition
  relations, one per phenomenon:
    \<^item> \<open>intra\<close> --- ordinary context-preserving flow, labelled by an \<open>edge_action\<close> that is
      a total within-context store transformer.  Executed by \<open>edge_step\<close>.
    \<^item> \<open>calls\<close> --- context-crossing calls, labelled by a \<open>call_action\<close> and carrying the
      call-site, the callee entry node, and the continuation node.

  Nodes are procedure-aware: \<open>FunctionEntry p\<close> and \<open>FunctionResult p\<close> are first-class
  nodes, not keyed side slots.  There is no global exit node and no call/return matching
  side relation: a call edge already names its callee entry and its continuation, and a
  return is an ordinary intra edge into \<open>FunctionResult p\<close>.  Calls carry incompatible
  typing from intra flow, so \<open>edge_step\<close> has no call case and \<open>intra\<close> can never carry a
  call --- by typing, not by a side condition.

  Translation from VIMP to CFG and the collecting/equation layers ride on this structure.
\<close>

subsection \<open>Nodes\<close>

datatype cfg_node =
    Statement (node_stmt: nat)
  | FunctionEntry (entry_proc: pname)
  | FunctionResult (result_proc: pname)

instance cfg_node :: countable
  by countable_datatype

text \<open>The solver unknown for a program point is a CFG node.  Analysis-facing code keeps the
  short name \<open>pp\<close> for it; a return node is \<^term>\<open>FunctionResult p\<close>, a callee entry
  \<^term>\<open>FunctionEntry p\<close>, an ordinary location \<^term>\<open>Statement n\<close>.\<close>
type_synonym pp = cfg_node

subsection \<open>Edge actions and call actions\<close>

text \<open>
  \<open>edge_action\<close> labels intra flow.  It has no call constructor: every action is a total
  store transformer within one activation, so an intra edge can never denote a call.  A
  \<open>EA_Ret e p\<close> writes the return value into \<open>ret_var\<close> in the callee's own context; its
  graph target is \<open>FunctionResult p\<close> (enforced by \<open>wf_cfg\<close>), which is why return
  summarisation is ordinary predecessor folding over \<open>FunctionResult p\<close>.

  \<open>call_action\<close> labels call edges.  \<open>CallEdge dst formals args\<close> records the caller
  destination variable, the callee's formal parameter names, and the actual arguments; the
  callee identity and the continuation are the two target nodes of the \<open>calls\<close> tuple, not
  payload of the action.  Carrying \<open>formals\<close> on the edge lets the caller-side entry transfer
  \<open>call_enter\<close> bind actuals to formals without consulting a procedure table, keeping the
  trace kernel independent of the source declaration environment.
\<close>

datatype edge_action =
    EA_Nop
  | EA_Assign   (ea_var: vname) (ea_rhs: exp)
  | EA_Special  (ea_special_op: special_call) (ea_special_dst: vname)
  | EA_Assume    (ea_cond: exp)
  | EA_AssumeNot (ea_cond: exp)
  | EA_Ret      (ea_ret_val: "exp option") (ea_ret_proc: pname)
  | EA_Check    (ea_check_cond: exp)

datatype call_action =
    CallEdge (ce_dst: "vname option") (ce_formals: "vname list") (ce_args: "exp list")

instance edge_action :: countable
  by countable_datatype

instance call_action :: countable
  by countable_datatype

text \<open>
  \<open>call_info\<close> is the call-boundary metadata an interprocedural transfer may consult: the
  caller destination, the callee, its formals, and the actual arguments.  Goblint's
  \<open>Analyses.Spec\<close> hands the same four to both halves of its return protocol --
  \<open>combine_env man lval fexp f args fc au ask\<close> and \<open>combine_assign\<close> with the identical
  argument shape -- so a transfer that only ever sees the caller and callee-exit states is
  strictly weaker than that interface.  The call site and the callee-exit point are the
  combine tree's own two program-point arguments, so they are not duplicated here.

  Goblint's \<open>fexp\<close> has no separate counterpart: VIMP calls a statically named procedure, so
  \<open>ci_callee\<close> already carries what the call expression identifies.  The callee context \<open>fc\<close>
  belongs to the routed-analysis layer rather than to a transfer-record field, and
  \<open>Queries.ask\<close> over the callee exit has none: there is no query bus.
\<close>
record call_info =
  ci_dst     :: "vname option"
  ci_callee  :: pname
  ci_formals :: "vname list"
  ci_args    :: "exp list"

definition call_info_of :: "call_action \<Rightarrow> pname \<Rightarrow> call_info" where
  "call_info_of ca p =
     \<lparr> ci_dst = ce_dst ca, ci_callee = p,
       ci_formals = ce_formals ca, ci_args = ce_args ca \<rparr>"

lemma call_info_of_simps [simp]:
  "ci_dst (call_info_of ca p) = ce_dst ca"
  "ci_callee (call_info_of ca p) = p"
  "ci_formals (call_info_of ca p) = ce_formals ca"
  "ci_args (call_info_of ca p) = ce_args ca"
  by (simp_all add: call_info_of_def)

subsection \<open>CFG record: two relations\<close>

text \<open>
  \<open>calls\<close> is a four-place relation \<open>(call_site, act, callee_entry, continuation)\<close>: the
  callee entry and the continuation are ordinary nodes, kept explicit so no matching side
  relation is needed.  The flat (call-free) CFG is exactly the \<open>calls = {}\<close> fragment, so
  every fact quantified over \<open>intra\<close> is verbatim a flat-CFG fact.
\<close>

record cfg =
  intra     :: "(cfg_node \<times> edge_action \<times> cfg_node) set"
  calls     :: "(cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
  cfg_entry :: cfg_node
  checks    :: "(cfg_node \<times> exp) set"

subsection \<open>Intra edge execution\<close>

text \<open>
  \<open>special_step\<close> is \<open>special_call\<close>'s own step function, factored out of \<open>edge_step\<close>
  so that extending the special-call vocabulary only touches this function (via
  \<open>special_result\<close>, shared with the source small-step semantics) and
  \<open>special_step_nonempty\<close> below, not every generic lemma stated over \<open>edge_action\<close>.
  \<open>Nondet_Int\<close> havocs the destination; \<open>Min\<close>/\<open>Max\<close> write exactly one, deterministic
  value, so no single equation characterizes every \<open>sc\<close> uniformly any more --
  callers reasoning about an as-yet-unclassified \<open>sc\<close> case-split on it instead.
\<close>

fun special_step :: "special_call \<Rightarrow> vname \<Rightarrow> store \<Rightarrow> store set" where
  "special_step sc x s = {s(x := v) |v. special_result sc s v}"

lemma special_step_nonempty [simp]: "special_step sc x s \<noteq> {}"
  by (cases sc) auto

text \<open>\<open>edge_step\<close> is the single primitive semantics of an intra action.  It is defined for
  every constructor and has no call case; guards are the only source of \<open>None\<close>.\<close>

fun edge_step :: "edge_action \<Rightarrow> store \<Rightarrow> store set" where
  "edge_step EA_Nop s = {s}"
| "edge_step (EA_Assign x a) s = {s(x := aval a s)}"
| "edge_step (EA_Special sc x) s = special_step sc x s"
| "edge_step (EA_Assume b) s = (if truthy (aval b s) then {s} else {})"
| "edge_step (EA_AssumeNot b) s = (if truthy (aval b s) then {} else {s})"
| "edge_step (EA_Ret e p) s =
     {s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))}"
| "edge_step (EA_Check c) s = {s}"

subsection \<open>Intra-only execution paths\<close>

text \<open>
  \<open>intra_path\<close> is the reflexive-transitive closure of \<^const>\<open>edge_step\<close> along \<^const>\<open>intra\<close>
  edges, on \<open>(node, store)\<close> pairs.  It deliberately excludes \<^const>\<open>calls\<close>: an intra path
  never pushes or pops an activation, so it lifts to the collecting semantics without any
  stack-representation side condition, and to a stack-preserving CFG run at any stack.
\<close>

text \<open>One intra transition on a \<open>(node, store)\<close> pair.  \<open>intra_path\<close> is its \<^const>\<open>star\<close>, so
  reflexivity, transitivity and the induction rule come from \<^theory>\<open>HOL-IMP.Star\<close> rather than
  from a bespoke closure.  The name avoids \<open>intra_step\<close>, which is the \<^emph>\<open>source\<close>-level
  \<^const>\<open>pstep\<close> fragment.\<close>

definition cfg_intra_step :: "cfg \<Rightarrow> cfg_node \<times> store \<Rightarrow> cfg_node \<times> store \<Rightarrow> bool" where
  "cfg_intra_step g p q \<longleftrightarrow>
     (\<exists>a. (fst p, a, fst q) \<in> intra g \<and> snd q \<in> edge_step a (snd p))"

abbreviation intra_path :: "cfg \<Rightarrow> cfg_node \<times> store \<Rightarrow> cfg_node \<times> store \<Rightarrow> bool" where
  "intra_path g \<equiv> star (cfg_intra_step g)"

lemma cfg_intra_stepI [intro]:
  "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> cfg_intra_step g (u, s) (v, s')"
  by (auto simp: cfg_intra_step_def)

lemma cfg_intra_stepE [elim]:
  assumes "cfg_intra_step g (u, s) (v, s')"
  obtains a where "(u, a, v) \<in> intra g" "s' \<in> edge_step a s"
  using assms by (auto simp: cfg_intra_step_def)

lemma intra_path_single:
  "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> intra_path g (u, s) (v, s')"
  by (intro star_step1 cfg_intra_stepI)

lemma intra_path_nop:
  "(u, EA_Nop, v) \<in> intra g \<Longrightarrow> intra_path g (u, s) (v, s)"
  by (rule intra_path_single[where a = EA_Nop]) simp_all


subsection \<open>Node set (derived, not stored)\<close>

text \<open>\<open>cfg_nodes\<close> is reconstructed from the endpoints of \<open>intra\<close>, every node occurring in
  \<open>calls\<close>, and \<open>cfg_entry\<close>.  It is not a record field.\<close>

definition cfg_nodes :: "cfg \<Rightarrow> cfg_node set" where
  "cfg_nodes g =
     {u. \<exists>a v. (u, a, v) \<in> intra g}
     \<union> {v. \<exists>u a. (u, a, v) \<in> intra g}
     \<union> {u. \<exists>act ce after. (u, act, ce, after) \<in> calls g}
     \<union> {ce. \<exists>u act after. (u, act, ce, after) \<in> calls g}
     \<union> {after. \<exists>u act ce. (u, act, ce, after) \<in> calls g}
     \<union> {cfg_entry g}"

text \<open>Whole-program completion is the entry procedure's \<open>FunctionResult\<close>.  A graph whose
  entry is not a procedure entry is never compiled; the fallback keeps the function total
  and aborts in generated code.\<close>
definition cfg_exit :: "cfg \<Rightarrow> cfg_node" where
  "cfg_exit g =
    (case cfg_entry g of
       FunctionEntry p \<Rightarrow> FunctionResult p
     | n \<Rightarrow> Code.abort (STR ''cfg_exit: entry is not a procedure entry'') (\<lambda>_. n))"

subsection \<open>Well-formedness\<close>

text \<open>\<open>wf_cfg\<close> is structural only: call edges enter procedure-entry nodes; no intra edge
  enters a procedure-entry node (so a callee is reached only across a call); and a return
  action lands on the matching procedure result.  No compiler-correctness or
  source-semantic property is included.\<close>

definition wf_cfg :: "cfg \<Rightarrow> bool" where
  "wf_cfg g \<longleftrightarrow>
     (\<forall>u act ce after. (u, act, ce, after) \<in> calls g \<longrightarrow> (\<exists>p. ce = FunctionEntry p))
   \<and> (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow> (\<forall>p. v \<noteq> FunctionEntry p))
   \<and> (\<forall>u e p v. (u, EA_Ret e p, v) \<in> intra g \<longrightarrow> v = FunctionResult p)"

subsection \<open>Structural invariants\<close>

lemma intra_endpoints_in_nodes:
  assumes "(u, a, v) \<in> intra g"
  shows "u \<in> cfg_nodes g" and "v \<in> cfg_nodes g"
  using assms by (auto simp: cfg_nodes_def)

lemma call_endpoints_in_nodes:
  assumes "(u, act, ce, after) \<in> calls g"
  shows "u \<in> cfg_nodes g" and "ce \<in> cfg_nodes g" and "after \<in> cfg_nodes g"
  using assms by (auto simp: cfg_nodes_def)

lemma cfg_entry_in_nodes: "cfg_entry g \<in> cfg_nodes g"
  by (simp add: cfg_nodes_def)

text \<open>Each of the five \<open>cfg_nodes\<close> disjuncts is a projection of \<open>intra g\<close> or \<open>calls g\<close>,
  so it inherits their finiteness as a finite image; the sixth is a singleton.\<close>
lemma cfg_nodes_finite:
  assumes "finite (intra g)" and "finite (calls g)"
  shows "finite (cfg_nodes g)"
proof -
  have "{u. \<exists>a v. (u, a, v) \<in> intra g} = (\<lambda>(u, a, v). u) ` intra g"
    and "{v. \<exists>u a. (u, a, v) \<in> intra g} = (\<lambda>(u, a, v). v) ` intra g"
    by force+
  moreover
  have "{u. \<exists>act ce after. (u, act, ce, after) \<in> calls g} = (\<lambda>(u, act, ce, after). u) ` calls g"
    and "{ce. \<exists>u act after. (u, act, ce, after) \<in> calls g} = (\<lambda>(u, act, ce, after). ce) ` calls g"
    and "{after. \<exists>u act ce. (u, act, ce, after) \<in> calls g}
           = (\<lambda>(u, act, ce, after). after) ` calls g"
    by force+
  ultimately show ?thesis
    unfolding cfg_nodes_def using assms by simp
qed

subsection \<open>Executable orders\<close>

text \<open>Structural orders make @{const sorted_list_of_set} a deterministic executable
  enumeration of intra and call relations. They affect only solver representation, not
  CFG semantics. \<open>exp\<close> already derives \<open>linorder\<close> in \<^theory>\<open>Voblint_VIMP.VIMP_Syntax\<close>.\<close>
derive linorder special_call
derive linorder edge_action
derive linorder call_action
derive linorder cfg_node

subsection \<open>Executable enumeration\<close>

text \<open>Stable list views for the TD bridge: the intra and call edge sets sorted by their
  structural order. Both guard on \<^term>\<open>finite (intra g)\<close>/\<^term>\<open>finite (calls g)\<close>:
  every compiled graph satisfies it, so the \<^const>\<open>Code.abort\<close> branch never fires in
  practice, and names the violation instead of failing on an uninformative
  \<^const>\<open>sorted_list_of_set\<close> pattern-match error. Placed here rather than in the Core
  session's own equation-generation enumerations, so any consumer of this session alone
  --- a compiled graph's \<open>finite_cfg\<close> interpretation among them --- gets them for free.\<close>

definition cfg_intra_list :: "cfg \<Rightarrow> (cfg_node \<times> edge_action \<times> cfg_node) list" where
  "cfg_intra_list g =
     (if finite (intra g) then sorted_list_of_set (intra g)
      else Code.abort (STR ''cfg_intra_list: infinite intra edge set'') (\<lambda>_. []))"

lemma cfg_intra_list_code [code]:
  "cfg_intra_list g = sorted_list_of_set (intra g)"
  unfolding cfg_intra_list_def by (cases "finite (intra g)") auto

definition cfg_calls_list ::
    "cfg \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) list" where
  "cfg_calls_list g =
     (if finite (calls g) then sorted_list_of_set (calls g)
      else Code.abort (STR ''cfg_calls_list: infinite calls edge set'') (\<lambda>_. []))"

lemma cfg_calls_list_code [code]:
  "cfg_calls_list g = sorted_list_of_set (calls g)"
  unfolding cfg_calls_list_def by (cases "finite (calls g)") auto

lemma set_cfg_intra_list [simp]:
  "finite (intra g) \<Longrightarrow> set (cfg_intra_list g) = intra g"
  unfolding cfg_intra_list_def by simp

lemma set_cfg_calls_list [simp]:
  "finite (calls g) \<Longrightarrow> set (cfg_calls_list g) = calls g"
  unfolding cfg_calls_list_def by simp

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

text \<open>A \<open>cfg\<close> whose two transition relations are finite.  Bundles the two
  finiteness facts every enumeration and every compiled-graph interpretation
  needs, so a caller states one assumption instead of two, and \<open>finite_nodes\<close>
  becomes derivable rather than re-proved at each instance.\<close>
locale finite_cfg =
  fixes g :: cfg
  assumes finite_intra [intro, simp]: "finite (intra g)"
    and finite_calls [intro, simp]: "finite (calls g)"
begin

lemma finite_nodes [simp]: "finite (cfg_nodes g)"
  by (rule cfg_nodes_finite) simp_all

end

end

