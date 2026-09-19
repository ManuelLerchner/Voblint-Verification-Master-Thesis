theory Routed_Context_Unit
  imports Routed_Context "Voblint_CFG.LTR_Collect"
begin

section \<open>The monovariant context as a routed-context instance\<close>

text \<open>
  Every other \<^locale>\<open>routed_context_base_hetero\<close> instance (call-string, entry-state)
  routes to a non-trivial context. This theory checks the routed-context abstraction
  also admits the degenerate case a context-insensitive analysis needs: exactly one
  context, chosen the same way at every call, carrying no history and no dependence on
  the abstract state. \<open>route_unit\<close> is that routing function; nothing else
  about \<^locale>\<open>routed_context_base_hetero\<close> changes.

  The context-insensitive analysis is the routed analysis instantiated at this routing
  function (\<open>unit_dg_analysis\<close>); nothing here is a second analysis. What this theory
  adds is the collapse at the end: at the unit context the activation-indexed collecting
  semantics is \<^const>\<open>ltr_collect\<close>.
\<close>

subsection \<open>Unit routing\<close>

text \<open>
  \<open>route_unit\<close> ignores every argument and always chooses the sole context \<open>()\<close>: no
  call-site history, no dependence on the caller's abstract state, no sentinel encoding.
  \<open>enterc_unit\<close> is its trace-semantic counterpart; its graph
  \<open>call_context_rel_of_fun enterc_unit\<close> instantiates
  \<^locale>\<open>routed_context_base_hetero\<close>'s \<open>R\<close> parameter. The two are definitionally
  the same constant function, so \<open>routed_entry_cover\<close>'s routing agreement holds
  independently of any call edge, solved state, or concrete store.
\<close>

definition route_unit :: "pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit" where
  [simp]: "route_unit u ctx d ca = ()"

definition enterc_unit :: "cfg_node \<Rightarrow> unit \<Rightarrow> store \<Rightarrow> unit" where
  [simp]: "enterc_unit u ctx s = ()"

lemma route_unit_enterc_unit_agree:
  "route_unit u ctx d ca = enterc_unit u ctx s"
  by simp

text \<open>
  Local equivalence facts cheap enough for this phase: the routed callee context at any
  matched call is the monovariant Base family's own (trivial, both are \<open>()\<close>), and the two
  routing hooks resolve to the identical closed term regardless of which call edge or
  caller state produced them (so \<open>route_unit\<close>/\<open>enterc_unit\<close> are interchangeable in any
  proof obligation, not merely equal pointwise). Deeper equivalence --- that
  \<open>routed_call_program\<close>/\<open>routed_entry_seed_programs\<close> instantiated here compute
  the same solved local/global contributions as the Base route's own call and seed
  hooks --- is not attempted: the two programs have different shapes (Base reads the
  callee entry directly;
  here the entry is published through \<open>seed_key\<close> and read back), so any such equivalence
  is a solved-system/solver argument, not a local rewrite.
\<close>

text \<open>
  The unit context never filters a trace: every valid trace carries the one context
  \<^term>\<open>()\<close>, so \<^const>\<open>activation_collect\<close>'s context conjunct holds for every trace
  reaching \<open>v\<close> and the two collectors coincide. Domain-generic: no domain-specific fact is
  used, so every \<^typ>\<open>unit\<close>-context routed producer (Sign, Interval, ...) cites this one
  lemma rather than re-deriving it.
\<close>

lemma activation_collect_unit_eq_ltr_collect:
  "activation_collect gs (call_context_rel_of_fun enterc_unit) () g S v () = ltr_collect gs g S v"
  unfolding activation_collect_of_fun ltr_collect_def by simp

end
