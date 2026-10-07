theory Routed_Context_Unit
  imports Routed_Context
begin

section \<open>The monovariant context as a routed-context instance\<close>

text \<open>
  Every other \<^locale>\<open>routed_context\<close> instance (call-string, entry-state)
  routes to a non-trivial context. This theory checks the routed-context abstraction
  also admits the degenerate case a context-insensitive analysis needs: exactly one
  context, chosen the same way at every call, carrying no history and no dependence on
  the abstract state. \<open>route_unit\<close> is that routing function; nothing else
  about \<^locale>\<open>routed_context\<close> changes.

  The context-insensitive analysis is the routed analysis registered at this routing
  function, exactly as the call-string and entry-state analyses are registered at
  theirs; nothing here is a second analysis. What this theory adds is the collapse at
  the end: at the unit context the activation-indexed collecting semantics is
  \<^const>\<open>node_collect\<close>.
\<close>

subsection \<open>Unit routing\<close>

text \<open>
  \<open>route_unit\<close> ignores every argument and always chooses the sole context \<open>()\<close>: no
  call-site history, no dependence on the caller's abstract state, no sentinel encoding.
  \<open>enterc_unit\<close> is its trace-semantic counterpart; its graph
  \<open>context_policy_of_fun enterc_unit\<close> instantiates
  \<^locale>\<open>routed_context\<close>'s \<open>adm\<close> parameter. The two are definitionally
  the same constant function, so \<open>routing_adequate\<close>'s routing agreement holds
  independently of any call edge, solved state, or concrete store.
\<close>

definition route_unit :: "pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit" where
  [simp]: "route_unit u ctx d ca = ()"

definition enterc_unit :: "cfg_node \<Rightarrow> unit \<Rightarrow> store \<Rightarrow> unit" where
  [simp]: "enterc_unit u ctx s = ()"

text \<open>
  The unit context never filters a trace: every valid activation trace carries the one context
  \<^term>\<open>()\<close>, so \<^const>\<open>activation_collect\<close>'s context conjunct holds for every trace
  reaching \<open>v\<close> and the two collectors coincide. Domain-generic: no domain-specific fact is
  used, so every \<^typ>\<open>unit\<close>-context routed producer (Sign, Interval, ...) cites this one
  lemma rather than re-deriving it.
\<close>

lemma activation_collect_unit_eq_node_collect:
  "\<A>\<^bsub>\<G>,context_policy_of_fun enterc_unit,(),g,S\<^esub> v () = \<C>\<^bsub>\<G>,g,S\<^esub> v"
  unfolding activation_collect_of_fun node_collect_def by simp

end
