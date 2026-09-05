theory Activation_Backbone
  imports "Voblint_Domain.Nonrelational_State" "Voblint_CFG.LTR_Abstract"
begin

section \<open>What one activation of a procedure may observe\<close>

text \<open>
  Every concrete call creates one callee activation.  Each step of that activation carries
  the context its creating call chose, a nested call derives its callee's context from that
  one, and a return resumes the caller at the caller's own context.  \<^const>\<open>key\<close> replays
  those choices along a trace, so a table indexed by \<open>(node, context)\<close> can be checked
  against concrete runs without carrying an auxiliary digest.  That indexing is
  many-to-one: activations reaching the same key are collected together, which is what
  keeps the table finite and what the bound below is stated over.

  \<open>cover v c\<close> is the set of stores that table admits at node \<open>v\<close> in context \<open>c\<close>.  Given four
  local closure obligations on it --- \<open>INIT\<close> for the seed stores, \<open>INTRA\<close> per intra edge,
  \<open>CALL\<close> per call, \<open>RETURN\<close> per return --- \<open>activation_collect_sound\<close> bounds
  \<^const>\<open>activation_collect\<close>, the set of stores some valid trace can leave at one
  \<open>(node, context)\<close>.  It is the context-sensitive twin of \<open>ltr_collect_semantic_postfix\<close>
  and shares its proof shape: interpret \<^locale>\<open>ltr_coverage\<close> at the supplied \<open>cover\<close>,
  then read off \<open>valid_ltr_covered\<close>.

  \<open>enterc\<close> assigns a context to each concrete call transition, and that is what indexes
  the collecting semantics.  It is handed the entered store, so a policy may inspect it,
  but need not: a call-string policy ignores it entirely, and an entry-state policy is
  induced instead by the analyzer's own routing decision on the abstract entry value.
  What the store argument buys is that the index is pinned to the concrete transition
  rather than left to the abstraction being proved sound.  Proving a particular policy's
  \<open>route\<close> and \<open>enterc\<close> agree on a covering entry alternative is the routed context
  locale's job downstream, not this theorem's.
\<close>

theorem activation_collect_sound:
  fixes cover :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and initial_ctx :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes INIT: "\<And>s. s \<in> S \<Longrightarrow> s \<in> cover (cfg_entry g) initial_ctx"
    and INTRA: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> cover u c \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> cover v c"
    and CALL: "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s
              \<in> cover (FunctionEntry p) (enterc u c (call_enter gs (CallEdge dst pars args) s))"
    and RETURN: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover cl c1 \<Longrightarrow> t \<in> cover (FunctionResult p) (enterc cl c1 es)
        \<Longrightarrow> call_enter_store gs g cl s es
        \<Longrightarrow> combine_collect gs dst s t \<in> cover cont c1"
  shows "activation_collect gs enterc initial_ctx g S v ctx \<subseteq> cover v ctx"
proof -
  interpret G: ltr_coverage g S cover enterc initial_ctx gs
    by (standard; blast intro: INIT INTRA CALL RETURN)
  show ?thesis
  proof (rule subsetI)
    fix st assume "st \<in> activation_collect gs enterc initial_ctx g S v ctx"
    then obtain t where t: "t \<in> valid_ltr gs g S"
      and sn: "sink_node t = v" and kc: "key enterc initial_ctx t = ctx"
      and st: "sink_store t = st"
      by (rule activation_collect_E)
    have "G.trace_covered t" using G.valid_ltr_covered[OF t] .
    then show "st \<in> cover v ctx" using sn kc st by simp
  qed
qed

end
