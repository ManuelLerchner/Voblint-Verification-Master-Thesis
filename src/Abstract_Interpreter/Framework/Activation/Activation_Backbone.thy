theory Activation_Backbone
  imports "Voblint_Domain.Nonrelational_State" "Voblint_CFG.Activation_Trace_Abstract"
begin

section \<open>What one activation of a procedure may observe\<close>

text \<open>
  Every concrete call creates one callee activation.  Each step of that activation carries
  the contexts its creating call admits, a nested call derives its callee's contexts from
  those, and a return resumes the caller at the caller's own.  \<^const>\<open>activation_context_rel\<close> replays
  those choices along a trace, so a table indexed by \<open>(node, context)\<close> can be checked
  against concrete runs without carrying an auxiliary digest.  That indexing is many-to-one
  and one-to-many at once: activations reaching the same context are collected together,
  and one activation may be collected under several contexts.  The buckets of a node cover
  its stores; they need not partition them.

  \<open>cover v c\<close> is the set of stores that table admits at node \<open>v\<close> in context \<open>c\<close>.  Given the
  five local obligations of \<^locale>\<open>activation_coverage\<close> on it --- \<open>INIT\<close> for the seed stores,
  \<open>INTRA\<close> per intra edge, \<open>CALL\<close> per call and admitted context, \<open>RETURN\<close> per return,
  \<open>TOTAL\<close> for at least one admitted context per covered call ---
  \<open>activation_collect_sound\<close> bounds \<^const>\<open>activation_collect\<close>, the set
  of stores some valid activation trace can leave at one \<open>(node, context)\<close>.  It is the context-sensitive
  twin of \<open>node_collect_semantic_postfix\<close> and shares its proof shape: interpret
  \<^locale>\<open>activation_coverage\<close> at the supplied \<open>cover\<close>, then read off \<open>valid_activation_trace_covered_at\<close>.

  \<open>R\<close> says which contexts may describe a concrete call transition, and that is what indexes
  the collecting semantics.  It is handed both stores, so a policy may inspect them, but
  need not: a call-string policy ignores them, and an entry-state policy is induced by the
  analyzer's own routing decisions on the abstract entry alternatives that cover them.
  Proving that a particular policy's \<open>route\<close> induces an \<open>R\<close> total on the solved table is
  the routed context locale's job downstream, not this theorem's.
\<close>

theorem activation_collect_sound:
  assumes "activation_coverage g S cover R c\<^sub>0 \<G>"
  shows "\<A>\<^bsub>\<G>,R,c\<^sub>0,g,S\<^esub> v ctx \<subseteq> cover v ctx"
proof -
  interpret G: activation_coverage g S cover R c\<^sub>0 \<G> by (fact assms)
  show ?thesis
  proof (rule subsetI)
    fix st assume "st \<in> \<A>\<^bsub>\<G>,R,c\<^sub>0,g,S\<^esub> v ctx"
    then obtain t where t: "t \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
      and sn: "sink_node t = v" and kc: "activation_context_rel \<G> R c\<^sub>0 g t ctx"
      and st: "sink_store t = st"
      by (rule activation_collect_E)
    have "sink_store t \<in> cover (sink_node t) ctx" using G.valid_activation_trace_covered_at[OF t kc]
      .
    then show "st \<in> cover v ctx" using sn st by simp
  qed
qed

end
