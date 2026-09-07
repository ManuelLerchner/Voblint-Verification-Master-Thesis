theory Activation_Backbone
  imports "Voblint_Domain.Nonrelational_State" "Voblint_CFG.LTR_Abstract"
begin

section \<open>What one activation of a procedure may observe\<close>

text \<open>
  Every concrete call creates one callee activation.  Each step of that activation carries
  the contexts its creating call admits, a nested call derives its callee's contexts from
  those, and a return resumes the caller at the caller's own.  \<^const>\<open>trace_context\<close> replays
  those choices along a trace, so a table indexed by \<open>(node, context)\<close> can be checked
  against concrete runs without carrying an auxiliary digest.  That indexing is many-to-one
  and one-to-many at once: activations reaching the same context are collected together,
  and one activation may be collected under several contexts.  The buckets of a node cover
  its stores; they need not partition them.

  \<open>cover v c\<close> is the set of stores that table admits at node \<open>v\<close> in context \<open>c\<close>.  Given five
  local obligations on it --- \<open>INIT\<close> for the seed stores, \<open>INTRA\<close> per intra edge, \<open>CALL\<close> per
  call and admitted context, \<open>RETURN\<close> per return, \<open>TOTAL\<close> for at least one admitted context
  per covered call --- \<open>activation_collect_sound\<close> bounds \<^const>\<open>activation_collect\<close>, the set
  of stores some valid trace can leave at one \<open>(node, context)\<close>.  It is the context-sensitive
  twin of \<open>ltr_collect_semantic_postfix\<close> and shares its proof shape: interpret
  \<^locale>\<open>ltr_coverage\<close> at the supplied \<open>cover\<close>, then read off \<open>valid_ltr_covered_at\<close>.

  \<open>R\<close> says which contexts may describe a concrete call transition, and that is what indexes
  the collecting semantics.  It is handed both stores, so a policy may inspect them, but
  need not: a call-string policy ignores them, and an entry-state policy is induced by the
  analyzer's own routing decisions on the abstract entry alternatives that cover them.
  Proving that a particular policy's \<open>route\<close> induces an \<open>R\<close> total on the solved table is
  the routed context locale's job downstream, not this theorem's.
\<close>

theorem activation_collect_sound:
  fixes cover :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and R :: "'c call_context_rel" and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes INIT: "\<And>s. s \<in> S \<Longrightarrow> s \<in> cover (cfg_entry g) startcontext"
    and INTRA: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> cover u c \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> cover v c"
    and CALL: "\<And>u dst pars args p cont c c' s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> R u c (call_info_of (CallEdge dst pars args) p) s
              (call_enter gs (CallEdge dst pars args) s) c'
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s \<in> cover (FunctionEntry p) c'"
    and RETURN: "\<And>cl dst pars args p cont c1 c' p' s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover cl c1
        \<Longrightarrow> admits_call_context gs g R cl c1 p' s es c'
        \<Longrightarrow> t \<in> cover (FunctionResult p) c'
        \<Longrightarrow> combine_collect gs dst s t \<in> cover cont c1"
    and TOTAL: "call_context_total_on cover R gs g"
  shows "activation_collect gs R startcontext g S v ctx \<subseteq> cover v ctx"
proof -
  interpret G: ltr_coverage g S cover R startcontext gs
    by (standard; blast intro: INIT INTRA CALL RETURN TOTAL)
  show ?thesis
  proof (rule subsetI)
    fix st assume "st \<in> activation_collect gs R startcontext g S v ctx"
    then obtain t where t: "t \<in> valid_ltr gs g S"
      and sn: "sink_node t = v" and kc: "trace_context gs R startcontext g t ctx"
      and st: "sink_store t = st"
      by (rule activation_collect_E)
    have "sink_store t \<in> cover (sink_node t) ctx" using G.valid_ltr_covered_at[OF t kc] .
    then show "st \<in> cover v ctx" using sn st by simp
  qed
qed

end

