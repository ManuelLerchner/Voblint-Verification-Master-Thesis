(* src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy *)
theorem activation_collect_sound:
  fixes cover :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and R :: "'c call_context_rel" and startcontext :: 'c
    and \<G> :: "vname \<Rightarrow> bool"
  assumes INIT: "\<And>s. s \<in> S \<Longrightarrow> s \<in> cover (cfg_entry g) startcontext"
    and INTRA: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> cover u c \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> cover v c"
    and CALL: "\<And>u dst pars args p cont c c' s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> R u c (call_info_of (CallEdge dst pars args) p) s
              (call_enter \<G> (CallEdge dst pars args) s) c'
        \<Longrightarrow> call_enter \<G> (CallEdge dst pars args) s
              \<in> cover (FunctionEntry p) c'"
    and RETURN: "\<And>cl dst pars args p cont c1 c' p' s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover cl c1
        \<Longrightarrow> admits_call_context \<G> g R cl c1 p' s es c'
        \<Longrightarrow> t \<in> cover (FunctionResult p) c'
        \<Longrightarrow> combine_collect \<G> dst s t \<in> cover cont c1"
    and TOTAL: "call_context_total_on cover R \<G> g"
  shows "\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v ctx \<subseteq> cover v ctx"
