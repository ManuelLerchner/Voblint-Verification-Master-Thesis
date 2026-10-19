(* src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy *)
locale activation_coverage =
  fixes \<kappa> :: kenv
    and g :: "(var_id, exp) gcfg" and S :: "store set"
    and cover :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and adm :: "'c call_context_policy"
    and c\<^sub>0 :: 'c
  assumes INIT[intro]: "\<And>s. s \<in> S \<Longrightarrow> s \<in> cover (cfg_entry g) c\<^sub>0"
    and INTRA[intro]: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> cover u c \<Longrightarrow> s' \<in> edge_step \<kappa> a s \<Longrightarrow> s' \<in> cover v c"
    and CALL[intro]: "\<And>u dst pars args p cont c c' s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> c' \<in> adm u c (call_info_of (CallEdge dst pars args) p) s
              (call_enter \<kappa> (CallEdge dst pars args) s)
        \<Longrightarrow> call_enter \<kappa> (CallEdge dst pars args) s \<in> cover (FunctionEntry p) c'"
    and RETURN[intro]: "\<And>u dst pars args p cont c c' p' s t es.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> admits_call_context \<kappa> g adm u c p' s es c'
        \<Longrightarrow> t \<in> cover (FunctionResult p) c'
        \<Longrightarrow> combine_collect \<kappa> dst s t \<in> cover cont c"
    and TOTAL: "call_context_total_on \<kappa> cover adm g"
