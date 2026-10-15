(* src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy *)
locale gactivation_coverage = collect_sem ev rv conv glob
  for ev :: "'e \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> int" and rv :: 'v
    and conv :: "'v option \<Rightarrow> int \<Rightarrow> int" and glob :: "'v \<Rightarrow> bool" +
  fixes g :: "('v, 'e) gcfg" and S :: "('v \<Rightarrow> int) set"
    and cover :: "cfg_node \<Rightarrow> 'c \<Rightarrow> ('v \<Rightarrow> int) set"
    and adm :: "('v, 'e, 'c) gcontext_policy"
    and c\<^sub>0 :: 'c
  assumes INIT[intro]: "\<And>s. s \<in> S \<Longrightarrow> s \<in> cover (cfg_entry g) c\<^sub>0"
    and INTRA[intro]: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> cover u c \<Longrightarrow> s' \<in> gedge_step a s \<Longrightarrow> s' \<in> cover v c"
    and CALL[intro]: "\<And>u dst pars args p cont c c' s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> c' \<in> adm u c (call_info_of (CallEdge dst pars args) p) s
              (gcall_enter (CallEdge dst pars args) s)
        \<Longrightarrow> gcall_enter (CallEdge dst pars args) s \<in> cover (FunctionEntry p) c'"
    and RETURN[intro]: "\<And>u dst pars args p cont c c' p' s t es.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> gadmits_call_context g adm u c p' s es c'
        \<Longrightarrow> t \<in> cover (FunctionResult p) c'
        \<Longrightarrow> gcombine_collect dst s t \<in> cover cont c"
    and TOTAL: "gcall_context_total_on cover adm g"
