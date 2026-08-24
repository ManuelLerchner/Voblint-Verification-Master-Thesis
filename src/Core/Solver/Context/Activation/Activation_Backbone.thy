theory Activation_Backbone
  imports Activation_Local_Sound
begin

section \<open>Generic soundness of the activation-indexed collecting semantics\<close>

text \<open>The activation key is fixed when a call creates an activation and remains
  unchanged across its local steps and nested calls. This structural key lets
  @{const activation_collect} project concrete local traces without propagating an
  auxiliary digest. The soundness argument depends only on concretization and the
  activation-local trace rules.\<close>

subsection \<open>The domain-independent backbone\<close>

text \<open>Local obligations connect the abstract solution to the trace rules. The root seed
  covers initial stores; ordinary edges preserve the activation context; \<open>ADMISS_TOTAL\<close>
  guarantees a call can always continue into some admissible context; calls cover the
  entered store at every context \<open>admiss\<close> admits; and return combination writes to the
  original caller context, reading the callee back at whichever context \<open>admiss\<close> related to
  that SAME caller context (\<open>COMB\<close>'s \<open>c2\<close> is not rediscovered independently --- it is the
  witness \<open>CALL\<close>'s own \<open>admiss\<close> fact supplies). The theorem is parameterized by the solution
  reader, admissibility relation, and root context.\<close>

theorem activation_collect_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and admiss :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool" and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, startcontext))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step \<Gamma> a s
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and ADMISS_TOTAL: "\<And>u c s. \<exists>c'. admiss u c s c'"
    and CALL: "\<And>u dst pars args p cont c s c'.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> admiss u c (call_enter \<Gamma> gs (CallEdge dst pars args) s) c'
        \<Longrightarrow> call_enter \<Gamma> gs (CallEdge dst pars args) s \<in> \<lbrakk>sg (Inl (FunctionEntry p, c'))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 c2 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> admiss cl c1 es c2 \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, c2))\<rbrakk>
        \<Longrightarrow> call_enter_store \<Gamma> gs g cl s es
        \<Longrightarrow> combine_collect \<Gamma> gs dst s t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
  shows "activation_collect \<Gamma> gs admiss startcontext g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule subsetI)
  fix st assume "st \<in> activation_collect \<Gamma> gs admiss startcontext g S v ctx"
  then obtain t where t: "t \<in> valid_ltr \<Gamma> gs g S"
    and sn: "sink_node t = v" and kc: "ctx_key admiss startcontext t ctx" and st: "sink_store t = st"
    by (rule activation_collect_E)
  have "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, ctx))\<rbrakk>"
    using ENTRY_G EDGE ADMISS_TOTAL CALL COMB t kc by (rule valid_ltr_ctx_sound)
  then show "st \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>" using sn st by simp
qed

text \<open>
  Generic counterpart of \<open>activation_collect_sound\<close>, parametric in the concretization
  reader \<open>gammaM\<close> rather than fixed to \<open>'a::sound_domain abs_state\<close>/\<open>\<lbrakk>_\<rbrakk>\<close>: see
  \<open>valid_ltr_ctx_sound_gen\<close>'s comment for why this is a genuine generalization, not a
  new proof.
\<close>

theorem activation_collect_sound_gen:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'M"
    and gammaM :: "'M \<Rightarrow> store set"
    and admiss :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool" and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> gammaM (sg (Inl (cfg_entry g, startcontext)))"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> gammaM (sg (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step \<Gamma> a s
        \<Longrightarrow> s' \<in> gammaM (sg (Inl (v, c)))"
    and ADMISS_TOTAL: "\<And>u c s. \<exists>c'. admiss u c s c'"
    and CALL: "\<And>u dst pars args p cont c s c'.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> gammaM (sg (Inl (u, c)))
        \<Longrightarrow> admiss u c (call_enter \<Gamma> gs (CallEdge dst pars args) s) c'
        \<Longrightarrow> call_enter \<Gamma> gs (CallEdge dst pars args) s \<in> gammaM (sg (Inl (FunctionEntry p, c')))"
    and COMB: "\<And>cl dst pars args p cont c1 c2 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> gammaM (sg (Inl (cl, c1))) \<Longrightarrow> admiss cl c1 es c2 \<Longrightarrow> t \<in> gammaM (sg (Inl (FunctionResult p, c2)))
        \<Longrightarrow> call_enter_store \<Gamma> gs g cl s es
        \<Longrightarrow> combine_collect \<Gamma> gs dst s t \<in> gammaM (sg (Inl (cont, c1)))"
  shows "activation_collect \<Gamma> gs admiss startcontext g S v ctx \<subseteq> gammaM (sg (Inl (v, ctx)))"
proof (rule subsetI)
  fix st assume "st \<in> activation_collect \<Gamma> gs admiss startcontext g S v ctx"
  then obtain t where t: "t \<in> valid_ltr \<Gamma> gs g S"
    and sn: "sink_node t = v" and kc: "ctx_key admiss startcontext t ctx" and st: "sink_store t = st"
    by (rule activation_collect_E)
  have "sink_store t \<in> gammaM (sg (Inl (sink_node t, ctx)))"
    using ENTRY_G EDGE ADMISS_TOTAL CALL COMB t kc by (rule valid_ltr_ctx_sound_gen)
  then show "st \<in> gammaM (sg (Inl (v, ctx)))" using sn st by simp
qed

end
