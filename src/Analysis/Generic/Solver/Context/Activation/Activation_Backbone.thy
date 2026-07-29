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

text \<open>Four local obligations connect the abstract solution to the trace rules.
  The root seed covers initial stores; ordinary edges preserve the activation key; calls
  cover the entered store at the routed callee key; and return combination writes to the
  original caller key. The theorem is parameterized by the solution reader, entry routing,
  and root key. No return-key function is needed because the caller key is stable.\<close>

theorem activation_collect_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and CALL: "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter is_global (CallEdge dst pars args) s
             \<in> \<lbrakk>sg (Inl (FunctionEntry p,
                          enterc u c (call_enter is_global (CallEdge dst pars args) s)))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect is_global dst s t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
  shows "activation_collect enterc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule subsetI)
  fix st assume "st \<in> activation_collect enterc seedc g S v ctx"
  then obtain t where t: "t \<in> valid_ltr g S"
    and sn: "sink_node t = v" and kc: "key enterc seedc t = ctx" and st: "sink_store t = st"
    by (rule activation_collect_E)
  have "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, key enterc seedc t))\<rbrakk>"
    using ENTRY_G EDGE CALL COMB t by (rule valid_ltr_ctx_sound)
  then show "st \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>" using sn kc st by simp
qed

end
