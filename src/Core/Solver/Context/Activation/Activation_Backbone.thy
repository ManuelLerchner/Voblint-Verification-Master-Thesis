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
  covers initial stores; ordinary edges preserve the activation context; calls cover the
  entered store at exactly the context \<open>enterc\<close> computes; and return combination writes to
  the original caller context, reading the callee back at exactly that same computed context
  (\<open>COMB\<close>'s context is not rediscovered independently --- it is \<open>CALL\<close>'s own \<open>enterc\<close>
  application). The theorem is parameterized by the solution reader, routing function, and
  root context.\<close>

theorem activation_collect_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and initial_ctx :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, initial_ctx))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and CALL: "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s
              \<in> \<lbrakk>sg (Inl (FunctionEntry p, enterc u c (call_enter gs (CallEdge dst pars args) s)))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store gs g cl s es
        \<Longrightarrow> combine_collect gs dst s t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
  shows "activation_collect gs enterc initial_ctx g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule subsetI)
  fix st assume "st \<in> activation_collect gs enterc initial_ctx g S v ctx"
  then obtain t where t: "t \<in> valid_ltr gs g S"
    and sn: "sink_node t = v" and kc: "key enterc initial_ctx t = ctx" and st: "sink_store t = st"
    by (rule activation_collect_E)
  have "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, ctx))\<rbrakk>"
    using ENTRY_G EDGE CALL COMB t kc by (rule valid_ltr_ctx_sound)
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
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and initial_ctx :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> gammaM (sg (Inl (cfg_entry g, initial_ctx)))"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> gammaM (sg (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> gammaM (sg (Inl (v, c)))"
    and CALL: "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> gammaM (sg (Inl (u, c)))
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s
              \<in> gammaM (sg (Inl (FunctionEntry p, enterc u c (call_enter gs (CallEdge dst pars args) s))))"
    and COMB: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> gammaM (sg (Inl (cl, c1))) \<Longrightarrow> t \<in> gammaM (sg (Inl (FunctionResult p, enterc cl c1 es)))
        \<Longrightarrow> call_enter_store gs g cl s es
        \<Longrightarrow> combine_collect gs dst s t \<in> gammaM (sg (Inl (cont, c1)))"
  shows "activation_collect gs enterc initial_ctx g S v ctx \<subseteq> gammaM (sg (Inl (v, ctx)))"
proof (rule subsetI)
  fix st assume "st \<in> activation_collect gs enterc initial_ctx g S v ctx"
  then obtain t where t: "t \<in> valid_ltr gs g S"
    and sn: "sink_node t = v" and kc: "key enterc initial_ctx t = ctx" and st: "sink_store t = st"
    by (rule activation_collect_E)
  have "sink_store t \<in> gammaM (sg (Inl (sink_node t, ctx)))"
    using ENTRY_G EDGE CALL COMB t kc by (rule valid_ltr_ctx_sound_gen)
  then show "st \<in> gammaM (sg (Inl (v, ctx)))" using sn st by simp
qed


end
