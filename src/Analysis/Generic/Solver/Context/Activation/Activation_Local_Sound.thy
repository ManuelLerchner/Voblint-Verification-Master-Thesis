theory Activation_Local_Sound
  imports Abstract_Domain "Voblint_CFG.LTR_Abstract"
begin

section \<open>Soundness of the activation-local context collecting\<close>

text \<open>
  The \<^locale>\<open>ltr_gamma\<close> interface turns four local closure obligations into
  context-sensitive trace soundness.  A resumed activation keeps its creation context, so
  combine closure checks the caller at that context and reads the callee result at the context
  selected by \<open>enterc\<close>.

  \<open>valid_ltr_ctx_sound\<close> is the domain-level engine.  Its set-level projection yields soundness
  for \<^const>\<open>activation_collect\<close> without repeating the trace induction.
\<close>

subsection \<open>The abstract interface at the domain concretization\<close>

text \<open>
  The architecture is layered:

    \<^item> \<^const>\<open>valid_ltr\<close> supplies the matched caller/callee relation --- a return recovers its
      caller through \<^const>\<open>caller_of\<close>, never by independent choice;
    \<^item> \<^const>\<open>key\<close> projects each matched trace into an analysis bucket, and may merge distinct
      activations;
    \<^item> the concretization \<open>acc v c = \<lbrakk>sg (Inl (v, c))\<rbrakk>\<close> over-approximates the stores in that
      bucket.

  The four semantic obligations \<open>ENTRY_G\<close> / \<open>EDGE\<close> / \<open>SEED_G\<close> / \<open>COMB\<close> are exactly the locale's
  \<open>ROOT\<close> / \<open>EDGE\<close> / \<open>SEED\<close> / \<open>COMB\<close> at that concretization, so the engine follows from
  \<open>ltr_gamma.valid_ltr_subset_gamma_ltr\<close>.  \<^const>\<open>key\<close> is not assumed injective.
\<close>

theorem valid_ltr_ctx_sound:
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
    and t: "t \<in> valid_ltr g S"
  shows "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, key enterc seedc t))\<rbrakk>"
proof -
  interpret G: ltr_gamma g S "\<lambda>v c. \<lbrakk>sg (Inl (v, c))\<rbrakk>" enterc seedc
    apply unfold_locales
    apply (blast intro: ENTRY_G)
    apply (blast intro: EDGE)
    apply (blast intro: CALL)
    apply (blast intro: COMB)
    done
  from t have "t \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr by blast
  then show ?thesis by (simp add: G.gamma_ltr_def)
qed

end
