theory Activation_Local_Sound
  imports Abstract_Domain "Voblint_CFG.LTR_Abstract"
begin

section \<open>Soundness of the activation-local context collecting\<close>

text \<open>
  The context-sensitive soundness engine, obtained as a projection of the domain-free interface
  \<^locale>\<open>ltr_gamma\<close> (\<^theory>\<open>Voblint_CFG.LTR_Abstract\<close>).  It discharges the same four semantic
  obligations as \<open>activation_collect_sound\<close> (\<open>ENTRY_G\<close>, \<open>EDGE\<close>, \<open>SEED_G\<close>, \<open>COMB\<close>), with one
  reshape: because the resumed activation keeps its creation context, a return is checked at the
  CALLER context \<open>c1\<close> rather than at a \<open>combc\<close>-combined context.  That reshape --- and the callee
  slot read at an \<open>enterc\<close>-routed context via \<open>callee_entry_invariant\<close> --- is now the
  locale's \<open>COMB\<close> / \<open>return_closed\<close> obligation, so this theory only instantiates the interface
  rather than re-running the \<^const>\<open>valid_ltr\<close> induction.

  This theory provides the domain-level engine \<open>valid_ltr_ctx_sound\<close>; the public
  \<open>activation_collect_sound\<close> (in \<open>Activation_Backbone\<close>) is the set-level projection over
  \<^const>\<open>activation_collect\<close>, proved by one line from it.
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
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and CALL: "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter (CallEdge dst pars args) s
             \<in> \<lbrakk>sg (Inl (FunctionEntry p,
                          enterc c (call_enter (CallEdge dst pars args) s)))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
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
