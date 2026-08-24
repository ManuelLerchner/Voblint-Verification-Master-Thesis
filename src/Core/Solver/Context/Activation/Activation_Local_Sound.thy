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
    \<^item> \<^const>\<open>ctx_key\<close> threads each matched trace's admissible context through the SAME
      recursive shape, so a callee's context is derived from its caller's own, not
      rediscovered independently;
    \<^item> the concretization \<open>acc v c = \<lbrakk>sg (Inl (v, c))\<rbrakk>\<close> over-approximates the stores in that
      bucket.

  The semantic obligations \<open>ENTRY_G\<close> / \<open>EDGE\<close> / \<open>ADMISS_TOTAL\<close> / \<open>CALL\<close> / \<open>COMB\<close> are exactly
  the locale's \<open>ROOT\<close> / \<open>EDGE\<close> / \<open>ADMISS_TOTAL\<close> / \<open>CALL\<close> / \<open>COMB\<close> at that concretization, so the
  engine follows from \<open>ltr_gamma.valid_ltr_subset_gamma_ltr\<close>. \<^const>\<open>ctx_key\<close> is not assumed
  single-valued: several contexts may be admissible for one activation, and the bound holds
  at every one of them.
\<close>

theorem valid_ltr_ctx_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and admiss :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool" and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv
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
    and t: "t \<in> valid_ltr \<Gamma> gs g S"
    and ck: "ctx_key admiss startcontext t c"
  shows "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, c))\<rbrakk>"
proof -
  interpret G: ltr_gamma g S "\<lambda>v c. \<lbrakk>sg (Inl (v, c))\<rbrakk>" admiss startcontext gs \<Gamma>
    apply unfold_locales
    apply (blast intro: ENTRY_G)
    apply (blast intro: EDGE)
    apply (blast intro: ADMISS_TOTAL)
    apply (blast intro: CALL)
    apply (blast intro: COMB)
    done
  from t have "t \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr by blast
  then have "G.bnd t" by (simp add: G.gamma_ltr_def)
  then show ?thesis using ck by blast
qed

text \<open>
  \<open>valid_ltr_ctx_sound\<close> only ever reads its concretization through the interpreted
  \<open>ltr_gamma\<close> locale, which is already generic over an arbitrary
  \<open>cfg_node \<Rightarrow> 'c \<Rightarrow> store set\<close> reader -- the \<open>'a::sound_domain abs_state\<close>/\<open>\<lbrakk>_\<rbrakk>\<close> carrier
  above is an accidental specialization, not something the proof needs. \<open>_gen\<close> below
  makes that reader (\<open>gammaM\<close>) an explicit parameter instead, so a reachability-lifted
  carrier can instantiate it at \<open>gamma_state_lift\<close> without a parallel proof.
\<close>

theorem valid_ltr_ctx_sound_gen:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'M"
    and gammaM :: "'M \<Rightarrow> store set"
    and admiss :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool" and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv
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
    and t: "t \<in> valid_ltr \<Gamma> gs g S"
    and ck: "ctx_key admiss startcontext t c"
  shows "sink_store t \<in> gammaM (sg (Inl (sink_node t, c)))"
proof -
  interpret G: ltr_gamma g S "\<lambda>v c. gammaM (sg (Inl (v, c)))" admiss startcontext gs \<Gamma>
    apply unfold_locales
    apply (blast intro: ENTRY_G)
    apply (blast intro: EDGE)
    apply (blast intro: ADMISS_TOTAL)
    apply (blast intro: CALL)
    apply (blast intro: COMB)
    done
  from t have "t \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr by blast
  then have "G.bnd t" by (simp add: G.gamma_ltr_def)
  then show ?thesis using ck by blast
qed

end
