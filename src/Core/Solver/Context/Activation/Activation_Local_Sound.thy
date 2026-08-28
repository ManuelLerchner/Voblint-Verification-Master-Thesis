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

text \<open>
  The architecture is layered:

    \<bullet> \<^const>\<open>valid_ltr\<close> supplies the matched caller/callee relation --- a return recovers its
      caller through \<^const>\<open>caller_of\<close>, never by independent choice;
    \<bullet> \<^const>\<open>key\<close> threads each matched trace's context through the SAME recursive shape, so
      a callee's context is derived from its caller's own, not rediscovered independently;
    \<bullet> the concretization \<open>acc v c = \<lbrakk>sg (Inl (v, c))\<rbrakk>\<close> over-approximates the stores in that
      bucket.

  The semantic obligations \<open>ENTRY_G\<close> / \<open>EDGE\<close> / \<open>CALL\<close> / \<open>COMB\<close> are exactly the locale's
  \<open>ROOT\<close> / \<open>EDGE\<close> / \<open>CALL\<close> / \<open>COMB\<close> at that concretization, so the engine follows from
  \<open>ltr_gamma.valid_ltr_subset_gamma_ltr\<close>.
\<close>

theorem valid_ltr_ctx_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, startcontext))\<rbrakk>"
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
    and t: "t \<in> valid_ltr gs g S"
    and ck: "key enterc startcontext t = c"
  shows "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, c))\<rbrakk>"
proof -
  interpret G: ltr_gamma g S "\<lambda>v c. \<lbrakk>sg (Inl (v, c))\<rbrakk>" enterc startcontext gs
    apply unfold_locales
    apply (blast intro: ENTRY_G)
    apply (blast intro: EDGE)
    apply (blast intro: CALL)
    apply (blast intro: COMB)
    done
  from t have "t \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr by blast
  then have "G.bnd t" by (simp add: G.gamma_ltr_def)
  then show ?thesis using ck by simp
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
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> gammaM (sg (Inl (cfg_entry g, startcontext)))"
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
    and t: "t \<in> valid_ltr gs g S"
    and ck: "key enterc startcontext t = c"
  shows "sink_store t \<in> gammaM (sg (Inl (sink_node t, c)))"
proof -
  interpret G: ltr_gamma g S "\<lambda>v c. gammaM (sg (Inl (v, c)))" enterc startcontext gs
    apply unfold_locales
    apply (blast intro: ENTRY_G)
    apply (blast intro: EDGE)
    apply (blast intro: CALL)
    apply (blast intro: COMB)
    done
  from t have "t \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr by blast
  then have "G.bnd t" by (simp add: G.gamma_ltr_def)
  then show ?thesis using ck by simp
qed


end
