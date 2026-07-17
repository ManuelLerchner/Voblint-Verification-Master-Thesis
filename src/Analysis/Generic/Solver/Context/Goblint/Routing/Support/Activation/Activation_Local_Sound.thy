theory Activation_Local_Sound
  imports Abstract_Domain "Voblint_CFG.CFG_Local_Trace"
begin

section \<open>Soundness of the activation-local context collecting\<close>

text \<open>
  The context-sensitive soundness backbone reproved directly over the concrete
  activation-local semantics \<^const>\<open>valid_ltr\<close>, projected by the ACTIVATION-STABLE context
  \<^const>\<open>key\<close>.  It discharges the same four semantic obligations as \<open>activation_collect_sound\<close>
  (\<open>ENTRY_G\<close>, \<open>EDGE\<close>, \<open>SEED_G\<close>, \<open>COMB\<close>), with one reshape: because the resumed activation
  keeps its creation context, a return is checked at the CALLER context \<open>c1\<close> rather than at a
  \<open>combc\<close>-combined context.  The callee slot is unchanged --- the entry invariant
  \<open>callee_entry_invariant\<close> shows every valid callee, leaf or nested, is seen at an
  \<open>enterc\<close>-routed context, so the existing callee premise \<open>enterc c1 es\<close> fires without a free
  callee-context parameter.

  This is internal Stage-3 scaffolding: it carries the statement shape of the public
  \<open>activation_collect_sound\<close> over \<^const>\<open>ltr_ctx_collect\<close>, but does not yet replace it.  No
  existing collecting definition, backbone theorem, DG discharge, or example is changed.
\<close>

subsection \<open>The return step\<close>

text \<open>The \<open>ret\<close> case in one lemma.  From caller and callee bounds at their own contexts, the
  entry invariant supplies (i) the callee context as \<open>enterc (key caller) (entry_store callee)\<close>
  and (ii) the concrete enter store witnessing the call; \<open>COMB\<close> then lands the return combine at
  the caller context.  No re-rooting, no arbitrary callee context.\<close>
lemma ret_bound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, c1))\<rbrakk>"
    and callee_val: "callee \<in> valid_ltr g S"
    and cof: "caller_of callee = Some caller"
    and comb: "(sink_node caller, sink_node callee, v, dst) \<in> combines g"
    and ih_caller: "sink_store caller \<in> \<lbrakk>sg (Inl (sink_node caller, key enterc seedc caller))\<rbrakk>"
    and ih_callee: "sink_store callee \<in> \<lbrakk>sg (Inl (sink_node callee, key enterc seedc callee))\<rbrakk>"
  shows "combine_collect dst (sink_store caller) (sink_store callee)
          \<in> \<lbrakk>sg (Inl (v, key enterc seedc caller))\<rbrakk>"
proof -
  have inst: "key enterc seedc callee = enterc (key enterc seedc caller) (entry_store callee)
              \<and> call_enter_store g (sink_node caller) (sink_store caller) (entry_store callee)"
    using callee_entry_invariant[OF callee_val, THEN bspec, OF callers_refl, rule_format, OF cof] .
  have ih_callee': "sink_store callee
        \<in> \<lbrakk>sg (Inl (sink_node callee, enterc (key enterc seedc caller) (entry_store callee)))\<rbrakk>"
    using ih_callee inst[THEN conjunct1] by simp
  show ?thesis
    by (rule COMB[OF comb ih_caller ih_callee' inst[THEN conjunct2]])
qed

subsection \<open>The soundness induction\<close>

text \<open>The witness bound holds along the whole caller chain, by induction on \<^const>\<open>valid_ltr\<close>.
  \<open>init\<close> is \<open>ENTRY_G\<close>; \<open>intra\<close> is \<open>EDGE\<close> (the stable context is preserved by \<^const>\<open>extend\<close>);
  \<open>call\<close> is \<open>SEED_G\<close> (the routed callee context is exactly \<^const>\<open>key\<close> of the new \<^const>\<open>Call\<close>);
  \<open>ret\<close> is \<open>ret_bound\<close>.  The chain, rather than a per-node statement, is needed because
  \<open>ret\<close> recovers its caller structurally; the caller lies in the callee's chain.\<close>
lemma valid_ltr_ctx_chain:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, c1))\<rbrakk>"
    and t: "t \<in> valid_ltr g S"
  shows "\<forall>u \<in> callers t. sink_store u \<in> \<lbrakk>sg (Inl (sink_node u, key enterc seedc u))\<rbrakk>"
  using t
proof (induction rule: valid_ltr.induct)
  case (init s)
  have "sink_store (Root [(cfg_entry g, s)])
        \<in> \<lbrakk>sg (Inl (sink_node (Root [(cfg_entry g, s)]), key enterc seedc (Root [(cfg_entry g, s)])))\<rbrakk>"
    using ENTRY_G[OF init] by (simp add: sink_node_def sink_store_def)
  then show ?case by (simp add: callers_Root)
next
  case (intra t a v s')
  show ?case
  proof
    fix u assume "u \<in> callers (extend t (v, s'))"
    then have "u = extend t (v, s') \<or> u \<in> callers t"
      using callers_extend_subset by blast
    then show "sink_store u \<in> \<lbrakk>sg (Inl (sink_node u, key enterc seedc u))\<rbrakk>"
    proof
      assume u: "u = extend t (v, s')"
      have pt: "path t \<noteq> []" using intra.hyps(1) valid_ltr_path_nonempty by blast
      have iht: "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, key enterc seedc t))\<rbrakk>"
        using intra.IH callers_refl by blast
      have "s' \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
        by (rule EDGE[OF intra.hyps(2,3) iht intra.hyps(4)])
      then show ?thesis using u pt by (simp add: key_extend_nonempty)
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH by blast
    qed
  qed
next
  case (call caller xs es fe ex ret dst se)
  show ?case
  proof
    fix u assume "u \<in> callers (Call caller [(fe, se)])"
    then have "u = Call caller [(fe, se)] \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "sink_store u \<in> \<lbrakk>sg (Inl (sink_node u, key enterc seedc u))\<rbrakk>"
    proof
      assume u: "u = Call caller [(fe, se)]"
      have ihc: "sink_store caller \<in> \<lbrakk>sg (Inl (sink_node caller, key enterc seedc caller))\<rbrakk>"
        using call.IH callers_refl by blast
      have "se \<in> \<lbrakk>sg (Inl (fe, enterc (key enterc seedc caller) se))\<rbrakk>"
        by (rule SEED_G[OF call.hyps(2) ihc call.hyps(4)])
      then show ?thesis using u by (simp add: sink_node_def sink_store_def entry_store_def)
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH by blast
    qed
  qed
next
  case (ret callee caller v dst r)
  show ?case
  proof
    fix u assume "u \<in> callers (Resume caller callee (path caller @ [(v, r)]))"
    then have "u = Resume caller callee (path caller @ [(v, r)]) \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "sink_store u \<in> \<lbrakk>sg (Inl (sink_node u, key enterc seedc u))\<rbrakk>"
    proof
      assume u: "u = Resume caller callee (path caller @ [(v, r)])"
      have ih_caller: "sink_store caller \<in> \<lbrakk>sg (Inl (sink_node caller, key enterc seedc caller))\<rbrakk>"
        using ret.IH ret.hyps(2) callers_caller_subset callers_refl by blast
      have ih_callee: "sink_store callee \<in> \<lbrakk>sg (Inl (sink_node callee, key enterc seedc callee))\<rbrakk>"
        using ret.IH callers_refl by blast
      have "combine_collect dst (sink_store caller) (sink_store callee)
              \<in> \<lbrakk>sg (Inl (v, key enterc seedc caller))\<rbrakk>"
        by (rule ret_bound[OF COMB ret.hyps(1,2,3) ih_caller ih_callee])
      then show ?thesis using u ret.hyps(4) by (simp add: sink_node_def sink_store_def)
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH by blast
    qed
  qed
qed

text \<open>The sink of a valid trace lands in its activation slot --- the internal analogue of
  \<open>activation_collect_sound\<close>, at the trace level.\<close>
theorem valid_ltr_ctx_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, c1))\<rbrakk>"
    and t: "t \<in> valid_ltr g S"
  shows "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, key enterc seedc t))\<rbrakk>"
proof -
  have "\<forall>u \<in> callers t. sink_store u \<in> \<lbrakk>sg (Inl (sink_node u, key enterc seedc u))\<rbrakk>"
    using ENTRY_G EDGE SEED_G COMB t by (rule valid_ltr_ctx_chain)
  then show ?thesis using callers_refl by blast
qed

subsection \<open>The projection soundness\<close>

text \<open>The internal projection \<^const>\<open>ltr_ctx_collect\<close> lands in the reader slot at each
  \<open>(pp, context)\<close> --- the Stage-3 statement, matching the shape of \<open>activation_collect_sound\<close>
  but over the activation-local semantics and stable context.\<close>
theorem ltr_ctx_collect_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, c1))\<rbrakk>"
  shows "ltr_ctx_collect enterc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof
  fix st assume "st \<in> ltr_ctx_collect enterc seedc g S v ctx"
  then obtain t where t: "t \<in> valid_ltr g S"
    and sn: "sink_node t = v" and kc: "key enterc seedc t = ctx" and st: "st = sink_store t"
    unfolding ltr_ctx_collect_def by blast
  have "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, key enterc seedc t))\<rbrakk>"
    using ENTRY_G EDGE SEED_G COMB t by (rule valid_ltr_ctx_sound)
  then show "st \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>" using sn kc st by simp
qed

end
