theory Activation_Backbone
  imports Activation_Local_Sound
begin

section \<open>Generic soundness of the activation-indexed collecting semantics\<close>

text \<open>
  Soundness of a seeded context-sensitive analysis stated directly against the activation-indexed
  projection \<^const>\<open>activation_collect\<close> --- the sink/key projection of the concrete
  activation-local traces \<^const>\<open>valid_ltr\<close>.  The context is ACTIVATION-STABLE: it is fixed when
  an activation is created (routed at \<^const>\<open>EA_Enter\<close>) and unchanged by the calls it later makes
  and returns from, matching Goblint's call-only \<open>Spec.context\<close>.  The backbone therefore needs no
  digest-propagation machinery: the context is structural.

  Domain- and generator-agnostic: it depends only on the abstract-domain concretisation and the
  local-trace engine \<open>valid_ltr_ctx_sound\<close>, and every context-sensitive activation soundness result
  rides on it.
\<close>

subsection \<open>The domain-independent backbone\<close>

text \<open>
  Purely semantic obligations, each at a FIXED activation context, discharge soundness through the
  local-trace engine:

    - \<open>ENTRY_G\<close>: the seed covers the start stores at the start context \<open>seedc\<close> (Goblint
      \<open>Spec.enter\<close>);
    - \<open>EDGE\<close>: an ordinary (non-\<^const>\<open>EA_Enter\<close>) edge preserves the context and covers the
      concrete step;
    - \<open>SEED_G\<close>: an \<^const>\<open>EA_Enter\<close> edge lands the entering store in the seeded callee slot at the
      routed callee context \<open>enterc c s'\<close> (Goblint \<open>Spec.context\<close> + the seed);
    - \<open>COMB\<close>: a combine reassembles the caller store and the routed callee-exit store into the
      return slot at the CALLER context \<open>c1\<close> --- Goblint's \<open>Spec.combine\<close> merges abstract states,
      not function contexts, so the resumed caller keeps its own context.

  Domain-independent: parameterised over \<open>sg\<close>, the routing \<open>enterc\<close> and the start context
  \<open>seedc\<close>.  A return map \<open>combc\<close> is not a parameter --- the stable context is the caller's.
\<close>

theorem activation_collect_sound:
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
  shows "activation_collect enterc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof
  fix st assume "st \<in> activation_collect enterc seedc g S v ctx"
  then obtain t where t: "t \<in> valid_ltr g S"
    and sn: "sink_node t = v" and kc: "key enterc seedc t = ctx" and st: "st = sink_store t"
    unfolding activation_collect_def by blast
  have "sink_store t \<in> \<lbrakk>sg (Inl (sink_node t, key enterc seedc t))\<rbrakk>"
    using ENTRY_G EDGE SEED_G COMB t by (rule valid_ltr_ctx_sound)
  then show "st \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>" using sn kc st by simp
qed

end
