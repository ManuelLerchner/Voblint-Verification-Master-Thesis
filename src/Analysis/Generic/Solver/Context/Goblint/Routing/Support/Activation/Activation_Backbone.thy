theory Activation_Backbone
  imports Abstract_Domain "Voblint_CFG.CFG_Collect_Activation"
begin

section \<open>Generic soundness of the activation-indexed collecting semantics\<close>

text \<open>
  Soundness of a seeded context-sensitive analysis stated directly against the
  activation-indexed collecting semantics \<^const>\<open>cfg_collect_ctx_act\<close>.  Because
  \<^const>\<open>trace_witness_act\<close> threads the EXACT call context along the trace ---
  constant on ordinary edges, routed at \<^const>\<open>EA_Enter\<close>, resumed at combine --- the
  soundness backbone needs no digest-propagation machinery: the context is
  structural, not a whole-trace filter.  It closes the enter step by a dedicated
  seed obligation rather than a false enter-edge transfer bound.

  This is the domain- and generator-agnostic core of the activation spine: it
  depends only on \<^const>\<open>trace_witness_act\<close> and the abstract-domain concretisation,
  and every context-sensitive activation soundness result rides on it.
\<close>

subsection \<open>The domain-independent backbone\<close>

text \<open>
  Purely semantic obligations, each at a FIXED threaded context, discharge
  soundness by induction on \<^const>\<open>trace_witness_act\<close>:

    - \<open>ENTRY_G\<close>: the seed covers the start stores at the start context \<open>seedc\<close>
      (Goblint \<open>Spec.enter\<close>).  The callee-relative \<open>proc_entry\<close> seed at a call from
      the CFG entry is \<^emph>\<open>not\<close> a separate obligation: its routed context
      \<open>enterc seedc s\<close> matches the \<open>enter\<close> rule, so it reduces to \<open>ENTRY_G\<close> stepped
      through \<open>SEED_G\<close>;
    - \<open>EDGE\<close>: an ordinary (non-\<^const>\<open>EA_Enter\<close>) edge preserves the context and
      covers the concrete step;
    - \<open>SEED_G\<close>: an \<^const>\<open>EA_Enter\<close> edge lands the entering store in the seeded
      callee slot at the routed callee context \<open>enterc c s\<close> (Goblint
      \<open>Spec.context\<close> + the seed);
    - \<open>COMB\<close>: a combine reassembles the caller store and the routed callee-exit
      store into the return slot at the resumed context \<open>combc c1 (enterc c1 s)\<close>
      (Goblint \<open>Spec.combine\<close>).

  Domain-independent: parameterised over \<open>sg\<close>, the routing \<open>enterc\<close>, the return
  map \<open>combc\<close> and the start context \<open>seedc\<close>.
\<close>

theorem activation_trace_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 es)))\<rbrakk>"
    and wit: "trace_witness_act enterc combc seedc g S v kc tr"
  shows "last tr \<in> \<lbrakk>sg (Inl (v, kc))\<rbrakk>"
  using wit
proof (induction rule: trace_witness_act.induct)
  case (entry v s)
  thus ?case using ENTRY_G by simp
next
  \<comment> \<open>The callee-relative seed at a call from the CFG entry.  Its \<^emph>\<open>routed\<close> context
     \<open>enterc seedc s\<close> is exactly the \<open>enter\<close> rule's target, so it reduces to the
     start seed \<open>ENTRY_G\<close> stepped through \<open>SEED_G\<close> --- no separate obligation.\<close>
  case (proc_entry xs es v s)
  from proc_entry.hyps(2) obtain s0 where s0: "s0 \<in> S"
    and seq: "s = bind_formals xs (map (\<lambda>e. aval e s0) es) (enter_state s0)" by auto
  have step: "edge_step (EA_Enter xs es) s0 = Some s" by (simp add: seq)
  have "s0 \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>" using ENTRY_G[OF s0] .
  hence "s \<in> \<lbrakk>sg (Inl (v, enterc seedc s))\<rbrakk>"
    by (rule SEED_G[OF proc_entry.hyps(1) _ step])
  thus ?case by simp
next
  case (intra u a v c tr s')
  have "s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    by (rule EDGE[OF intra.hyps(1,2) intra.IH intra.hyps(4)])
  thus ?case by simp
next
  case (enter u xs es v c tau s')
  have "s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    by (rule SEED_G[OF enter.hyps(1) enter.IH enter.hyps(3)])
  thus ?case by simp
next
  case (combine cl ex v dst c1 tau rho r)
  have "r \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 (hd rho))))\<rbrakk>"
    using COMB[OF combine.hyps(1) combine.IH(1) combine.IH(2) combine.hyps(5)] combine.hyps(4) by simp
  thus ?case by (metis last_appendR snoc_eq_iff_butlast)
qed

text \<open>Set-level form: the activation-indexed collecting at \<open>(v, ctx)\<close> lies in the
  concretisation of the local slot \<open>sg (Inl (v, ctx))\<close> --- the activation analogue
  of \<open>clean_ctx_collect_rread\<close>, with the structural context in place of the digest
  filter.\<close>

theorem activation_collect_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 es)))\<rbrakk>"
  shows "cfg_collect_ctx_act enterc combc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof
  fix st assume "st \<in> cfg_collect_ctx_act enterc combc seedc g S v ctx"
  then obtain tr where tr: "trace_witness_act enterc combc seedc g S v ctx tr"
    and st: "st = last tr"
    unfolding cfg_collect_ctx_act_def by blast
  show "st \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    unfolding st
    by (rule activation_trace_sound[OF ENTRY_G EDGE SEED_G COMB tr])
qed

end
