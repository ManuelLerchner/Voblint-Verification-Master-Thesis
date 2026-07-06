theory Context_Domain
  imports TD_Side_CFG
begin

section \<open>Goblint-style context interface\<close>

text \<open>
  A single locale packaging the context-sensitivity operations that were
  previously scattered across the soundness kernel (the routing helper \<open>ec\<close>) and
  the executable switching combine (\<open>prep\<close> and the call-site-aware \<open>ec\<close>).  It
  mirrors Goblint's analysis specification:

    \<^item> \<open>start_context\<close> --- Goblint \<open>startcontext\<close>: the context of the entry
      activation of \<open>main\<close>.
    \<^item> \<open>prep\<close> --- the pre-call state transform of Goblint \<open>enter\<close> (argument /
      global pinning applied before the callee context is read).
    \<^item> \<open>ctx_sel\<close> --- Goblint \<open>context\<close>: the callee-context selector, aware of the
      call site \<^typ>\<open>pp\<close>, the caller context, and the prepped caller state.
      (Named \<open>ctx_sel\<close> because \<open>context\<close> is an Isar keyword.)
    \<^item> \<open>entdg\<close> --- the concrete enter digest: the context a concrete callee
      activation belongs to, read off its entry store.
    \<^item> \<open>cmp\<close> --- the context order matching a concrete digest against an abstract
      context (\<open>(=)\<close> for keyed globals, \<open>(\<subseteq>)\<close> for the semantic entry-store route).

  \<open>route\<close> is the composite the equation generator's switching combine computes at
  a call: prepare the caller state, then select the callee context.  The
  soundness kernel routes callee reads through \<open>route\<close>; the two-stage
  \<open>ctx_sel \<circ> prep\<close> shape is exactly \<open>switching_combine_st\<close>'s
  \<open>ec cc ctx (prep cc (sc \<squnion> g))\<close>.
\<close>

locale context_domain =
  fixes start_context :: "'c"
    and prep    :: "pp \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and ctx_sel :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c"
    and entdg   :: "store \<Rightarrow> 'c"
    and cmp     :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
begin

definition route :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" where
  "route cc ctx a = ctx_sel cc ctx (prep cc a)"

text \<open>
  The prior cc-free routing helper \<open>ec :: 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c\<close> is the
  degenerate interpretation with an identity \<open>prep\<close> and a call-site-agnostic
  \<open>ctx_sel\<close>; \<open>route\<close> then collapses to \<open>ec\<close>.  This is the backward-compatible shim
  keeping the unit-global and semantic entry-store routes unchanged.
\<close>

lemma route_cc_free:
  assumes "\<And>cc. prep cc = id"
    and "\<And>cc ctx a. ctx_sel cc ctx a = ec ctx a"
  shows "route cc ctx a = ec ctx a"
  using assms by (simp add: route_def)

end

end
