theory Call_String_Context
  imports "Voblint_Domain.Abstract_Domain" "Voblint_CFG.CFG_Def"
begin

section \<open>A reusable bounded call-string context\<close>

text \<open>
  The call-string route/enter-context pair: this theory owns only the call-string
  \<^emph>\<open>data\<close> and the one closed-term equality that makes \<open>routed_context_base_hetero\<close>'s
  routing agreement trivial for any bound \<open>k\<close> --- it deliberately does not
  import \<open>Routed_Context\<close> or \<open>DG_Ctx_Activation\<close>, and fixes no domain, no solver, and
  no CFG. \<open>cs_route\<close>/\<open>cs_context\<close> (defined below) plug into \<open>routed_context_base_hetero\<close>'s
  \<open>route\<close>/\<open>enterc\<close> parameters at whatever concrete instantiation a caller chooses; nothing
  here decides what that instantiation is.
\<close>

subsection \<open>The call-string type and its two projections\<close>

text \<open>Most recent call site first, unbounded as a type --- \<open>k\<close> only bounds the \<^emph>\<open>values\<close>
  \<open>cs_route\<close>/\<open>cs_context\<close> produce, not the type itself. This mirrors Goblint's
  \<open>C.t\<close> being a value-level choice under a type-level bound only because OCaml forces the
  bound to be a type; here \<open>k\<close> is ordinary \<^typ>\<open>nat\<close> data.\<close>

type_synonym call_string = "cfg_node list"

text \<open>The equation-level route: push the call site, keep only the most recent \<open>k\<close>. Ignores
  the entered abstract/executable value \<open>d\<close> entirely, so it is representation-independent
  for \<^emph>\<open>any\<close> domain without a per-domain commute lemma (\<open>cs_route_indep_of_data\<close> below).\<close>

definition cs_route :: "nat \<Rightarrow> pp \<Rightarrow> call_string \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> call_string" where
  "cs_route k u ctx d ca = take k (u # ctx)"

text \<open>The trace-semantic context function \<open>routed_context_base_hetero\<close>'s \<open>enterc\<close> parameter needs
  (\<open>LTR_Def\<close>'s \<open>key\<close>): same closed term as \<^const>\<open>cs_route\<close>, over the concrete
  \<^typ>\<open>store\<close> \<open>key\<close> supplies instead of an abstract/executable \<open>'d\<close>.\<close>

definition cs_context :: "nat \<Rightarrow> cfg_node \<Rightarrow> call_string \<Rightarrow> store \<Rightarrow> call_string" where
  "cs_context k u ctx s = take k (u # ctx)"

subsection \<open>The two facts every instance needs\<close>

text \<open>Routing agreement, generically: since neither side reads \<open>d\<close>/\<open>s\<close>, this holds for
  \<^emph>\<open>any\<close> \<open>k\<close>, \<open>u\<close>, \<open>ctx\<close>, \<open>d\<close>, \<open>ca\<close>, \<open>s\<close> with zero case analysis.\<close>

lemma cs_route_context_agree: "cs_route k u ctx d ca = cs_context k u ctx s"
  by (simp add: cs_route_def cs_context_def)

text \<open>Representation independence: \<^const>\<open>cs_route\<close> agrees with itself under \<^emph>\<open>any\<close>
  substitution for its data argument, since \<open>d\<close> never appears on the right-hand side. A
  caller needing \<open>cs_route k u ctx (d::'exec) ca = cs_route k u ctx (repr d) ca\<close> for a
  specific representation map \<open>repr\<close> -- an executable-to-abstract readback, say --
  gets it as an instance of this lemma, or just as directly by unfolding
  \<open>cs_route_def\<close> at the call site --- both are one line.\<close>

lemma cs_route_indep_of_data: "cs_route k u ctx d ca = cs_route k u ctx d' ca"
  by (simp add: cs_route_def)

subsection \<open>Bounded length\<close>

lemma cs_route_length: "length (cs_route k u ctx d ca) \<le> k"
  by (simp add: cs_route_def)

subsection \<open>Truncation behaviour\<close>

text \<open>Below the bound, pushing a call site loses nothing --- a plain cons, not a
  truncation. Needed for any future precision argument: contexts stay distinct as long as
  the call histories being separated fit under \<open>k\<close>.\<close>

lemma cs_route_below_bound:
  "length ctx < k \<Longrightarrow> cs_route k u ctx d ca = u # ctx"
  by (simp add: cs_route_def)

lemma cs_context_below_bound:
  "length ctx < k \<Longrightarrow> cs_context k u ctx s = u # ctx"
  by (simp add: cs_context_def)

text \<open>The central algebraic property of a bounded call string: projecting a longer bound's
  context down to a shorter one agrees with routing at the shorter bound directly. This is
  the \<open>take k1 ctx_k2 = ctx_k1\<close> fact any future \<open>k1 <= k2\<close> refinement theorem needs to relate
  the two analyses' unknown spaces.\<close>

lemma cs_route_k_mono:
  assumes "k1 \<le> k2"
  shows "take k1 (cs_route k2 u ctx d ca) = cs_route k1 u ctx d ca"
  using assms by (simp add: cs_route_def)

subsection \<open>The call-string-keyed global-key type\<close>

text \<open>The global-key space a call-string-routed equation system publishes into: one
  \<open>Global\<close> slot for the real globals, plus one \<open>Seed\<close> slot per (procedure entry,
  call-string) pair for the routed callee entry states. The \<open>Seed\<close> payload carries the
  call string itself, so the key shape does not depend on the bound \<open>k\<close> --- only the
  payload's length does. Still pure data: no domain, no solver, no CFG.\<close>

datatype call_string_gk = Global | Seed (seed_pp: pp) (seed_cs: "cfg_node list")

end
