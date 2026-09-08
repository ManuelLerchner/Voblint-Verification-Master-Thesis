theory Context_Space_Finite
  imports "Voblint_Framework.Call_String_Context" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Which routing policies can have a finite solved key set\<close>

text \<open>
  A published result table is well formed only if its key set is finite
  (\<open>wf_analysis_result\<close>, in the framework's result layer). A key is a
  \<open>(node, context)\<close> pair, so one way to get there is to exhibit a fixed finite set the
  keys are drawn from and appeal to \<open>finite_subset\<close>. This theory builds that set, one per
  routing policy.

  What it builds is a candidate space, not a reachability or a termination result. Nothing
  below says which keys a solver run actually produces, and nothing below bounds how often
  the value at one key is raised -- an interval unknown can ascend forever inside a
  one-element key space. Both halves of the containment are therefore hypotheses of every
  result here, not conclusions:

    \<^item> \<open>fst ` vars \<subseteq> cfg_nodes (compile_prog Pi ps)\<close> --- the keys are nodes of the program
      the solver was given. There is no theorem here connecting the vendored solver's
      returned key set to the unknowns its equation system mentions.
    \<^item> \<open>snd ` vars\<close> lies in the policy's context space --- routing never left it. For call
      strings that is a length-and-alphabet condition, and truncation alone does not
      establish it: a starting context whose elements are not nodes of this program stays
      short under \<^const>\<open>cs_route\<close> without ever entering the space.

  What differs between policies is how cheaply the second hypothesis can be met. Call
  strings bound the length for free: \<^const>\<open>cs_route\<close> truncates every context to length at
  most \<open>k\<close> (\<open>cs_route_length\<close>, \<^theory>\<open>Voblint_Framework.Call_String_Context\<close>), and a
  compiled program's CFG has finitely many nodes (\<open>cfg_nodes_finite\<close>,
  \<^theory>\<open>Voblint_CFG.CFG_Def\<close>), so with the standard library's own
  \<open>finite_lists_length_le\<close> the space is finite for every \<open>k\<close> and every domain alike. The
  monovariant policy makes the hypothesis vacuous: its context type is \<^typ>\<open>unit\<close>, so
  there is no context space to bound and the node half is the whole story.

  An entry-state context is a domain value rather than a bounded-length list over a finite
  alphabet, so it needs a separate argument. A finite value domain together with a fixed
  formals count supplies one -- \<open>sign list\<close> at the callee's arity is a finite set -- but an
  infinite-height domain such as \<open>ivl\<close> does not, and an ordinary widening policy bounds
  values rather than the context identities keyed by them. Bounding those needs a policy
  that controls key creation or merges keys (a gas budget, a tabulation cap), with real
  precision consequences that nothing here specifies. This development stops at the two
  policies whose context space needs no such decision.

  The concrete analyses reach a finite key set by an unrelated route: they discharge their
  own obligation from the vendored solver's \<open>finite_stabl_solve\<close>, which yields a finite
  stable set from a terminating solve. Neither argument implies the other -- a bounded
  candidate space does not make a solve terminate, and a terminating solve says nothing
  about the space its keys were drawn from.
\<close>

lemma call_strings_bounded_finite:
  assumes "finite A"
  shows "finite {cs::call_string. set cs \<subseteq> A \<and> length cs \<le> k}"
  using assms by (rule finite_lists_length_le)

theorem compiled_call_strings_finite:
  "finite {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps) \<and> length cs \<le> k}"
  using cfg_nodes_finite[OF compile_prog_finite[THEN conjunct1] compile_prog_finite[THEN conjunct2]]
  by (rule call_strings_bounded_finite)

text \<open>
  The practical corollary a \<open>call_string_routed_context\<close> instance can cite directly:
  every \<open>(node, call-string)\<close> pair a \<open>k\<close>-bounded call-string analysis over a compiled
  program could ever solve for lies in a fixed finite set, so \<open>vars\<close> --- whatever a
  particular solver run actually populates it with --- is finite because it lies in a
  finite superset, not merely because the run happened to terminate.
\<close>

theorem compiled_call_string_vars_finite:
  assumes nodes: "fst ` vars \<subseteq> cfg_nodes (compile_prog Pi ps)"
    and ctxs: "snd ` vars \<subseteq> {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps)
                                \<and> length cs \<le> k}"
  shows "finite vars"
proof -
  have "vars \<subseteq> cfg_nodes (compile_prog Pi ps)
          \<times> {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps) \<and> length cs \<le> k}"
    using nodes ctxs by(auto; force) 
  moreover have "finite (cfg_nodes (compile_prog Pi ps)
          \<times> {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps) \<and> length cs \<le> k})"
    using cfg_nodes_finite compile_prog_finite compiled_call_strings_finite
    by (blast intro: finite_cartesian_product)
  ultimately show ?thesis by (rule finite_subset)
qed

text \<open>
  The seed-key space follows the same shape: one \<^const>\<open>Global\<close> slot plus one \<^const>\<open>Seed\<close>
  slot per (callee-entry node, call-string) pair. \<open>seed_pp\<close> ranges over \<^typ>\<open>pp\<close>, which is
  \<^typ>\<open>cfg_node\<close> (\<^theory>\<open>Voblint_CFG.CFG_Def\<close>) -- a call-string seed is keyed by the
  callee's \<^const>\<open>FunctionEntry\<close> node, not the raw procedure name -- so this reuses
  \<open>cfg_nodes_finite\<close> again rather than needing a separate finiteness fact about \<open>ps\<close>.
\<close>

theorem compiled_call_string_gk_finite:
  "finite ({Global} \<union> (\<Union>p \<in> cfg_nodes (compile_prog Pi ps). Seed p `
        {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps) \<and> length cs \<le> k}))"
  using compiled_call_strings_finite
    cfg_nodes_finite[OF compile_prog_finite[THEN conjunct1] compile_prog_finite[THEN conjunct2]]
  by auto

section \<open>The monovariant policy\<close>

text \<open>
  The same result for the monovariant \<open>route_unit\<close> policy, where it needs less: a context is
  \<^typ>\<open>unit\<close>, so the context factor is a singleton and the node bound is the
  entire hypothesis. Stated over \<open>fst ` vars\<close> rather than a product, since with
  one context there is nothing for a product to say.
\<close>

theorem compiled_unit_vars_finite:
  fixes vars :: "(pp \<times> unit) set"
  assumes "fst ` vars \<subseteq> cfg_nodes (compile_prog Pi ps)"
  shows "finite vars"
proof -
  have "vars \<subseteq> cfg_nodes (compile_prog Pi ps) \<times> (UNIV :: unit set)"
    using assms by auto
  moreover have "finite (cfg_nodes (compile_prog Pi ps) \<times> (UNIV :: unit set))"
    using cfg_nodes_finite compile_prog_finite by force
  ultimately show ?thesis by (rule finite_subset)
qed

end
