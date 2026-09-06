theory Context_Space_Finite
  imports "Voblint_Framework.Call_String_Context" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Which routing policies can have a finite solved key set\<close>

text \<open>
  A published result table is well formed only if its key set is finite
  (\<open>wf_analysis_result\<close>, in the framework's result layer), and nothing
  about a solved system supplies that: the solver hands back a plain
  \<open>(pp \<times> 'c) set\<close>, so the argument has to come from bounding the space those
  keys are drawn from. A key is a \<open>(node, context)\<close> pair, so bounding it means
  bounding both halves, and the two halves are in very different shape.

  The node half is one obligation shared by every policy below, and it is the
  one this theory cannot discharge:

    \<^item> \<open>fst ` vars \<subseteq> cfg_nodes (compile_prog Pi ps)\<close> --- the solver only ever
      reached nodes of the program it was given. True of every run, but there
      is no theorem here connecting the vendored solver's returned key set to
      the unknowns its equation system mentions, so each result below carries
      it as an assumption.

  The context half is where the policies part company. Call strings get it for
  free: \<^const>\<open>cs_route\<close> truncates every context to length at most \<open>k\<close>
  (\<open>cs_route_length\<close>, \<^theory>\<open>Voblint_Framework.Call_String_Context\<close>), and a
  compiled program's CFG has finitely many nodes (\<open>cfg_nodes_finite\<close>,
  \<^theory>\<open>Voblint_CFG.CFG_Def\<close>). With the standard library's own
  \<open>finite_lists_length_le\<close>, the set of contexts \<^emph>\<open>any\<close> \<open>k\<close>-bounded call-string
  routing over a compiled program could ever produce is finite, independent of
  which unknowns a particular run visits. The monovariant policy gets it more
  cheaply still: its context type is \<^typ>\<open>unit\<close>, so there is no context space
  to bound and the node obligation is the whole story.

  That is a genuine strengthening over the \<open>solve_dom\<close> contract every routed
  instance otherwise relies on (a per-run, empirical termination check): the
  context bound holds before any solve is attempted, for every domain that
  instantiates the policy alike -- nothing below is domain-specific.

  Entry-state contexts get neither: an entry-state context is a domain value
  (\<open>ivl list\<close>, \<open>sign list\<close>, ...) rather than a bounded-length list over a finite
  alphabet, and for an infinite-height domain such as \<open>ivl\<close> the context space is
  genuinely unbounded. Making \<^emph>\<open>that\<close> case "first-class" needs an actual bounding
  policy (a gas budget, a widening threshold, ...) with real precision
  consequences that nothing in the codebase specifies yet; this development
  deliberately stops at the two policies whose context space needs no such
  decision.
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
  \<^typ>\<open>cfg_node\<close> (\<^theory>\<open>Voblint_Domain.Abstract_Domain\<close>) -- a call-string seed is keyed by the
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
