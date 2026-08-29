theory Call_String_Context_Finite
  imports Call_String_Context "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Call-string context spaces are finite by construction\<close>

text \<open>
  #77's ask ("Context-bounding lifters ... make bounding a first-class, terminating
  mechanism instead of relying on the ambient finiteness assumption") is already met for
  call-string contexts: \<^const>\<open>cs_route\<close> truncates every context to length at most \<open>k\<close>
  (\<open>cs_route_length\<close>, \<^theory>\<open>Voblint_Core.Call_String_Context\<close>), and a compiled program's
  CFG has finitely many nodes (\<open>cfg_nodes_finite\<close>, \<^theory>\<open>Voblint_CFG.CFG_Def\<close>). Those
  two facts alone bound the entire call-string-keyed context space: combined with the
  standard library's own \<open>finite_lists_length_le\<close>, the set of contexts \<^emph>\<open>any\<close> \<open>k\<close>-bounded
  call-string routing over a compiled program could ever produce is finite, independent of
  which unknowns a particular solver run actually visits. This is a genuine strengthening
  over the \<open>solve_dom\<close> contract every routed instance otherwise relies on (a per-run,
  empirical termination check): here finiteness holds for the whole context space, before
  any solve is attempted, for every domain that instantiates \<open>call_string_routed_context\<close>
  (\<open>Call_String_Routed_Context\<close>) alike -- nothing below is domain-specific.

  Entry-state contexts do not get this for free: an entry-state context is a domain value
  (\<open>ivl list\<close>, \<open>sign list\<close>, ...) rather than a bounded-length list over a finite alphabet,
  and for an infinite-height domain such as \<open>ivl\<close> the context space is genuinely
  unbounded. Making \<^emph>\<open>that\<close> case "first-class" needs an actual bounding policy (a gas
  budget, a widening threshold, ...) with real precision consequences that nothing in the
  codebase or the tracking issue specifies yet; this development deliberately stops at the
  call-string case, which needs no such policy decision.
\<close>

lemma call_strings_bounded_finite:
  assumes "finite A"
  shows "finite {cs::call_string. set cs \<subseteq> A \<and> length cs \<le> k}"
  using assms by (rule finite_lists_length_le)

theorem compiled_call_strings_finite:
  "finite {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps main_name main) \<and> length cs \<le> k}"
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
  assumes "vars \<subseteq> cfg_nodes (compile_prog Pi ps main_name main)
             \<times> {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps main_name main) \<and> length cs \<le> k}"
  shows "finite vars"
proof (rule finite_subset[OF assms])
  have fn: "finite (cfg_nodes (compile_prog Pi ps main_name main))"
    using cfg_nodes_finite compile_prog_finite by blast
  show "finite (cfg_nodes (compile_prog Pi ps main_name main)
          \<times> {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps main_name main) \<and> length cs \<le> k})"
    using fn compiled_call_strings_finite by (rule finite_cartesian_product)
qed

text \<open>
  The seed-key space follows the same shape: one \<^const>\<open>Global\<close> slot plus one \<^const>\<open>Seed\<close>
  slot per (callee-entry node, call-string) pair. \<open>seed_pp\<close> ranges over \<^typ>\<open>pp\<close>, which is
  \<^typ>\<open>cfg_node\<close> (\<^theory>\<open>Voblint_Core.Abstract_Domain\<close>) -- a call-string seed is keyed by the
  callee's \<^const>\<open>FunctionEntry\<close> node, not the raw procedure name -- so this reuses
  \<open>cfg_nodes_finite\<close> again rather than needing a separate finiteness fact about \<open>ps\<close>.
\<close>

theorem compiled_call_string_gk_finite:
  "finite ({Global} \<union> (\<Union>p \<in> cfg_nodes (compile_prog Pi ps main_name main). Seed p `
        {cs::call_string. set cs \<subseteq> cfg_nodes (compile_prog Pi ps main_name main) \<and> length cs \<le> k}))"
  using compiled_call_strings_finite
    cfg_nodes_finite[OF compile_prog_finite[THEN conjunct1] compile_prog_finite[THEN conjunct2]]
  by auto

end
