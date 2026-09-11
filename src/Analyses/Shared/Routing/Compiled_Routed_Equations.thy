theory Compiled_Routed_Equations
  imports
    "Voblint_Framework.Routed_Context"
    "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Executable routed equations for a compiled program\<close>

text \<open>
  A routed configuration chooses a global key, a seed-key constructor, a
  routing function, a D/G specification, an initial local state and an initial
  global state. The remaining equation-system wiring is fixed: predecessor
  enumeration, edge execution, static call resolution, seed publication, and
  bottom initialization of every other unknown.

  A context-insensitive analysis is this constructor at the unit context:
  \<open>Analysis_Global ()\<close> as the global key, \<open>Activation_Seed\<close> as the seed
  constructor and \<open>route_unit\<close> as the routing function. There is no second
  unit-context generator.

  Solver policy is deliberately outside this constructor. Always-join,
  per-origin, and warrowing instances can solve the same equations without
  hiding that choice here.
\<close>

definition compiled_routed_eqs_for ::
    "'K
      \<Rightarrow> (pp \<Rightarrow> 'C \<Rightarrow> 'K)
      \<Rightarrow> (pp \<Rightarrow> 'C \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'C)
      \<Rightarrow> (pp \<times> 'C, 'K, unit,
           'D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec
      \<Rightarrow> cfg
      \<Rightarrow> 'D
      \<Rightarrow> 'G
      \<Rightarrow> (pp \<times> 'C, 'K, ('D, 'G) dg_state) eqsT"
where
  "compiled_routed_eqs_for global seed route S g initial initial_global =
     routed_node_rhs_buffered intra_predecessor_addr_list
       (\<lambda>_. global) route
       (\<lambda>ctx' src a. dg_spec_edge_tree S a src (\<lambda>_. global))
       (routed_call_tree S global seed (static_resolve g) (\<lambda>d. d = bot))
       (routed_entry_seed_tree seed)
       g bot initial initial_global"

end



