theory Compiled_Routed_Equations
  imports
    "Voblint_Framework.Routed_Context"
    "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Executable routed equations for a compiled program\<close>

text \<open>
  A routed configuration chooses a global key, a seed-key constructor, a
  routing function, a D/G specification, and an initial local state. The remaining
  equation-system wiring is fixed: predecessor enumeration, edge execution,
  static call resolution, seed publication, and bottom initialization.

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
      \<Rightarrow> (pp \<times> 'C, 'K, ('D, 'G) dg_state) eqsT"
where
  "compiled_routed_eqs_for global seed route S g initial =
     routed_node_rhs_buffered intra_predecessor_addr_list
       (\<lambda>_. global) route
       (\<lambda>ctx' src a. dg_spec_edge_tree S a src (\<lambda>_. global))
       (routed_call_tree S global seed (static_resolve g) (\<lambda>d. d = bot))
       (routed_entry_seed_tree seed)
       g bot initial bot"

section \<open>Solver-independent assembly outputs\<close>

text \<open>
  Once the routed equation constructor is selected, a solver contributes only
  its executable solve and termination predicates. These definitions derive the
  solution and termination wrappers from that constructor; they do not fix an
  update discipline.
\<close>

definition compiled_routed_sol_for ::
  "((pp \<times> unit, 'K, ('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot)
      dg_state) eqsT \<Rightarrow> (pp \<times> unit) \<Rightarrow>
      (pp \<times> unit) set \<times> (pp \<times> unit + 'K \<Rightarrow> ('D, 'G) dg_state))
    \<Rightarrow> 'K \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'K)
    \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit)
    \<Rightarrow> (pp \<times> unit, 'K, unit, 'D, 'G) dg_spec
    \<Rightarrow> cfg \<Rightarrow> 'D
    \<Rightarrow> (pp \<times> unit)
    \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + 'K \<Rightarrow> ('D, 'G) dg_state)" where
  "compiled_routed_sol_for solve global seed route S g initial x0 =
     solve (compiled_routed_eqs_for global seed route S g initial) x0"

definition compiled_routed_terminates_for ::
  "((pp \<times> unit, 'K, ('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot)
      dg_state) eqsT \<Rightarrow> (pp \<times> unit) \<Rightarrow> bool)
    \<Rightarrow> 'K \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'K)
    \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit)
    \<Rightarrow> (pp \<times> unit, 'K, unit, 'D, 'G) dg_spec
    \<Rightarrow> cfg \<Rightarrow> 'D \<Rightarrow> (pp \<times> unit) \<Rightarrow> bool" where
  "compiled_routed_terminates_for solve_dom global seed route S g initial x0 =
     solve_dom (compiled_routed_eqs_for global seed route S g initial) x0"


section \<open>Complete unit-context assembly\<close>

text \<open>The assembly derives equations and the solved association-list from a
  routed specification and solver. Termination remains a downstream premise.\<close>

locale compiled_unit_analysis =
  fixes global :: 'K
    and seed :: "pp \<Rightarrow> unit \<Rightarrow> 'K"
    and route :: "pp \<Rightarrow> unit \<Rightarrow> 'D::bounded_semilattice_sup_bot \<Rightarrow> call_action \<Rightarrow> unit"
    and S :: "(pp \<times> unit, 'K, unit, 'D, 'G::bounded_semilattice_sup_bot) dg_spec"
    and g :: cfg
    and initial :: "'D"
    and solve :: "((pp \<times> unit, 'K, ('D, 'G) dg_state) eqsT \<Rightarrow>
      (pp \<times> unit) \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + 'K \<Rightarrow> ('D, 'G) dg_state))"
    and x0 :: "pp \<times> unit"
begin

definition equations :: "(pp \<times> unit, 'K, ('D, 'G) dg_state) eqsT" where
  "equations = compiled_routed_eqs_for global seed route S g initial"

definition solved :: "(pp \<times> unit) set \<times>
    (pp \<times> unit + 'K \<Rightarrow> ('D, 'G) dg_state)" where
  "solved = solve equations x0"

end

end

