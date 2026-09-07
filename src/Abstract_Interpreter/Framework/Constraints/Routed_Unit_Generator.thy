theory Routed_Unit_Generator
  imports Routed_Context_Unit CFG_Enumeration
begin

section \<open>Building the equations of a context-insensitive analysis\<close>

text \<open>
  A context-insensitive analysis is the routed protocol run at a single context,
  the unit one: every call routes the same way, so a procedure has one summary
  rather than one per calling context. This theory names that instantiation of
  the generic seeded generator --- once, so no second call-generation algorithm
  can hide behind a differently named wrapper --- in an unbuffered and a
  side-buffered form. Nothing here is specific to how a state is represented;
  the carrier stays a parameter.
\<close>

text \<open>
  The executable generator is the same polymorphic seeded keyed generator
  (\<^const>\<open>routed_node_rhs\<close>) every routed instance uses, with its
  intra hook instantiated at the specification's own compiled edge tree.
  Unit context (\<open>gkey = (\<lambda>_. ())\<close>), no procedure-entry seed
  (\<open>frame_seed = (\<lambda>_. bot)\<close>).
\<close>

text \<open>
  A context-insensitive analysis is the routed protocol at the unit context: every
  call routes to \<^const>\<open>route_unit\<close>, the seed key is \<^const>\<open>Activation_Seed\<close>, the
  analysis global is \<^const>\<open>Analysis_Global\<close>, and targets resolve statically.
  \<open>unit_routed_eqs\<close> is that generator at an arbitrary specification, taking the
  compiled graph directly: every consumer --- a registration locale, a production
  entry point, an executable regression --- names this one constant, so there is
  no second call-generation algorithm hidden behind a differently named wrapper.
\<close>

definition unit_routed_eqs ::
  "(pp \<times> unit, (unit, unit) routed_gk, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, ('D, 'G) dg_state) eqsT"
where
  "unit_routed_eqs S g bot0 s0d s0g =
     routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>c src a. dg_spec_edge_tree S a src (\<lambda>_. Analysis_Global ()))
       (routed_call_tree S (Analysis_Global ()) Activation_Seed (static_resolve g) (\<lambda>d. d = bot))
       (routed_entry_seed_tree Activation_Seed)
       g bot0 s0d s0g"

text \<open>
  The buffered sibling: the same specification, the same unit context, folded so a
  node with several intra predecessors or several returning calls publishes its
  analysis-global contribution once per evaluation rather than once per
  contribution --- the discipline a per-origin-gated update rule needs.
  \<open>routed_domain_exec.pp_st\<close> (\<open>Routed_Exec_Refinement\<close>, this session) is the generic
  bridge from a computed post-solution of this generator back to
  \<^const>\<open>unit_routed_eqs\<close>'s post-solution, so a caller solves this one and still
  satisfies \<^locale>\<open>dg_ctx_activation_base\<close>'s premise unchanged.
\<close>

definition unit_routed_eqs_buffered ::
  "(pp \<times> unit, (unit, unit) routed_gk, unit, 'D::bounded_semilattice_sup_bot,
     'G::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, ('D, 'G) dg_state) eqsT"
where
  "unit_routed_eqs_buffered S g bot0 s0d s0g =
     routed_node_rhs_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>c src a. dg_spec_edge_tree S a src (\<lambda>_. Analysis_Global ()))
       (routed_call_tree S (Analysis_Global ()) Activation_Seed (static_resolve g) (\<lambda>d. d = bot))
       (routed_entry_seed_tree Activation_Seed)
       g bot0 s0d s0g"
end
