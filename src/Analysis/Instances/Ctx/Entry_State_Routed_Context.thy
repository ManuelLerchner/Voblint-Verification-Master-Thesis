theory Entry_State_Routed_Context
  imports "Voblint_Core.Routed_Context" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Entry-state routing as a routed-context instance\<close>

text \<open>
  \<^locale>\<open>routed_context_base_hetero\<close> at a route that reads the entered callee state,
  with \<open>enterc := route_enterc_of_sigma S route sigma gk0 g\<close>, over the CFG of a compiled
  program and at whichever carrier \<open>S\<close> is stated over. The route is a parameter because
  one policy is spelled differently per carrier: \<^const>\<open>formals_route_lifted_gen\<close>
  projects the formals out of an abstract state, an executable instance projects them out
  of its own quotient state. Unlike \<open>Call_String_Routed_Context\<close>'s
  \<open>call_string_routed_context\<close>, no single seed-key datatype is shared across
  entry-state instances: each is keyed by its own carrier's value list, so \<open>gk0\<close> and
  \<open>seed_key\<close> stay genuine locale parameters.

  Three of the obligations \<^locale>\<open>routed_context_base_hetero\<close> leaves are facts about
  the routing policy or about \<^const>\<open>compile_prog\<close> alone and are discharged here once:
  \<open>finC\<close> (\<open>compile_prog_finite\<close>), \<open>call_enter_store_agree\<close> (call-source uniqueness,
  \<open>compile_prog_calls_source_unique\<close>) and \<open>route_enterc_agree\<close>
  (\<open>route_enterc_of_sigma_agree\<close>, generic in any \<open>route\<close> reading its caller state from
  \<open>sigma\<close>). \<open>seed_key_ne_gk0\<close>, \<open>call_fwd\<close> and \<open>comb_fwd\<close> remain per-instance
  assumptions: the first is datatype distinctness of the instance's seed key, the other
  two say the solved variable set covers a routed callee entry or return continuation, a
  property of the program together with what the solver explored.
\<close>

locale entry_state_routed_context =
  dg_ctx_activation_base S gammaDG gs "compile_prog Pi ps" gk0 route
    "routed_cmb_g S gk0 seed_key (static_resolve (compile_prog Pi ps))"
    "routed_extra_g seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
    and gk0 :: 'k
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and gammaM :: "'M \<Rightarrow> store set" +
  assumes seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> (FunctionEntry p,
              route u ctx
                (enter_local S pars args (locals (sigma (Inl (u, ctx))))
                    (globs (sigma (Inr gk0)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> (cont, c1) \<in> vars"
begin

sublocale routed: routed_context_base_hetero S gammaDG gs "compile_prog Pi ps" gk0
  route bot0 s0d s0g sigma vars x0 sg seed_key
  "static_resolve (compile_prog Pi ps)" gammaM
  "route_enterc_of_sigma S route sigma gk0 (compile_prog Pi ps)"
proof unfold_locales
  show "finite (calls (compile_prog Pi ps))" using compile_prog_finite by simp
next
  show "\<And>p ctx. seed_key p ctx \<noteq> gk0" by (rule seed_key_ne_gk0)
next
  fix u ctx dst pars args p cont s
  assume "(u, CallEdge dst pars args, FunctionEntry p, cont)
            \<in> calls (compile_prog Pi ps)"
  then show "p \<in> set (static_resolve (compile_prog Pi ps) cont u
                        (CallEdge dst pars args) (locals (sigma (Inl (u, ctx)))))"
    by (simp add: static_resolve_iff compile_prog_finite)
next
  fix u ctx dst pars args p cont s
  assume "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps)"
  have fin: "finite (calls (compile_prog Pi ps))" using compile_prog_finite by blast
  show "route u ctx
            (enter_local S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
            (CallEdge dst pars args)
          = route_enterc_of_sigma S route sigma gk0
              (compile_prog Pi ps) u ctx (call_enter gs (CallEdge dst pars args) s)"
    by (rule route_enterc_of_sigma_agree[OF fin compile_prog_calls_source_unique ce])
next
  fix u ctx dst pars args p cont
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps)"
  then show "(FunctionEntry p,
                route u ctx
                  (enter_local S pars args (locals (sigma (Inl (u, ctx))))
                      (globs (sigma (Inr gk0)))) (CallEdge dst pars args))
               \<in> vars"
    by (rule call_fwd)
next
  fix cl c1 dst pars args p cont
  assume "(cl, c1) \<in> vars"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps)"
  then show "(cont, c1) \<in> vars" by (rule comb_fwd)
next
  fix cl s es dst pars args p cont
  assume ces: "call_enter_store gs (compile_prog Pi ps) cl s es"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont)
               \<in> calls (compile_prog Pi ps)"
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  then show "es = call_enter gs (CallEdge dst pars args) s" using es_eq by simp
qed

text \<open>CALL and COMB, at the entry-state instance: the callee entry state published under
  the routed context is sound, and a return combine at the caller's own context is sound.
  Both are \<^locale>\<open>routed_context_base_hetero\<close>'s theorems, re-exported here so a
  concrete instance cites them without naming the sublocale.\<close>

lemmas routed_context_call = routed.routed_context_call
lemmas routed_context_comb = routed.routed_context_comb
lemmas activation_collect_sound = routed.activation_collect_dg_sound

end

end
