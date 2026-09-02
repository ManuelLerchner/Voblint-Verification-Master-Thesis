theory Call_String_Routed_Context
  imports "Voblint_Framework.Routed_Context" "Voblint_Framework.Call_String_Context" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Call-string routing as a routed-context instance\<close>

text \<open>
  \<^locale>\<open>routed_context_base_hetero\<close> at \<open>route := cs_route k\<close>, \<open>enterc := cs_context k\<close>,
  \<open>gk0 := Global\<close> and \<open>seed_key := Seed\<close>, over the CFG of a compiled program and at
  whichever carrier \<open>S\<close> is stated over. Four of the obligations that specialization
  leaves are facts about the routing policy or about \<^const>\<open>compile_prog\<close> alone and are
  discharged here once and for all \<open>k\<close>:

    \<^item> \<open>finC\<close> holds for every \<^const>\<open>compile_prog\<close> output (\<open>compile_prog_finite\<close>);
    \<^item> \<open>call_enter_store_agree\<close> is call-source uniqueness for every
      \<^const>\<open>compile_prog\<close> output (\<open>compile_prog_calls_source_unique\<close>);
    \<^item> \<open>seed_key_ne_gk0\<close> is datatype distinctness for \<^type>\<open>call_string_gk\<close>;
    \<^item> \<open>route_enterc_agree\<close> is \<^const>\<open>cs_route\<close> and \<^const>\<open>cs_context\<close> being the same
      closed term (\<open>cs_route_context_agree\<close>), independently of the entered value.

  \<open>call_fwd\<close> and \<open>comb_fwd\<close> remain assumptions, and deliberately so: each says the solved
  variable set covers a particular routed callee entry or return continuation, which is a
  property of the program together with what the solver actually explored. An instance
  supplies them; no generic argument can.
\<close>

locale call_string_routed_context =
  dg_ctx_activation_base S gammaDG gs "compile_prog Pi ps" Global "cs_route k"
    "routed_cmb_g S Global Seed (static_resolve (compile_prog Pi ps))"
    "routed_extra_g Seed Global"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "(pp \<times> cfg_node list, call_string_gk, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
    and k :: nat
    and bot0 s0d s0g sigma vars x0 sg
    and gammaM :: "'M \<Rightarrow> store set" +
  assumes call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> (FunctionEntry p,
              cs_route k u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> (cont, c1) \<in> vars"
begin

sublocale routed: routed_context_base_hetero S gammaDG gs "compile_prog Pi ps" Global
  "cs_route k" bot0 s0d s0g sigma vars x0 sg Seed
  "static_resolve (compile_prog Pi ps)" gammaM "cs_context k"
proof unfold_locales
  show "finite (calls (compile_prog Pi ps))" using compile_prog_finite by simp
next
  show "\<And>p ctx. Seed p ctx \<noteq> Global" by simp
  fix u ctx dst pars args p cont s
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont)
            \<in> calls (compile_prog Pi ps)"
    and "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr Global)))"
  then show "p \<in> set (static_resolve (compile_prog Pi ps) cont u
                        (CallEdge dst pars args) (locals (sigma (Inl (u, ctx)))))"
    by (simp add: static_resolve_iff compile_prog_finite)
next
  fix u ctx dst pars args p cont s
  show "cs_route k u ctx (entered S Global sigma
            (call_info_of (CallEdge dst pars args) p) (Inl (u, ctx)))
          (CallEdge dst pars args)
          = cs_context k u ctx (call_enter gs (CallEdge dst pars args) s)"
    by (rule cs_route_context_agree)
next
  fix u ctx dst pars args p cont
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps)"
  then have "(FunctionEntry p,
                cs_route k u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
               \<in> vars"
    by (rule call_fwd)
  then show "(FunctionEntry p,
                cs_route k u ctx (entered S Global sigma
                    (call_info_of (CallEdge dst pars args) p) (Inl (u, ctx)))
                  (CallEdge dst pars args))
               \<in> vars"
    by (simp add: cs_route_def)
next
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

text \<open>CALL and COMB, at the call-string instance: the callee entry state published under
  the routed context is sound, and a return combine at the caller's own context is sound.
  Both are \<^locale>\<open>routed_context_base_hetero\<close>'s theorems, re-exported here so a
  concrete instance cites them without naming the sublocale.\<close>

lemmas routed_context_call = routed.routed_context_call
lemmas routed_context_comb = routed.routed_context_comb
lemmas activation_collect_sound = routed.activation_collect_dg_sound

end

end
