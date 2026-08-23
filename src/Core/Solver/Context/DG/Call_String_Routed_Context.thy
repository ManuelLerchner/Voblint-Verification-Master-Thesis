theory Call_String_Routed_Context
  imports Routed_Context Call_String_Context "Voblint_CFG.VIMP_Proc_to_CFG"
begin

section \<open>Call-string routing as a routed-context instance\<close>

text \<open>
  \<^locale>\<open>routed_context_hetero\<close> at \<open>route := cs_route k\<close>, \<open>enterc := cs_context k\<close>,
  \<open>gk0 := Global\<close> and \<open>seed_key := Seed\<close>, over the CFG of a compiled program. Four of the
  six obligations that specialization leaves are then facts about the routing policy or
  about \<^const>\<open>compile_prog\<close> alone --- nothing about which program was compiled --- and
  are discharged here once and for all \<open>k\<close>:

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
  dg_ctx_activation_base S gamma_dg_base gs "compile_prog Pi ps mnm main" Global "cs_route k"
    "routed_cmb_g S Global Seed" "routed_extra_g Seed Global"
    bot0 s0d s0g sigma vars x0 sg gamma_state_lift
  for S :: "('a::sound_domain abs_state lifted, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
    and k :: nat
    and bot0 s0d s0g sigma vars x0 sg +
  assumes call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps mnm main)
       \<Longrightarrow> (FunctionEntry p,
              cs_route k u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps mnm main)
       \<Longrightarrow> (cont, c1) \<in> vars"
begin

sublocale routed: routed_context_hetero S gs "compile_prog Pi ps mnm main" Global
  "cs_route k" bot0 s0d s0g sigma vars x0 sg Seed "cs_context k"
proof unfold_locales
  show "finite (calls (compile_prog Pi ps mnm main))" using compile_prog_finite by simp
next
  show "\<And>p ctx. Seed p ctx \<noteq> Global" by simp
next
  fix u ctx dst pars args p cont s
  show "cs_route k u ctx (enter_local S pars args (locals (sigma (Inl (u, ctx))))
            (globs (sigma (Inr Global)))) (CallEdge dst pars args)
          = cs_context k u ctx (call_enter gs (CallEdge dst pars args) s)"
    by (rule cs_route_context_agree)
next
  fix u ctx dst pars args p cont
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps mnm main)"
  then have "(FunctionEntry p,
                cs_route k u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
               \<in> vars"
    by (rule call_fwd)
  then show "(FunctionEntry p,
                cs_route k u ctx (enter_local S pars args (locals (sigma (Inl (u, ctx))))
                    (globs (sigma (Inr Global)))) (CallEdge dst pars args))
               \<in> vars"
    by (simp add: cs_route_def)
next
  fix cl c1 dst pars args p cont
  assume "(cl, c1) \<in> vars"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps mnm main)"
  then show "(cont, c1) \<in> vars" by (rule comb_fwd)
next
  fix cl s es dst pars args p cont
  assume ces: "call_enter_store gs (compile_prog Pi ps mnm main) cl s es"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont)
               \<in> calls (compile_prog Pi ps mnm main)"
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  then show "es = call_enter gs (CallEdge dst pars args) s" using es_eq by simp
qed

text \<open>CALL and COMB, at the call-string instance: the callee entry state published under
  the routed context is sound, and a return combine at the caller's own context is sound.
  Both are \<^locale>\<open>routed_context_hetero\<close>'s theorems, re-exported here so a concrete
  instance cites them without naming the sublocale.\<close>

lemmas routed_context_call = routed.routed_context_call
lemmas routed_context_comb = routed.routed_context_comb

end

end
