theory Entry_State_Routed_Context
  imports Routed_Context "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Entry-state routing as a routed-context instance\<close>

text \<open>
  \<^locale>\<open>routed_context_hetero\<close> at \<open>route := formals_route_lifted_gen S\<close>,
  \<open>enterc := route_enterc_of_sigma (formals_route_lifted_gen S) sigma g\<close>, over the CFG
  of a compiled program. Unlike \<open>Call_String_Routed_Context\<close>'s own
  \<open>call_string_routed_context\<close> -- which hardcodes \<open>Call_String_Context\<close>'s
  one canonical \<open>call_string_gk\<close> seed-key datatype, shared by every CallString instance --
  no single seed-key datatype is shared across EntryState instances: each domain's own
  routed context is keyed by \<open>that domain's own abstract carrier\<close> (\<open>ivl list\<close>, \<open>sign list\<close>,
  ...), so \<open>gk0\<close>/\<open>seed_key\<close> stay genuine locale parameters here, mirroring
  \<open>Routed_Context_Unit\<close>'s own \<open>unit_routed_context\<close>'s posture on that same axis
  rather than \<open>call_string_routed_context\<close>'s.

  Three of the five obligations \<^locale>\<open>routed_context_hetero\<close> leaves are then facts about
  the routing policy or about \<^const>\<open>compile_prog\<close> alone -- nothing about which domain,
  program, or seed-key type -- and are discharged here once and for all \<open>S\<close>:

    \<bullet> \<open>finC\<close> holds for every \<^const>\<open>compile_prog\<close> output (\<open>compile_prog_finite\<close>);
    \<bullet> \<open>call_enter_store_agree\<close> is call-source uniqueness for every
      \<^const>\<open>compile_prog\<close> output (\<open>compile_prog_calls_source_unique\<close>);
    \<bullet> \<open>route_enterc_agree\<close> is \<open>route_enterc_of_sigma_agree\<close>
      (\<^theory>\<open>Voblint_Core.Routed_Context\<close>), generic in \<^emph>\<open>any\<close> \<open>route\<close> reading its
      caller state from \<open>sigma\<close> -- unlike \<open>call_string_routed_context\<close>'s own
      \<open>cs_route_context_agree\<close>, this does not depend on \<open>route\<close> ignoring its state
      argument, since \<^const>\<open>formals_route_lifted_gen\<close> genuinely does not.

  \<open>seed_key_ne_gk0\<close> stays a genuine per-instance assumption (a fact about the concrete
  seed-key datatype an instance supplies, matching \<open>unit_routed_context\<close>'s own choice),
  and so do \<open>call_fwd\<close>/\<open>comb_fwd\<close>: each says the solved variable set covers a
  particular routed callee entry or return continuation, a property of the program
  together with what the solver actually explored. An instance supplies them; no
  generic argument can.
\<close>

locale entry_state_routed_context =
  dg_ctx_activation_base S gamma_dg_base gs "compile_prog Pi ps main_name main" gk0
    "formals_route_lifted_gen S"
    "routed_cmb_g S gk0 seed_key (static_resolve (compile_prog Pi ps main_name main))"
    "routed_extra_g seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg gamma_state_lift
  for S :: "('a::sound_domain abs_state lifted, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and main_name :: pname and main :: com
    and gk0 :: 'k
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'a list \<Rightarrow> 'k" +
  assumes seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps main_name main)
       \<Longrightarrow> (FunctionEntry p,
              formals_route_lifted_gen S u ctx
                (enter_local S pars args (locals (sigma (Inl (u, ctx))))
                    (globs (sigma (Inr gk0)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps main_name main)
       \<Longrightarrow> (cont, c1) \<in> vars"
begin

sublocale routed: routed_context_hetero S gs "compile_prog Pi ps main_name main" gk0
  "formals_route_lifted_gen S" bot0 s0d s0g sigma vars x0 sg seed_key
  "static_resolve (compile_prog Pi ps main_name main)"
  "route_enterc_of_sigma S (formals_route_lifted_gen S) sigma gk0 (compile_prog Pi ps main_name main)"
proof unfold_locales
  show "finite (calls (compile_prog Pi ps main_name main))" using compile_prog_finite by simp
next
  show "\<And>p ctx. seed_key p ctx \<noteq> gk0" by (rule seed_key_ne_gk0)
next
  fix u ctx dst pars args p cont s
  assume "(u, CallEdge dst pars args, FunctionEntry p, cont)
            \<in> calls (compile_prog Pi ps main_name main)"
  then show "p \<in> set (static_resolve (compile_prog Pi ps main_name main) cont u
                        (CallEdge dst pars args) (locals (sigma (Inl (u, ctx)))))"
    by (simp add: static_resolve_iff compile_prog_finite)
next
  fix u ctx dst pars args p cont s
  assume "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps main_name main)"
  have fin: "finite (calls (compile_prog Pi ps main_name main))" using compile_prog_finite by blast
  show "formals_route_lifted_gen S u ctx
            (enter_local S pars args (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
            (CallEdge dst pars args)
          = route_enterc_of_sigma S (formals_route_lifted_gen S) sigma gk0
              (compile_prog Pi ps main_name main) u ctx (call_enter gs (CallEdge dst pars args) s)"
    by (rule route_enterc_of_sigma_agree[OF fin compile_prog_calls_source_unique ce])
next
  fix u ctx dst pars args p cont
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps main_name main)"
  then show "(FunctionEntry p,
                formals_route_lifted_gen S u ctx
                  (enter_local S pars args (locals (sigma (Inl (u, ctx))))
                      (globs (sigma (Inr gk0)))) (CallEdge dst pars args))
               \<in> vars"
    by (rule call_fwd)
next
  fix cl c1 dst pars args p cont
  assume "(cl, c1) \<in> vars"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps main_name main)"
  then show "(cont, c1) \<in> vars" by (rule comb_fwd)
next
  fix cl s es dst pars args p cont
  assume ces: "call_enter_store gs (compile_prog Pi ps main_name main) cl s es"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont)
               \<in> calls (compile_prog Pi ps main_name main)"
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps main_name main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  then show "es = call_enter gs (CallEdge dst pars args) s" using es_eq by simp
qed

text \<open>CALL and COMB, at the entry-state instance: the callee entry state published under
  the routed context is sound, and a return combine at the caller's own context is sound.
  Both are \<^locale>\<open>routed_context_hetero\<close>'s theorems, re-exported here so a concrete
  instance cites them without naming the sublocale.\<close>

lemmas routed_context_call = routed.routed_context_call
lemmas routed_context_comb = routed.routed_context_comb

end

end

