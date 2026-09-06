theory Entry_State_Routed_Context
  imports "Voblint_Framework.Routed_Context" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Entry-state routing as a routed-context instance\<close>

text \<open>
  \<^locale>\<open>routed_context_base_hetero\<close> at a route that reads the entered callee state, with
  \<open>R := routed_entry_context_rel alts gammaDG sigma gk0 route\<close>, over the CFG of a compiled
  program and at whichever carrier \<open>S\<close> is stated over.  The route is a parameter because one
  policy is spelled differently per carrier: \<^const>\<open>formals_route_lifted_gen\<close> projects the
  formals out of an abstract state, an executable instance projects them out of its own
  quotient state.  Unlike \<open>Call_String_Routed_Context\<close>'s \<open>call_string_routed_context\<close>, no
  single seed-key datatype is shared across entry-state instances: each is keyed by its own
  carrier's value list, so \<open>gk0\<close> and \<open>seed_key\<close> stay genuine locale parameters.

  The entry operation is pure: \<open>alts ci d\<close> is the list of alternatives the specification
  answers for call \<open>ci\<close> at caller state \<open>d\<close>, and \<open>enter_pure\<close> says the specification's own
  \<open>enter\<^sup>#\<close> is exactly that list handed to its continuation.  Everything the routed locale
  asks about \<open>R\<close> then reduces to two facts about \<open>alts\<close>: its alternatives cover every
  concrete call at a covered call site (\<open>enter_cover\<close>), and the solver visited the callee
  entry at every context an alternative routes to (\<open>call_fwd\<close>).  A one-alternative
  specification instantiates \<open>alts ci d = [(d, en ci d)]\<close>; one that splits a call into
  several alternatives, possibly overlapping, instantiates it with the longer list and
  nothing else changes.

  Two of the routed obligations are facts about \<^const>\<open>compile_prog\<close> alone and are
  discharged here once: \<open>finC\<close> (\<open>compile_prog_finite\<close>) and \<open>calls_unique\<close>
  (\<open>compile_prog_calls_source_unique\<close>).  \<open>seed_key_ne_gk0\<close>, \<open>call_fwd\<close> and \<open>comb_fwd\<close>
  remain per-instance assumptions: the first is datatype distinctness of the instance's
  seed key, the other two say the solved variable set covers a routed callee entry or return
  continuation, a property of the program together with what the solver explored.
\<close>

locale entry_state_routed_context =
  dg_ctx_activation_base S gammaDG gs "compile_prog Pi ps" gk0 route
    "routed_call_tree S gk0 seed_key (static_resolve (compile_prog Pi ps)) is_bot"
    "routed_entry_seed_tree seed_key"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
    and gk0 :: 'k
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and bot0 s0d s0g sigma vars x0 sg
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and is_bot :: "'D \<Rightarrow> bool"
    and gammaM :: "'M \<Rightarrow> store set"
    and alts :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D enter_result list" +
  assumes seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and is_bot_bot: "is_bot bot"
    and is_bot_sound: "\<And>d gv. is_bot d \<Longrightarrow> gammaDG d gv = {}"
    and enter_pure: "\<And>ci. enter\<^sup># S ci = local_enter_transfer (alts ci)"
    and enter_cover:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))
       \<Longrightarrow> entry_pairs_cover (\<lambda>d. gammaDG d (globs (sigma (Inr gk0)))) s
             (call_enter gs (CallEdge dst pars args) s)
             (alts (call_info_of (CallEdge dst pars args) p) (locals (sigma (Inl (u, ctx)))))"
    and call_fwd:
    "\<And>u ctx dst pars args p cont cont' entry.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> (cont', entry) \<in> set (alts (call_info_of (CallEdge dst pars args) p)
                                  (locals (sigma (Inl (u, ctx)))))
       \<Longrightarrow> \<not> is_bot entry
       \<Longrightarrow> (FunctionEntry p, route u ctx entry (CallEdge dst pars args)) \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> (cont, c1) \<in> vars"
begin

text \<open>The context relation this instance keys its collecting semantics by.\<close>
abbreviation entry_context_rel :: "'c call_context_rel" where
  "entry_context_rel \<equiv> routed_entry_context_rel alts gammaDG sigma gk0 route"

sublocale routed: routed_context_base_hetero S gammaDG gs "compile_prog Pi ps" gk0
  route bot0 s0d s0g sigma vars x0 sg seed_key
  "static_resolve (compile_prog Pi ps)" is_bot gammaM entry_context_rel
proof unfold_locales
  show "finite (calls (compile_prog Pi ps))" using compile_prog_finite by simp
next
  show "calls_source_unique (compile_prog Pi ps)"
    unfolding calls_source_unique_def using compile_prog_calls_source_unique by blast
next
  show "\<And>p ctx. seed_key p ctx \<noteq> gk0" by (rule seed_key_ne_gk0)
next
  show "is_bot bot" by (rule is_bot_bot)
next
  show "\<And>d gv. is_bot d \<Longrightarrow> gammaDG d gv = {}" by (rule is_bot_sound)
next
  fix u ctx dst pars args p cont s
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
  then show "p \<in> set (static_resolve (compile_prog Pi ps) cont u
                        (CallEdge dst pars args) (locals (sigma (Inl (u, ctx)))))"
    by (simp add: compile_prog_finite)
next
  fix u ctx dst pars args p cont s ctx'
  assume covV: "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
    and Rc: "entry_context_rel u ctx (call_info_of (CallEdge dst pars args) p) s
               (call_enter gs (CallEdge dst pars args) s) ctx'"
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (sigma (Inl (u, ctx)))"
  from Rc obtain cont' entry
    where mem: "(cont', entry) \<in> set (alts ?ci ?d)"
      and ccov: "s \<in> gammaDG cont' (globs (sigma (Inr gk0)))"
      and ecov: "call_enter gs (CallEdge dst pars args) s
                   \<in> gammaDG entry (globs (sigma (Inr gk0)))"
      and req0: "ctx' = route u ctx entry (CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci))"
    by (rule routed_entry_context_relE)
  have req: "route u ctx entry (CallEdge dst pars args) = ctx'" using req0 by simp
  have not_bot: "\<not> is_bot entry"
    using ecov is_bot_sound by fastforce
  have Rr: "enter_runs (enter\<^sup># S ?ci) (mk_dg_man ?d (\<lambda>_. gk0)) sigma (alts ?ci ?d) bot"
    unfolding enter_pure by (rule enter_runs_local_enter_transfer_mk_dg_man)
  have D: "enter_deps (enter\<^sup># S ?ci) (mk_dg_man ?d (\<lambda>_. gk0)) sigma (alts ?ci ?d) {}"
    unfolding enter_pure by (rule enter_deps_local_enter_transfer_mk_dg_man)
  show "\<exists>pairs pub deps cont' entry.
             enter_runs (enter\<^sup># S ?ci) (mk_dg_man ?d (\<lambda>_. gk0)) sigma pairs pub
           \<and> enter_deps (enter\<^sup># S ?ci) (mk_dg_man ?d (\<lambda>_. gk0)) sigma pairs deps
           \<and> (cont', entry) \<in> set pairs
           \<and> s \<in> gammaDG cont' (globs (sigma (Inr gk0)))
           \<and> call_enter gs (CallEdge dst pars args) s
               \<in> gammaDG entry (globs (sigma (Inr gk0)))
           \<and> route u ctx entry (CallEdge dst pars args) = ctx'
           \<and> (FunctionEntry p, ctx') \<in> vars"
    using Rr D mem ccov ecov req call_fwd[OF covV ce mem not_bot] by blast
next
next
  fix u ctx dst pars args p cont s
  assume covV: "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0)))"
  show "\<exists>ctx'. entry_context_rel u ctx (call_info_of (CallEdge dst pars args) p) s
                 (call_enter gs (CallEdge dst pars args) s) ctx'"
  proof (rule routed_entry_context_rel_total)
    show "entry_pairs_cover (\<lambda>d. gammaDG d (globs (sigma (Inr gk0)))) s
            (call_enter gs (CallEdge dst pars args) s)
            (alts (call_info_of (CallEdge dst pars args) p) (locals (sigma (Inl (u, ctx)))))"
      by (rule enter_cover[OF covV ce sin])
  qed
next
  fix cl c1 dst pars args p cont
  assume "(cl, c1) \<in> vars"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
  then show "(cont, c1) \<in> vars" by (rule comb_fwd)
qed

text \<open>CALL and COMB, at the entry-state instance: the callee entry state published under
  every admitted context is sound, and a return combine at the caller's own context is
  sound.  Both are \<^locale>\<open>routed_context_base_hetero\<close>'s theorems, re-exported here so a
  concrete instance cites them without naming the sublocale.\<close>

lemmas routed_context_call = routed.routed_context_call
lemmas routed_context_comb = routed.routed_context_comb
lemmas activation_collect_sound = routed.activation_collect_dg_sound

end

end
