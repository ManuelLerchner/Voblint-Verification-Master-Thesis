theory Call_String_Routed_Context
  imports
    Compiled_Routed_Equations
    "Voblint_Framework.Call_String_Context"
begin

section \<open>Telling activations apart by how they were called\<close>

text \<open>
  A call string is the last \<open>k\<close> call sites on the stack. Keying an analysis by one
  means a procedure entered from two places is analysed twice, separately, instead
  of once at the join of both --- and entered from more than \<open>k\<close> levels deep, the
  oldest sites drop off and those activations merge again.

  This theory says that policy is a legal routing for the generic spine, and pays
  once, for every \<open>k\<close> and every domain, the part of that bill which depends only on
  the policy and on the shape of a compiled program:

    \<^item> \<open>finC\<close> holds for every \<^const>\<open>compile_prog\<close> output (\<open>compile_prog_finite\<close>);
    \<^item> \<open>calls_unique\<close> is call-source uniqueness for every \<^const>\<open>compile_prog\<close>
      output (\<open>compile_prog_calls_source_unique\<close>);
    \<^item> \<open>seed_key_ne_gk0\<close> is datatype distinctness for \<^type>\<open>call_string_gk\<close>;
    \<^item> \<open>routed_entry_cover\<close>'s routing conjunct is \<^const>\<open>cs_route\<close> and
      \<^const>\<open>cs_context\<close> being the same closed term (\<open>cs_route_context_agree\<close>),
      independently of the entered value, so every context the relation admits is the
      one \<^const>\<open>cs_route\<close> computes on any alternative;
    \<^item> \<open>routed_entry_total\<close> is immediate: the graph of a function admits exactly one
      context per call.

  \<open>call_fwd\<close> and \<open>comb_fwd\<close> remain assumptions, and deliberately so: each says the solved
  variable set covers a particular routed callee entry or return continuation, which is a
  property of the program together with what the solver actually explored. An instance
  supplies them; no generic argument can.
\<close>

definition call_string_eqs_for ::
    "nat
      \<Rightarrow> (pp \<times> call_string, call_string_gk, unit,
           'D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec
      \<Rightarrow> cfg
      \<Rightarrow> 'D
      \<Rightarrow> (pp \<times> call_string, call_string_gk, ('D, 'G) dg_state) eqsT"
where
  "call_string_eqs_for k S g initial =
     compiled_routed_eqs_for Call_String_Context.Global
       Call_String_Context.Seed (cs_route k) S g initial bot"

text \<open>
  The constructor fixes the call-string routing, global and seed keys,
  compiled-program resolver, and bottom initialization. A domain supplies
  only its specification, graph, and initial local state.
\<close>

locale call_string_routed_context =
  dg_ctx_activation_base S gammaDG gs "compile_prog Pi ps" Global "cs_route k"
    "routed_call_tree S Global Seed (static_resolve (compile_prog Pi ps)) is_bot"
    "routed_entry_seed_tree Seed"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "(pp \<times> cfg_node list, call_string_gk, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
    and k :: nat
    and bot0 s0d s0g sigma vars x0 sg
    and is_bot :: "'D \<Rightarrow> bool"
    and gammaM :: "'M \<Rightarrow> store set" +
  assumes is_bot_bot: "is_bot bot"
    and is_bot_sound: "\<And>d gv. is_bot d \<Longrightarrow> gammaDG d gv = {}"
    and enter_complete:
    "\<And>u ctx dst pars args p cont s.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont)
             \<in> calls (compile_prog Pi ps)
       \<Longrightarrow> s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr Global)))
       \<Longrightarrow> \<exists>pairs pub deps.
             enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. Global)) sigma pairs pub
           \<and> enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. Global)) sigma pairs deps
           \<and> entry_pairs_cover (\<lambda>d. gammaDG d (globs (sigma (Inr Global)))) s
               (call_enter gs (CallEdge dst pars args) s) pairs"
    and call_fwd:
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
  "static_resolve (compile_prog Pi ps)" is_bot gammaM "call_context_rel_of_fun (cs_context k)"
proof unfold_locales
  show "finite (calls (compile_prog Pi ps))" using compile_prog_finite by simp
next
  show "calls_source_unique (compile_prog Pi ps)"
    unfolding calls_source_unique_def using compile_prog_calls_source_unique by blast
next
  show "\<And>p ctx. Seed p ctx \<noteq> Global" by simp
next
  show "is_bot bot" by (rule is_bot_bot)
next
  show "\<And>d gv. is_bot d \<Longrightarrow> gammaDG d gv = {}" by (rule is_bot_sound)
next
  fix u ctx dst pars args p cont s
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont)
            \<in> calls (compile_prog Pi ps)"
    and "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr Global)))"
  then show "p \<in> set (static_resolve (compile_prog Pi ps) cont u
                        (CallEdge dst pars args) (locals (sigma (Inl (u, ctx)))))"
    by (simp add: compile_prog_finite)
next
  fix u ctx dst pars args p cont s ctx'
  assume covV: "(u, ctx) \<in> vars"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont)
               \<in> calls (compile_prog Pi ps)"
    and sin: "s \<in> gammaDG (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr Global)))"
    and Rc: "call_context_rel_of_fun (cs_context k) u ctx (call_info_of (CallEdge dst pars args) p)
               s (call_enter gs (CallEdge dst pars args) s) ctx'"
  have ctx': "ctx' = cs_context k u ctx (call_enter gs (CallEdge dst pars args) s)"
    using Rc by simp
  obtain pairs pub deps
    where R: "enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
                (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. Global)) sigma pairs pub"
      and D: "enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
                (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. Global)) sigma pairs deps"
      and P: "entry_pairs_cover (\<lambda>d. gammaDG d (globs (sigma (Inr Global)))) s
                (call_enter gs (CallEdge dst pars args) s) pairs"
    using enter_complete[OF covV ce sin] by blast
  from P obtain cont' entry
    where mem: "(cont', entry) \<in> set pairs"
      and ccov: "s \<in> gammaDG cont' (globs (sigma (Inr Global)))"
      and ecov: "call_enter gs (CallEdge dst pars args) s
                   \<in> gammaDG entry (globs (sigma (Inr Global)))"
    by (rule entry_pairs_coverE)
  have req: "cs_route k u ctx entry (CallEdge dst pars args) = ctx'"
    unfolding ctx' by (rule cs_route_context_agree)
  have covE: "(FunctionEntry p, ctx') \<in> vars"
    using call_fwd[OF covV ce] req by (simp add: cs_route_def)
  show "\<exists>pairs pub deps cont' entry.
             enter_runs (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. Global)) sigma pairs pub
           \<and> enter_deps (enter\<^sup># S (call_info_of (CallEdge dst pars args) p))
               (mk_dg_man (locals (sigma (Inl (u, ctx)))) (\<lambda>_. Global)) sigma pairs deps
           \<and> (cont', entry) \<in> set pairs
           \<and> s \<in> gammaDG cont' (globs (sigma (Inr Global)))
           \<and> call_enter gs (CallEdge dst pars args) s
               \<in> gammaDG entry (globs (sigma (Inr Global)))
           \<and> cs_route k u ctx entry (CallEdge dst pars args) = ctx'
           \<and> (FunctionEntry p, ctx') \<in> vars"
    using R D mem ccov ecov req covE by blast
next
  fix u ctx dst pars args p cont s
  show "\<exists>ctx'. call_context_rel_of_fun (cs_context k) u ctx
                 (call_info_of (CallEdge dst pars args) p) s
                 (call_enter gs (CallEdge dst pars args) s) ctx'"
    by simp
next
  fix cl c1 dst pars args p cont
  assume "(cl, c1) \<in> vars"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls (compile_prog Pi ps)"
  then show "(cont, c1) \<in> vars" by (rule comb_fwd)
qed

text \<open>CALL and COMB, at the call-string instance: the callee entry state published under
  every admitted routed context is sound, and a return combine at the caller's own context
  is sound. Both are \<^locale>\<open>routed_context_base_hetero\<close>'s theorems, re-exported here
  so a concrete instance cites them without naming the sublocale; so is the
  activation-collect endpoint, now over \<open>call_context_rel_of_fun (cs_context k)\<close> and a
  \<open>startcontext\<close>.\<close>

lemmas routed_context_call = routed.routed_context_call
lemmas routed_context_comb = routed.routed_context_comb
lemmas activation_collect_sound = routed.activation_collect_dg_sound

end

end
