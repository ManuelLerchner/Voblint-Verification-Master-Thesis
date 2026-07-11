section \<open>Recursive global returns to main via rehydration --- no return values\<close>

theory Example_Interval_Recursion_Rehydrate
  imports
    Voblint_Formalization.Example_Interval_Recursion_Convergence
    Voblint_Formalization.Exec_Ivl_Cmp_Seed_Rehydrate_Run
begin

text \<open>
  \<^bold>\<open>The point.\<close>  The recursive counter of
  \<^theory>\<open>Voblint_Formalization.Example_Interval_Recursion_Convergence\<close> increments the
  \<^emph>\<open>global\<close> \<open>G\<close> to 3 and returns.  Concretely \<^const>\<open>combine_states\<close> (\<open><s|t>\<close>) already
  carries the callee's globals back --- caller locals, callee globals --- so \<open>main\<close>
  ends with \<open>G = 3\<close> with no \<open>return\<close>, no \<open>RET\<close>, no \<open>x := f()\<close>.  The missing value in the
  clean graph was a \<^emph>\<open>combine\<close> limitation, not a language one.

  \<^bold>\<open>Why the clean solve showed \<open>bot\<close>.\<close>  The clean seeded combine
  \<^const>\<open>ivl_combine_rread\<close> returns \<^const>\<open>restrict_local_st\<close> of the merged result,
  \<^emph>\<open>stripping\<close> the globals from the returned caller local.  The callee's global effect
  is published into the context-keyed \<^emph>\<open>Side\<close> slot but never folded back into the
  caller continuation, so the local \<open>G\<close> at \<open>main\<close>'s continuation is \<^const>\<open>bot\<close>
  (\<open>rdiv_clean_strips_global_at_main\<close>).

  \<^bold>\<open>The fix: rehydration.\<close>  \<^const>\<open>ivl_combine_rehydrate\<close> (Goblint's \<open>Spec.combine\<close>)
  rebuilds the caller continuation as \<^const>\<open>combine_abs_st\<close> --- caller locals,
  \<^emph>\<open>callee globals\<close> --- the abstract mirror of \<open><s|t>\<close>.  Re-solving the \<^emph>\<open>same\<close> CFG with
  it carries \<open>G = [3,3]\<close> up the entire recursive return chain
  (\<open>rdiv_rehyd_return_chain\<close>) all the way to \<open>main\<close>'s continuation
  (\<open>rdiv_rehyd_returns_global_to_main\<close>).  The enter side, the transfer, and the context
  selector are all unchanged; only the returned continuation keeps the callee globals
  instead of discarding them.
\<close>

subsection \<open>Re-solving the recursion with the rehydrating combine\<close>

definition rdiv_rehyd_eqs :: "(pp \<times> ivl st, ivl st, ivl st) eqsT" where
  "rdiv_rehyd_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. ivl_combine_rehydrate cc ex c)
     restrict_global_st rdiv_cfg ivl_etf_clean_st bot cinit_ivl_st"

definition rdiv_rehyd_solution ::
  "(pp \<times> ivl st) set \<times> ((pp \<times> ivl st) + ivl st \<Rightarrow> ivl st)" where
  "rdiv_rehyd_solution = TD_side_always_join_Interp_solve rdiv_rehyd_eqs (cfg_exit rdiv_cfg, bot)"

text \<open>The exact (widening-free) rehydrating solve terminates on the same bounded recursion.\<close>
lemma rdiv_rehyd_runs: "fst rdiv_rehyd_solution \<noteq> {}"
  unfolding rdiv_rehyd_solution_def rdiv_rehyd_eqs_def rdiv_cfg_def rdiv_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The clean combine strips the returned global; rehydration carries it back\<close>

text \<open>Clean combine: \<open>main\<close>'s continuation (node 11, context \<^const>\<open>bot\<close>) has local \<open>G =\<close>
  \<^const>\<open>bot\<close> --- the callee's global effect was stripped from the \<^const>\<open>Answer\<close> and left
  in the context-keyed Side slot.\<close>
lemma rdiv_clean_strips_global_at_main:
  "lookup_st (snd rdiv_clean_solution (Inl (11, bot))) ''G'' = bot"
  unfolding rdiv_clean_solution_def rdiv_clean_eqs_def rdiv_cfg_def rdiv_prog_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>Rehydrating combine: the callee's global \<open>G = [3,3]\<close> flows back to the very same
  node --- the value the clean graph showed as \<open>[0,0]\<close> / \<^const>\<open>bot\<close>.\<close>
lemma rdiv_rehyd_returns_global_to_main:
  "lookup_st (snd rdiv_rehyd_solution (Inl (11, bot))) ''G'' = Ivl (Fin 3) (Fin 3)"
  unfolding rdiv_rehyd_solution_def rdiv_rehyd_eqs_def rdiv_cfg_def rdiv_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The return chain: every recursive activation carries \<open>[3,3]\<close> upward\<close>

text \<open>At each \<open>f\<close> activation's continuation (node 4) the rehydrated caller local carries
  the callee's returned \<open>G = [3,3]\<close>: the deepest live call \<open>f @ [3,3]\<close> exits with
  \<open>G = [3,3]\<close>, and rehydration hands it to \<open>f @ [2,2]\<close>, \<open>f @ [1,1]\<close>, \<open>f @ [0,0]\<close>, and
  finally \<open>main\<close> in turn --- the globals-only return chain, no explicit return.\<close>
lemma rdiv_rehyd_return_chain:
  "lookup_st (snd rdiv_rehyd_solution (Inl (4, rdiv_ctxk 0))) ''G'' = Ivl (Fin 3) (Fin 3)
   \<and> lookup_st (snd rdiv_rehyd_solution (Inl (4, rdiv_ctxk 1))) ''G'' = Ivl (Fin 3) (Fin 3)
   \<and> lookup_st (snd rdiv_rehyd_solution (Inl (4, rdiv_ctxk 2))) ''G'' = Ivl (Fin 3) (Fin 3)"
  unfolding rdiv_rehyd_solution_def rdiv_rehyd_eqs_def rdiv_cfg_def rdiv_prog_def rdiv_ctxk_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The rehydrated run is a genuine solver post-fixpoint\<close>

text \<open>
  \<^bold>\<open>How was the strip spine ``sound'' with the missing rehydrate?\<close>  It was not proved
  sound at return nodes.  The generic context-sliced soundness theorem
  \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close> carries the return combine as an
  obligation: originally the raw \<open>COMB\<close> premise (\<open><s|t> \<in> \<lbrakk>sg (Inl ret)\<rbrakk>\<close>), now the
  abstract bound \<open>COMB_BOUND\<close> (\<open>\<langle>caller|callee\<rangle> \<le> sg (Inl ret)\<close>,
  \<open>ivl_clean_ctx_collect_rread_head_bound\<close>).  The strip combine
  \<^const>\<open>ivl_combine_rread\<close> cannot discharge it once a callee global is read back: it
  stores that global at \<^const>\<open>bot\<close> in the returned local (\<open>rdiv_clean_strips_global_at_main\<close>),
  so the concrete return \<open><s|t>\<close> --- carrying \<open>G = 3\<close> --- escapes the concretisation.
  The convergence example only ever asserted executable \<open>eval\<close> values; it never
  instantiated the soundness theorem, so no false theorem was proved --- the return
  obligation was simply left open.  Rehydration discharges it exactly
  (\<open>rehydrate_caller_continuation_sound\<close>, the \<^const>\<open>combine_abs_st\<close> return slot).

  \<^bold>\<open>The generic solver post-fixpoint, applied.\<close>  The vendored side solver's
  @{thm [source] TD_side_always_join_Interp.partial_post_solution} certifies any
  terminating solve as a \<^const>\<open>part_post_solution\<close>.  Termination is discharged by
  execution (\<^const>\<open>TD_side_always_join_Interp_solve_c\<close> returns a result, so the
  program lies in the solver's domain via
  @{thm [source] TD_side_always_join_Interp.term_equivalence}).  No program-specific
  reasoning: the same generic theorem that closes every terminating run.
\<close>

lemma rdiv_rehyd_solve_c_some:
  "TD_side_always_join_Interp_solve_c rdiv_rehyd_eqs (cfg_exit rdiv_cfg, bot) \<noteq> None"
  unfolding rdiv_rehyd_eqs_def rdiv_cfg_def rdiv_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

lemma rdiv_rehyd_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(ivl st) TYPE(ivl st)
     rdiv_rehyd_eqs (cfg_exit rdiv_cfg, bot)"
  unfolding TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using rdiv_rehyd_solve_c_some by simp

theorem rdiv_rehyd_post_fixpoint:
  "part_post_solution rdiv_rehyd_eqs (cfg_exit rdiv_cfg, bot)
     (snd rdiv_rehyd_solution) (fst rdiv_rehyd_solution)"
  using TD_side_always_join_Interp.partial_post_solution
      [OF rdiv_rehyd_solve_dom, of "fst rdiv_rehyd_solution" "snd rdiv_rehyd_solution"]
  unfolding rdiv_rehyd_solution_def by simp

text \<open>
  The reached-unknown consequence: at every solved unknown the reassembled
  right-hand side --- the clean edge transfers \<^emph>\<open>and\<close> the rehydrated return combine
  \<^const>\<open>combine_abs_st\<close> --- is dominated by the stored local slot.  This is
  \<open>EDGE_BOUND\<close>, \<open>COMB_BOUND\<close> and the seed bound \<^emph>\<open>uniformly\<close>, read straight off the
  generic post-fixpoint; the return combine is now an order fact, not a raw
  \<open><s|t>\<close> obligation.
\<close>

corollary rdiv_rehyd_rhs_dominated:
  assumes "(v, ctx) \<in> fst rdiv_rehyd_solution"
  shows "traverse_rhs (rdiv_rehyd_eqs (v, ctx)) (snd rdiv_rehyd_solution)
           \<le> snd rdiv_rehyd_solution (Inl (v, ctx))"
  using part_post_solution_imp_se_constraint_holds[OF rdiv_rehyd_post_fixpoint assms]
  by (simp add: se_constraint_holds_def)

text \<open>At \<open>main\<close>'s continuation (node 11, context \<^const>\<open>bot\<close>) --- the exact node where the
  strip combine stranded \<open>G\<close> at \<^const>\<open>bot\<close> --- the rehydrated return right-hand side is
  dominated by the stored slot, and that slot carries the callee's \<open>G = [3,3]\<close>
  (\<open>rdiv_rehyd_returns_global_to_main\<close>).  A genuine, generic-post-fixpoint-backed
  return-node soundness witness for the rehydrating combine.\<close>

lemma rdiv_rehyd_main_cont_reached:
  "(11, bot::ivl st) \<in> fst rdiv_rehyd_solution"
  unfolding rdiv_rehyd_solution_def rdiv_rehyd_eqs_def rdiv_cfg_def rdiv_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

corollary rdiv_rehyd_main_return_sound:
  "traverse_rhs (rdiv_rehyd_eqs (11, bot)) (snd rdiv_rehyd_solution)
     \<le> snd rdiv_rehyd_solution (Inl (11, bot))"
  by (rule rdiv_rehyd_rhs_dominated[OF rdiv_rehyd_main_cont_reached])

text \<open>
  \<^bold>\<open>Scope of the generic closure --- exactly what remains.\<close>  The \<^emph>\<open>return\<close> half is now
  closed generically.  The \<open>COMB\<close> black box is gone from
  \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close> (replaced by the \<^const>\<open>combine_abs\<close>
  bound the rehydration meets); the combine summand of \<^emph>\<open>any\<close> seeded post-solution is
  dominated by the return slot (\<open>Exec_Cmp_Bridge.seeded_clean_comb_bound\<close>, generic);
  and that summand is the \<^const>\<open>combine_abs_st\<close> continuation
  (\<open>traverse_ivl_combine_rehydrate\<close>).  With the routing selector
  \<open>rt cl ctx _ = restrict_global_st (snd rdiv_rehyd_solution (Inl (cl, ctx)))\<close> --- a
  legitimate instantiation of the kernel's \<^emph>\<open>free\<close> \<open>rt\<close> parameter that matches the
  generator's callee key exactly --- there is no context-reification obstruction.

  Lifting the reached-RHS domination to the collecting-semantics conclusion
  \<open>cfg_collect_ctx rdiv_cfg \<dots> \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>\<close> via
  \<open>ivl_clean_ctx_collect_rread_head_bound\<close> is \<^emph>\<open>not\<close> mere plumbing.  Three obligations
  are mechanical (an interval copy of \<open>seeded_clean_edge_bound\<close>; the
  \<^typ>\<open>ivl st\<close>-to-\<^typ>\<open>ivl abs_state\<close> transport
  \<open>part_post_solution_cmp_seed_st_to_abs_eff\<close> instantiated at the rehydrate combine;
  the \<^const>\<open>combine_abs\<close> assembly from the two lemmas above).  \<^bold>\<open>Two are genuinely
  missing generic results\<close>, unclosed for \<^emph>\<open>every\<close> domain (Sign included), not specific
  to interval or to rehydration:

    \<^item> \<^bold>\<open>ENTRY / PROC_ENTRY \<open>\<gamma>\<close>-cover.\<close>  That the seed \<^const>\<open>restrict_global_st\<close>
      covers the concrete entering stores at each context.  Only program-specific
      witnesses exist (Sign's \<open>seed_clean_sound_on_prog2\<close>); no generic seed-soundness
      lemma.

    \<^item> \<^bold>\<open>ENTER_MONO kernel-connection.\<close>  From the point-routing \<^emph>\<open>equation\<close>
      (\<open>point_ivl_gamma_exact\<close> / the \<open>iseed_slots_point\<close> analogue) to the kernel
      obligation \<open>cmp (f (enter_state s)) (rt cl ctx (sg (Inl (cl, ctx))))\<close> with the
      generator's concrete \<open>cmp\<close> / \<open>f\<close> / \<open>rt\<close>.  \<open>Exec_Ivl_Seed_EnterMono\<close>
      proves the routing equation in isolation but never wires it to this obligation.

  The smallest single missing generic lemma is a \<^emph>\<open>generator-to-kernel instantiation\<close>
  --- one lemma over an arbitrary \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> run reducing the
  kernel's \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> / \<open>ENTER_MONO\<close> to (a) seed \<open>\<gamma>\<close>-soundness on the
  initial stores and (b) the eval-checkable point-routing premise.  It is deliberately
  not discharged here by a program-specialised reachable-context proof, and it blocks
  the final lift for Sign and interval alike.
\<close>

subsection \<open>Context-clustered GraphViz of the rehydrated run\<close>

text \<open>The same six context clusters as the clean graph
  (\<^theory>\<open>Voblint_Formalization.Example_Interval_Recursion_Convergence\<close>), but each
  node's local \<open>G\<close> is read from \<^const>\<open>rdiv_rehyd_solution\<close>.  The difference is legible
  at the return nodes: where the clean graph shows \<^const>\<open>bot\<close> for the returned local
  \<open>G\<close>, the rehydrated graph shows the callee's \<open>[3,3]\<close> handed back up the
  \<open>fBot \<rightarrow> f3 \<rightarrow> f2 \<rightarrow> f1 \<rightarrow> f0 \<rightarrow> main\<close> return chain.  The cluster layout, enter chain,
  call, and return wiring are reused verbatim from the convergence example.\<close>

definition rdiv_rehyd_node_label :: "pp \<times> rdiv_rctx \<Rightarrow> string" where
  "rdiv_rehyd_node_label = ctx_debug_state_node_label rdiv_cfg [''G'']
     (\<lambda>pc. case pc of (p, r) \<Rightarrow> snd rdiv_rehyd_solution (Inl (p, rdiv_rctx_ctx r)))"

definition rdiv_rehyd_globals :: "rdiv_rctx \<Rightarrow> string" where
  "rdiv_rehyd_globals r =
     ''G = '' @ show_val (lookup_st (snd rdiv_rehyd_solution (Inr (rdiv_rctx_ctx r))) ''G'')"

definition rdiv_rehyd_dot :: String.literal where
  "rdiv_rehyd_dot = String.implode
     (ctx_debug_graphviz_with_globals
        rdiv_rctx_key rdiv_rctx_label rdiv_rehyd_globals rdiv_rehyd_node_label
        (\<lambda>_. ''shape=box'')
        [RMain, RF0, RF1, RF2, RF3, RFbot]
        rdiv_gv_nodes rdiv_gv_intra rdiv_gv_calls rdiv_gv_returns)"

text \<open>@{command ML_val} \<open>writeln (@{code rdiv_rehyd_dot})\<close> emits the DOT source: the
  \<open>f\<close> return nodes now carry \<open>G = [3,3]\<close> back to \<open>main\<close>'s continuation, the value the
  clean graph stranded at \<^const>\<open>bot\<close>.\<close>

ML_val \<open>writeln (@{code rdiv_rehyd_dot})\<close>

end
