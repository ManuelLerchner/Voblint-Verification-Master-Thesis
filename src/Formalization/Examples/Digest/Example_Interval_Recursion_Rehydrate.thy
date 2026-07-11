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
