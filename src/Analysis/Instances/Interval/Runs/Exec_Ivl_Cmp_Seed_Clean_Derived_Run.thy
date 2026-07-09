theory Exec_Ivl_Cmp_Seed_Clean_Derived_Run
  imports Exec_Ivl_Cmp_Seed_Clean_Run Analysis_GraphViz
begin

section \<open>Executable interval seeded-clean (R_read) run: a derived global kept context-separated\<close>

text \<open>
  A second executable interval run on the Goblint-faithful seeded-clean spine, this
  time with a \<^emph>\<open>derived\<close> global.  Two globals: \<open>G\<close>, which \<open>main\<close> sets, and \<open>GH\<close>,
  which the callee computes as \<open>GH := G + 1\<close>.  \<open>main\<close> calls \<open>f\<close> twice, at sites where
  \<open>G\<close> holds the distinct points \<open>[0,0]\<close> and \<open>[10,10]\<close>.

  The run reuses the entire spine from \<open>Exec_Ivl_Cmp_Seed_Clean_Run\<close> --- the clean
  transfer \<^const>\<open>ivl_etf_clean_st\<close>, the context selector \<^const>\<open>ivl_ec\<close>, and the
  R_read combine \<^const>\<open>ivl_combine_rread\<close> --- adding only a new program and its
  equation system.  It is non-recursive and loop-free, so no interval widening runs.

  \<^bold>\<open>Precision it certifies.\<close>  The derived global \<open>GH\<close> is kept \<^emph>\<open>separated per calling
  context\<close>, in two places at once:

    \<^item> as the callee-exit \<^emph>\<open>local\<close> (\<open>dseed_cfg\<close> node \<open>1\<close>): \<open>GH = [1,1]\<close> in the
      \<open>G = [0,0]\<close> context, \<open>GH = [11,11]\<close> in the \<open>G = [10,10]\<close> context;
    \<^item> as the context-indexed \<^emph>\<open>global side state\<close> (\<open>Inr dseed_ctx_lo\<close> / \<open>Inr
      dseed_ctx_hi\<close>): the side effect \<open>GH := G + 1\<close> is published under the writer's
      own context (the generator remaps the transfer's side key to \<open>gkey c = c\<close>),
      so the two writes land in distinct global slots, \<open>[1,1]\<close> and \<open>[11,11]\<close>.

  A monovariant (context-insensitive) analysis would merge \<open>f\<close>'s two entries to
  \<open>G = [0,10]\<close> and derive a single callee exit \<open>GH = [1,11]\<close> --- the union of the
  two points.  The D/G/C split recovers the exact points.

  \<^bold>\<open>What R_read does not do.\<close>  The clean transfer reads only the local slot.  A caller
  that read a global back after the call (\<open>g := G\<close>) would see \<open>bot\<close>: the clean combine
  returns \<^const>\<open>restrict_local_st\<close> of the result, so globals are not folded into the
  caller's local flow.  Folding a global into a read is G_read/Obs, a different
  combine; this run therefore certifies the callee and global-side precision, not a
  caller read-back.
\<close>

subsection \<open>A non-recursive two-call program with a derived global\<close>

definition dseed_prog :: imp_prog where
  "dseed_prog = \<lbrakk>
     int G, GH;

     void f() {
       GH := G + 1
     }
     void main() {
       G := 0;
       f();
       G := 10;
       f()
     }
   \<rbrakk>"

definition dseed_cfg :: cfg where
  "dseed_cfg = compile_prog (prog_table dseed_prog) (prog_procs dseed_prog) (prog_main dseed_prog)"

definition dseed_clean_eqs :: "(pp \<times> ivl st, ivl st, ivl st) eqsT" where
  "dseed_clean_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. ivl_combine_rread cc ex c)
     restrict_global_st dseed_cfg ivl_etf_clean_st bot cinit_ivl_st"

definition dseed_clean_solution ::
  "(pp \<times> ivl st) set \<times> ((pp \<times> ivl st) + ivl st \<Rightarrow> ivl st)" where
  "dseed_clean_solution = TD_side_always_join_Interp_solve dseed_clean_eqs (cfg_exit dseed_cfg, bot)"

lemma dseed_clean_runs: "fst dseed_clean_solution \<noteq> {}"
  unfolding dseed_clean_solution_def dseed_clean_eqs_def dseed_cfg_def dseed_prog_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The two calling contexts (G-derived, distinct points)\<close>

text \<open>The context of a callee activation is the surviving global read from the caller
  \<^emph>\<open>local\<close> (\<^const>\<open>ivl_ec\<close>): \<open>G = [0,0]\<close> at the first call site, \<open>G = [10,10]\<close> at the
  second.\<close>

definition dseed_ctx_lo :: "ivl st" where
  "dseed_ctx_lo = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 0) (Fin 0)))"

definition dseed_ctx_hi :: "ivl st" where
  "dseed_ctx_hi = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 10) (Fin 10)))"

subsection \<open>The derived global stays separated per context (callee-exit local)\<close>

text \<open>
  \<open>f\<close> computes \<open>GH := G + 1\<close> reading the seeded local, so the callee-exit local
  (\<^const>\<open>dseed_cfg\<close> node \<open>1\<close>) carries the exact derived point in each context:
  \<open>GH = [1,1]\<close> when \<open>G = [0,0]\<close>, \<open>GH = [11,11]\<close> when \<open>G = [10,10]\<close>.
\<close>

lemma dseed_callee_exit_derived:
  "lookup_st (snd dseed_clean_solution (Inl (1, dseed_ctx_lo))) ''GH'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd dseed_clean_solution (Inl (1, dseed_ctx_hi))) ''GH'' = Ivl (Fin 11) (Fin 11)"
  unfolding dseed_clean_solution_def dseed_clean_eqs_def dseed_cfg_def dseed_prog_def
    dseed_ctx_lo_def dseed_ctx_hi_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>...and as the context-indexed global side state\<close>

text \<open>
  The write \<open>GH := G + 1\<close> is sided under the writer's own context (the generator
  remaps the transfer's side key to \<open>gkey c = c\<close>), so the derived global lands in a
  \<^emph>\<open>per-context\<close> global slot: \<open>Inr dseed_ctx_lo\<close> holds \<open>GH = [1,1]\<close>, \<open>Inr
  dseed_ctx_hi\<close> holds \<open>GH = [11,11]\<close>.  The two side effects do not join.
\<close>

lemma dseed_global_side_separated:
  "lookup_st (snd dseed_clean_solution (Inr dseed_ctx_lo)) ''GH'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd dseed_clean_solution (Inr dseed_ctx_hi)) ''GH'' = Ivl (Fin 11) (Fin 11)"
  unfolding dseed_clean_solution_def dseed_clean_eqs_def dseed_cfg_def dseed_prog_def
    dseed_ctx_lo_def dseed_ctx_hi_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>Soundness of the derived values\<close>

text \<open>The concrete run computes \<open>GH = 1\<close> (from \<open>G = 0\<close>) and \<open>GH = 11\<close> (from \<open>G = 10\<close>),
  and both lie in the concretisation of the analyzer's interval.\<close>

lemma dseed_derived_in_gamma:
  "1 \<in> gamma_ivl (Ivl (Fin 1) (Fin 1)) \<and> 11 \<in> gamma_ivl (Ivl (Fin 11) (Fin 11))"
  by simp

subsection \<open>The two contexts stay separate (D/G/C precision)\<close>

text \<open>
  The G-derived context split keeps the two activations apart at distinct points.
  A monovariant analysis would join \<open>f\<close>'s entries to \<open>G = [0,10]\<close> and its exit to a
  single \<open>GH = [1,11]\<close>, losing the per-call-site precision the split preserves.
\<close>

theorem dseed_contexts_separate:
  "lookup_st (snd dseed_clean_solution (Inl (1, dseed_ctx_lo))) ''GH'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd dseed_clean_solution (Inl (1, dseed_ctx_hi))) ''GH'' = Ivl (Fin 11) (Fin 11)
   \<and> (Ivl (Fin 1) (Fin 1) :: ivl) \<noteq> Ivl (Fin 11) (Fin 11)"
  using dseed_callee_exit_derived by simp

subsection \<open>Context-clustered GraphViz of the solved run\<close>

text \<open>
  One cluster per activation: \<open>main\<close> (context \<open>bot\<close>) and the two copies of \<open>f\<close>, at
  \<open>G = [0,0]\<close> and \<open>G = [10,10]\<close>.  Node labels are the generic
  \<^const>\<open>ctx_debug_state_node_label_auto\<close> (auto-collected locals, per-context state);
  each \<open>f\<close> cluster carries its separated derived global \<open>GH\<close> from the context-indexed
  global side state.
\<close>

datatype dseed_rctx = DsMain | DsFLo | DsFHi

definition dseed_rctx_ctx :: "dseed_rctx \<Rightarrow> ivl st" where
  "dseed_rctx_ctx r = (case r of DsMain \<Rightarrow> bot | DsFLo \<Rightarrow> dseed_ctx_lo | DsFHi \<Rightarrow> dseed_ctx_hi)"

definition dseed_rctx_key :: "dseed_rctx \<Rightarrow> string" where
  "dseed_rctx_key r = (case r of DsMain \<Rightarrow> ''main'' | DsFLo \<Rightarrow> ''fGlo'' | DsFHi \<Rightarrow> ''fGhi'')"

definition dseed_rctx_label :: "dseed_rctx \<Rightarrow> string" where
  "dseed_rctx_label r =
     (case r of DsMain \<Rightarrow> ''main'' | DsFLo \<Rightarrow> ''f @ G=[0,0]'' | DsFHi \<Rightarrow> ''f @ G=[10,10]'')"

text \<open>\<open>f\<close> is compiled first, so its body is \<open>pp0\<close>/\<open>pp1\<close>; \<open>main\<close> is the rest.\<close>
definition dseed_f_pps :: "pp list" where "dseed_f_pps = [0, 1]"

definition dseed_node_label :: "pp \<times> dseed_rctx \<Rightarrow> string" where
  "dseed_node_label = ctx_debug_state_node_label_auto dseed_cfg
     (\<lambda>pc. case pc of (p, r) \<Rightarrow> snd dseed_clean_solution (Inl (p, dseed_rctx_ctx r)))"

definition dseed_globals :: "dseed_rctx \<Rightarrow> string" where
  "dseed_globals r =
     ''GH = '' @ show_val (lookup_st (snd dseed_clean_solution (Inr (dseed_rctx_ctx r))) ''GH'')"

text \<open>A call site's context is the global part of its caller local (\<^const>\<open>ivl_ec\<close>):
  node \<open>4\<close> selects \<open>G = [0,0]\<close>, node \<open>7\<close> selects \<open>G = [10,10]\<close>.\<close>
definition dseed_f_rctx_of :: "pp \<Rightarrow> dseed_rctx" where
  "dseed_f_rctx_of cc =
     (if restrict_global_st (snd dseed_clean_solution (Inl (cc, bot))) = dseed_ctx_lo
      then DsFLo else DsFHi)"

definition dseed_rmode_nodes :: "(pp \<times> dseed_rctx) list" where
  "dseed_rmode_nodes =
     map (\<lambda>p. (p, DsMain)) (filter (\<lambda>p. p \<notin> set dseed_f_pps) (sorted_list_of_set (nodes dseed_cfg)))
   @ map (\<lambda>p. (p, DsFLo)) dseed_f_pps
   @ map (\<lambda>p. (p, DsFHi)) dseed_f_pps"

definition dseed_rmode_intra :: "((pp \<times> dseed_rctx) \<times> edge_action \<times> (pp \<times> dseed_rctx)) list" where
  "dseed_rmode_intra =
     [((u, DsMain), a, (v, DsMain)). (u, a, v) \<leftarrow> cfg_edges_list dseed_cfg,
        a \<noteq> EA_Enter, u \<notin> set dseed_f_pps, v \<notin> set dseed_f_pps]
   @ [((u, r), a, (v, r)). (u, a, v) \<leftarrow> cfg_edges_list dseed_cfg,
        u \<in> set dseed_f_pps, v \<in> set dseed_f_pps, r \<leftarrow> [DsFLo, DsFHi]]"

definition dseed_rmode_calls :: "((pp \<times> dseed_rctx) \<times> (pp \<times> dseed_rctx)) list" where
  "dseed_rmode_calls =
     [((u, DsMain), (v, dseed_f_rctx_of u)). (u, a, v) \<leftarrow> cfg_edges_list dseed_cfg, a = EA_Enter]"

definition dseed_rmode_returns ::
  "((pp \<times> dseed_rctx) \<times> (pp \<times> pp \<times> pp) \<times> (pp \<times> dseed_rctx)) list" where
  "dseed_rmode_returns =
     [((ex, dseed_f_rctx_of cc), (cc, ex, ret), (ret, DsMain)). (cc, ex, ret) \<leftarrow> cfg_combines_list dseed_cfg]"

definition dseed_dot :: String.literal where
  "dseed_dot = String.implode
     (ctx_debug_graphviz_with_globals
        dseed_rctx_key dseed_rctx_label dseed_globals dseed_node_label (\<lambda>_. ''shape=box'')
        [DsMain, DsFLo, DsFHi]
        dseed_rmode_nodes dseed_rmode_intra dseed_rmode_calls dseed_rmode_returns)"

text \<open>@{command ML_val} \<open>writeln (@{code dseed_dot})\<close> emits the DOT source: three clusters,
  the two \<open>f\<close> copies carrying the separated derived globals \<open>GH = [1,1]\<close> / \<open>GH = [11,11]\<close>.\<close>

ML_val \<open>writeln (@{code dseed_dot})\<close>

text \<open>
  \<^bold>\<open>What this run certifies.\<close>  The seeded-clean interval spine runs end to end through
  the vendored side solver on a two-call, loop-free program whose callee derives a
  \<^emph>\<open>second\<close> global \<open>GH := G + 1\<close>.  The G-derived context keeps that derived global
  separated per activation, both as the callee-exit local
  (\<open>dseed_callee_exit_derived\<close>) and as the context-indexed global side state
  (\<open>dseed_global_side_separated\<close>); the computed points are sound
  (\<open>dseed_derived_in_gamma\<close>) and distinct (\<open>dseed_contexts_separate\<close>), where a
  monovariant analysis would merge them to \<open>GH = [1,11]\<close>.  The abstract D/G/C
  soundness this run instances lives in
  \<^theory>\<open>Voblint_Analysis.Exec_Ivl_Cmp_Seed_Sound\<close>
  (@{thm [source] ivl_clean_ctx_collect_rread}).  No loop is analysed, so interval
  widening is not engaged.
\<close>

end

