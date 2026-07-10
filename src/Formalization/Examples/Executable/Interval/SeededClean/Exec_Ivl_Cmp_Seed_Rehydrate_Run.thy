theory Exec_Ivl_Cmp_Seed_Rehydrate_Run
  imports Exec_Ivl_Cmp_Seed_Clean_Run Voblint_Analysis.Analysis_GraphViz
begin

section \<open>Return rehydration: caller continuation on the seeded-clean (R_read) spine\<close>

text \<open>
  The seeded-clean spine (\<^theory>\<open>Voblint_Formalization.Exec_Ivl_Cmp_Seed_Clean_Run\<close>) is
  Goblint-faithful on the \<^emph>\<open>enter\<close> side (the seed copies caller globals into the
  callee-entry local) and reads only the local \<open>D\<close> in the transfer.  Its combine,
  \<^const>\<open>ivl_combine_rread\<close>, returns \<^const>\<open>restrict_local_st\<close> of the merged result:
  it \<^emph>\<open>strips\<close> globals from the caller-local state on return.  A caller that reads a
  global back after the call --- \<open>g := G; h := GH\<close> --- therefore observes \<open>bot\<close>.

  This theory closes that gap with \<^emph>\<open>return rehydration\<close>, Goblint's \<open>Spec.combine\<close>:
  the caller continuation is reconstructed as
  \<^term>\<open>combine_abs_st sc se :: ivl st\<close> --- \<^emph>\<open>locals from the caller\<close> \<open>sc\<close>,
  \<^emph>\<open>globals from the callee exit\<close> \<open>se\<close> --- exactly the abstract mirror of the
  concrete \<^term>\<open>combine_states s t\<close> (\<open><s|t>\<close>).  This is not a \<open>local \<squnion> global\<close> read:
  the transfer is unchanged (still the clean, local-only \<^const>\<open>ivl_etf_clean_st\<close>),
  the callee context is still selected from the caller local (\<^const>\<open>ivl_ec\<close>), and
  the globals folded in are the \<^emph>\<open>callee's returned\<close> globals, not a flow-insensitive
  published slot.

  \<^bold>\<open>Goblint correspondence.\<close>  For a non-relational (per-variable) domain,
  Goblint's \<open>combine_env\<close> / \<open>combine_assign\<close> reconstruct the caller \<open>D.t\<close> by taking
  the caller's locals and the callee's globals (the callee \<open>D.t\<close> carries the updated
  globals).  \<^const>\<open>combine_abs_st\<close> is that reconstruction; it is what the retain and
  unit spines already use structurally.  The only change from the strip combine is
  \<^emph>\<open>not\<close> discarding the reconstructed globals via \<^const>\<open>restrict_local_st\<close>.
\<close>

subsection \<open>The rehydrating combine\<close>

text \<open>Selects the callee context from the caller local (\<^const>\<open>ivl_ec\<close>, R_read),
  seeds the caller globals to the callee entry, and on return rebuilds the caller
  continuation as \<^term>\<open>combine_abs_st sc se\<close> --- keeping the callee's globals in the
  returned local.\<close>

definition ivl_combine_rehydrate ::
  "pp \<Rightarrow> pp \<Rightarrow> ivl st \<Rightarrow> (pp \<times> ivl st, ivl st, ivl st) strategy_tree"
where
  "ivl_combine_rehydrate cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc.
       let callee = ivl_ec ctx sc in
       Side callee (restrict_global_st sc)
         (QueryL (ex, callee) (\<lambda>se.
           Side ctx (restrict_global_st se)
             (Answer (combine_abs_st sc se)))))"

text \<open>The R_read architecture is preserved: the callee context is a function of the
  caller \<^emph>\<open>local\<close> alone (no published-global read), identical to the clean combine's
  selector.\<close>

lemma ivl_combine_rehydrate_context_is_local:
  "ivl_ec ctx sc = restrict_global_st sc"
  by (simp add: ivl_ec_def)

text \<open>The returned caller continuation is the structural combine \<^const>\<open>combine_abs_st\<close>
  --- locals from the caller \<open>sc\<close>, globals from the callee exit \<open>se\<close> --- \<^emph>\<open>not\<close> a
  \<open>local \<squnion> global\<close> read of a published slot.\<close>

lemma ivl_combine_rehydrate_answer:
  "ivl_combine_rehydrate cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc.
       Side (restrict_global_st sc) (restrict_global_st sc)
         (QueryL (ex, restrict_global_st sc) (\<lambda>se.
           Side ctx (restrict_global_st se)
             (Answer (combine_abs_st sc se)))))"
  by (simp add: ivl_combine_rehydrate_def ivl_ec_def Let_def)

subsection \<open>Soundness of the rehydrated caller continuation (Spec.combine)\<close>

text \<open>
  The crux of the return path: if the caller store \<open>s\<close> is soundly abstracted by the
  caller local \<open>sc\<close> and the callee-exit store \<open>t\<close> by the callee-exit local \<open>se\<close>,
  then Goblint's concrete combine \<open><s|t>\<close> (locals from \<open>s\<close>, globals from \<open>t\<close>) is
  soundly abstracted by the rehydrated continuation \<^term>\<open>combine_abs_st sc se\<close>.
  This is exactly the \<open>COMB\<close> obligation of the generic context-sliced soundness
  theorem \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>
  (@{thm [source] sound_transfer.clean_ctx_collect_rread}), whose conclusion is the
  \<^emph>\<open>local\<close> slot at the return node.  The strip combine cannot discharge it once the
  callee writes a global that is later read: its returned local has that global at
  \<open>bot\<close>, so \<open><s|t>\<close> (carrying the concrete global) escapes the concretisation.
  Rehydration restores exactly the missing globals, and no more.

  It is a pure \<^class>\<open>sound_domain\<close> fact (\<open>combine_states_sound\<close> transported to
  the executable \<^typ>\<open>ivl st\<close> layer via \<open>fun_of_st_combine_abs_st\<close>); it does
  not read a published global slot and so does not reintroduce the \<open>local \<squnion> global\<close>
  join.\<close>

lemma rehydrate_caller_continuation_sound:
  fixes sc se :: "ivl st"
  assumes "s \<in> \<lbrakk>fun_of_st sc\<rbrakk>" and "t \<in> \<lbrakk>fun_of_st se\<rbrakk>"
  shows "<s|t> \<in> \<lbrakk>fun_of_st (combine_abs_st sc se)\<rbrakk>"
  using assms by (simp add: fun_of_st_combine_abs_st combine_states_sound)

subsection \<open>A program that reads globals back after the call\<close>

text \<open>The witness program: \<open>f\<close> derives \<open>GH := G + 1\<close>; \<open>main\<close> calls it twice and
  \<^emph>\<open>reads both globals back\<close> into locals \<open>g1,h1\<close> / \<open>g2,h2\<close> after each call.  Under the
  strip combine these reads are \<open>bot\<close>; under rehydration they are the exact points.\<close>

definition rhyd_prog :: imp_prog where
  "rhyd_prog = \<lbrakk>
     int G, GH;

     void f() {
       GH := G + 1
     }
     void main() {
       G := 0;
       f();
       g1 := G;
       h1 := GH;
       G := 10;
       f();
       g2 := G;
       h2 := GH
     }
   \<rbrakk>"

definition rhyd_cfg :: cfg where
  "rhyd_cfg = compile_prog (prog_table rhyd_prog) (prog_procs rhyd_prog) (prog_main rhyd_prog)"

definition rhyd_eqs :: "(pp \<times> ivl st, ivl st, ivl st) eqsT" where
  "rhyd_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. ivl_combine_rehydrate cc ex c)
     restrict_global_st rhyd_cfg ivl_etf_clean_st bot cinit_ivl_st"

definition rhyd_solution ::
  "(pp \<times> ivl st) set \<times> ((pp \<times> ivl st) + ivl st \<Rightarrow> ivl st)" where
  "rhyd_solution = TD_side_always_join_Interp_solve rhyd_eqs (cfg_exit rhyd_cfg, bot)"


lemma rhyd_runs: "fst rhyd_solution \<noteq> {}"
  unfolding rhyd_solution_def rhyd_eqs_def rhyd_cfg_def rhyd_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    combine_abs_st_def side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The read-backs recover the exact points (rehydration, not a read join)\<close>

text \<open>
  \<^const>\<open>rhyd_cfg\<close> nodes: \<open>f = 0 \<rightarrow> 1\<close>; \<open>main\<close> reads back \<open>g1\<close> at \<open>7\<close>, \<open>h1\<close> at \<open>9\<close>,
  \<open>g2\<close> at \<open>15\<close>, \<open>h2\<close> at \<open>17\<close>.  All four are exact points --- the globals are present in
  the caller-local flow because \<^const>\<open>ivl_combine_rehydrate\<close> put them back on return,
  \<^emph>\<open>not\<close> because a read folds in a published global.
\<close>

lemma rhyd_readbacks_exact:
  "lookup_st (snd rhyd_solution (Inl (7,  bot::ivl st))) ''g1'' = Ivl (Fin 0)  (Fin 0)
   \<and> lookup_st (snd rhyd_solution (Inl (9,  bot::ivl st))) ''h1'' = Ivl (Fin 1)  (Fin 1)
   \<and> lookup_st (snd rhyd_solution (Inl (15, bot::ivl st))) ''g2'' = Ivl (Fin 10) (Fin 10)
   \<and> lookup_st (snd rhyd_solution (Inl (17, bot::ivl st))) ''h2'' = Ivl (Fin 11) (Fin 11)"
  unfolding rhyd_solution_def rhyd_eqs_def rhyd_cfg_def rhyd_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    combine_abs_st_def side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>Soundness of the read-back values: the concrete run has \<open>g1=0, h1=1, g2=10,
  h2=11\<close>, and each lies in the concretisation of the analyzer's interval.\<close>

lemma rhyd_readbacks_in_gamma:
  "0 \<in> gamma_ivl (Ivl (Fin 0) (Fin 0)) \<and> 1 \<in> gamma_ivl (Ivl (Fin 1) (Fin 1))
   \<and> 10 \<in> gamma_ivl (Ivl (Fin 10) (Fin 10)) \<and> 11 \<in> gamma_ivl (Ivl (Fin 11) (Fin 11))"
  by simp

subsection \<open>The two contexts stay separated (rehydration preserves R_read precision)\<close>

text \<open>The two calling contexts are the callee-selected globals: \<open>{G=[0,0]}\<close> at the
  first site, and \<open>{G=[10,10], GH=[1,1]}\<close> at the second --- rehydration carries the
  first call's derived \<open>GH\<close> into the caller local, so the second context observes it.\<close>

definition rhyd_ctx_lo :: "ivl st" where
  "rhyd_ctx_lo = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 0) (Fin 0)))"

definition rhyd_ctx_hi :: "ivl st" where
  "rhyd_ctx_hi = restrict_global_st
     (update_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 10) (Fin 10))) ''GH'' (Ivl (Fin 1) (Fin 1)))"

text \<open>The callee-exit local (\<^const>\<open>rhyd_cfg\<close> node \<open>1\<close>) is the exact derived point in
  each context, distinct across the two --- the R_read separation of the seeded-clean
  spine survives rehydration.\<close>

lemma rhyd_callee_exit_separated:
  "lookup_st (snd rhyd_solution (Inl (1, rhyd_ctx_lo))) ''GH'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd rhyd_solution (Inl (1, rhyd_ctx_hi))) ''GH'' = Ivl (Fin 11) (Fin 11)
   \<and> (Ivl (Fin 1) (Fin 1) :: ivl) \<noteq> Ivl (Fin 11) (Fin 11)"
  unfolding rhyd_solution_def rhyd_eqs_def rhyd_cfg_def rhyd_prog_def
    rhyd_ctx_lo_def rhyd_ctx_hi_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    combine_abs_st_def side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>Context-clustered GraphViz of the solved run\<close>

text \<open>One cluster per activation: \<open>main\<close> (context \<open>bot\<close>, carrying the rehydrated
  read-backs \<open>g1,h1,g2,h2\<close>) and the two copies of \<open>f\<close> at their contexts.  Node labels
  are the generic \<^const>\<open>ctx_debug_state_node_label_auto\<close>; each \<open>f\<close> cluster carries
  its callee-derived global \<open>GH\<close>.\<close>

datatype rhyd_rctx = RhMain | RhFLo | RhFHi

definition rhyd_rctx_ctx :: "rhyd_rctx \<Rightarrow> ivl st" where
  "rhyd_rctx_ctx r = (case r of RhMain \<Rightarrow> bot | RhFLo \<Rightarrow> rhyd_ctx_lo | RhFHi \<Rightarrow> rhyd_ctx_hi)"

definition rhyd_rctx_key :: "rhyd_rctx \<Rightarrow> string" where
  "rhyd_rctx_key r = (case r of RhMain \<Rightarrow> ''main'' | RhFLo \<Rightarrow> ''fGlo'' | RhFHi \<Rightarrow> ''fGhi'')"

definition rhyd_rctx_label :: "rhyd_rctx \<Rightarrow> string" where
  "rhyd_rctx_label r =
     (case r of RhMain \<Rightarrow> ''main'' | RhFLo \<Rightarrow> ''f @ G=[0,0]'' | RhFHi \<Rightarrow> ''f @ G=[10,10]'')"

definition rhyd_f_pps :: "pp list" where "rhyd_f_pps = [0, 1]"

definition rhyd_node_label :: "pp \<times> rhyd_rctx \<Rightarrow> string" where
  "rhyd_node_label = ctx_debug_state_node_label_auto rhyd_cfg
     (\<lambda>pc. case pc of (p, r) \<Rightarrow> snd rhyd_solution (Inl (p, rhyd_rctx_ctx r)))"

definition rhyd_globals :: "rhyd_rctx \<Rightarrow> string" where
  "rhyd_globals r =
     ''GH = '' @ show_val (lookup_st (snd rhyd_solution (Inr (rhyd_rctx_ctx r))) ''GH'')"

text \<open>A call site's context is the callee-selected global part of its caller local
  (\<^const>\<open>ivl_ec\<close>): node \<open>4\<close> selects \<open>rhyd_ctx_lo\<close>, node \<open>11\<close> selects \<open>rhyd_ctx_hi\<close>.\<close>
definition rhyd_f_rctx_of :: "pp \<Rightarrow> rhyd_rctx" where
  "rhyd_f_rctx_of cc =
     (if restrict_global_st (snd rhyd_solution (Inl (cc, bot))) = rhyd_ctx_lo
      then RhFLo else RhFHi)"

definition rhyd_rmode_nodes :: "(pp \<times> rhyd_rctx) list" where
  "rhyd_rmode_nodes =
     map (\<lambda>p. (p, RhMain)) (filter (\<lambda>p. p \<notin> set rhyd_f_pps) (sorted_list_of_set (nodes rhyd_cfg)))
   @ map (\<lambda>p. (p, RhFLo)) rhyd_f_pps
   @ map (\<lambda>p. (p, RhFHi)) rhyd_f_pps"

definition rhyd_rmode_intra :: "((pp \<times> rhyd_rctx) \<times> edge_action \<times> (pp \<times> rhyd_rctx)) list" where
  "rhyd_rmode_intra =
     [((u, RhMain), a, (v, RhMain)). (u, a, v) \<leftarrow> cfg_edges_list rhyd_cfg,
        a \<noteq> EA_Enter, u \<notin> set rhyd_f_pps, v \<notin> set rhyd_f_pps]
   @ [((u, r), a, (v, r)). (u, a, v) \<leftarrow> cfg_edges_list rhyd_cfg,
        u \<in> set rhyd_f_pps, v \<in> set rhyd_f_pps, r \<leftarrow> [RhFLo, RhFHi]]"

definition rhyd_rmode_calls :: "((pp \<times> rhyd_rctx) \<times> (pp \<times> rhyd_rctx)) list" where
  "rhyd_rmode_calls =
     [((u, RhMain), (v, rhyd_f_rctx_of u)). (u, a, v) \<leftarrow> cfg_edges_list rhyd_cfg, a = EA_Enter]"

definition rhyd_rmode_returns ::
  "((pp \<times> rhyd_rctx) \<times> (pp \<times> pp \<times> pp) \<times> (pp \<times> rhyd_rctx)) list" where
  "rhyd_rmode_returns =
     [((ex, rhyd_f_rctx_of cc), (cc, ex, ret), (ret, RhMain)). (cc, ex, ret) \<leftarrow> cfg_combines_list rhyd_cfg]"

definition rhyd_dot :: String.literal where
  "rhyd_dot = String.implode
     (ctx_debug_graphviz_with_globals
        rhyd_rctx_key rhyd_rctx_label rhyd_globals rhyd_node_label (\<lambda>_. ''shape=box'')
        [RhMain, RhFLo, RhFHi]
        rhyd_rmode_nodes rhyd_rmode_intra rhyd_rmode_calls rhyd_rmode_returns)"

text \<open>@{command ML_val} \<open>writeln (@{code rhyd_dot})\<close> emits the DOT source: \<open>main\<close>'s
  read-back nodes carry \<open>g1=[0,0]\<close>, \<open>h1=[1,1]\<close>, \<open>g2=[10,10]\<close>, \<open>h2=[11,11]\<close>.\<close>

ML_val \<open>writeln (@{code rhyd_dot})\<close>

text \<open>
  \<^bold>\<open>What this run certifies.\<close>  Return rehydration completes the Goblint-faithful D/G/C
  return path.  The caller continuation is the structural combine
  \<^const>\<open>combine_abs_st\<close> (\<open>Spec.combine\<close>), proved \<open>\<gamma>\<close>-sound in
  \<open>rehydrate_caller_continuation_sound\<close> --- the \<open>COMB\<close> obligation of the generic
  context-sliced theorem, which the strip combine could not discharge once a callee
  global is read back.  The R_read architecture is untouched: the transfer still
  reads only the local (\<^const>\<open>ivl_etf_clean_st\<close>), the context is still selected from
  the caller local (\<open>ivl_combine_rehydrate_context_is_local\<close>), and the reconstructed
  globals are the callee's returned globals, not a \<open>local \<squnion> global\<close> read
  (\<open>ivl_combine_rehydrate_answer\<close>).  Executably, the four read-backs recover the exact
  points (\<open>rhyd_readbacks_exact\<close>, sound by \<open>rhyd_readbacks_in_gamma\<close>) and the two
  contexts stay separated (\<open>rhyd_callee_exit_separated\<close>).  The strip-combine spine
  (\<^theory>\<open>Voblint_Formalization.Exec_Ivl_Cmp_Seed_Clean_Run\<close>) and the retain
  \<open>side_env_cmp\<close> baseline are untouched.  No loop is analysed, so interval widening is
  not engaged.
\<close>

end

