section \<open>Guarded recursion converges once empty intervals are canonicalised\<close>

theory Example_Interval_Recursion_Convergence
  imports
    Voblint_Formalization.Exec_Ivl_Cmp_Seed_Clean_Run
    Voblint_Analysis.Analysis_GraphViz
begin

text \<open>
  \<^bold>\<open>Bounded recursion the seeded-clean interval spine now solves exactly.\<close>  \<open>f\<close> guards its
  self-call by \<open>G < 3\<close>, so concrete execution does \<open>G = 0, 1, 2, 3\<close> and stops --- three
  live recursive calls, then the guard fails.  The compiled CFG carries the recursion
  (self \<^const>\<open>EA_Enter\<close> plus combine), reachable only through the guarded true branch.

  \<^bold>\<open>Why this used to diverge.\<close>  Empty intervals were not canonicalised.  Once the guard
  \<open>G < 3\<close> kills the branch in the recursive context \<open>[3,3]\<close> to \<open>Ivl (Fin 3) (Fin 2)\<close> (an
  empty interval), the following \<open>G := G + 1\<close> added the bounds pointwise:
  \<open>[3,2] + [1,1] = [4,3]\<close> --- \<^emph>\<open>another\<close> empty interval, a \<^emph>\<open>different\<close> representation of
  \<open>\<bottom>\<close>.  Fed through \<^const>\<open>restrict_global_st\<close> it became a fresh calling context \<open>[4,3]\<close>,
  whose activation walked to \<open>[5,3]\<close>, and so on.  Because \<^typ>\<open>ivl\<close> equality is structural,
  every step was a new unknown and the solver never terminated.

  \<^bold>\<open>The fix.\<close>  \<^const>\<open>normalize_ivl\<close> collapses every empty interval to the single \<^const>\<open>bot\<close>
  representative, and interval \<open>+\<close> / \<open>-\<close> route their operands through it.  Now
  \<open>[3,2] + [1,1] = \<bottom>\<close>, the recursive context collapses to \<^const>\<open>bot\<close>, and \<^const>\<open>bot\<close> is a
  fixpoint of the activation.  The activation therefore visits only the finitely many
  contexts \<open>[0,0]\<close>, \<open>[1,1]\<close>, \<open>[2,2]\<close>, \<open>[3,3]\<close>, \<^const>\<open>bot\<close>, so the exact (widening-free)
  seeded-clean solve terminates (\<open>rdiv_clean_runs\<close>), each call site keeps its own context
  (\<open>rdiv_callee_entry_by_context\<close>), and the published global is context-separated and precise
  (\<open>rdiv_published_global_by_context\<close>).  The final @{command ML_val} renders the six
  context clusters as GraphViz.
\<close>

subsection \<open>The program and its compiled CFG\<close>

definition rdiv_prog :: imp_prog where
  "rdiv_prog = \<lbrakk>
     int G;
     void f() {
       if (G < 3) { G := G + 1; f() } else { G := G }
     }
     void main() {
       G := 0;
       f()
     }
   \<rbrakk>"

definition rdiv_cfg :: cfg where
  "rdiv_cfg = compile_prog (prog_table rdiv_prog) (prog_procs rdiv_prog) (prog_main rdiv_prog)"

subsection \<open>The exact seeded-clean solve now terminates\<close>

definition rdiv_clean_eqs :: "(pp \<times> ivl st, ivl st, ivl st) eqsT" where
  "rdiv_clean_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. ivl_combine_rread cc ex c)
     restrict_global_st rdiv_cfg ivl_etf_clean_st bot cinit_ivl_st"

definition rdiv_clean_solution ::
  "(pp \<times> ivl st) set \<times> ((pp \<times> ivl st) + ivl st \<Rightarrow> ivl st)" where
  "rdiv_clean_solution = TD_side_always_join_Interp_solve rdiv_clean_eqs (cfg_exit rdiv_cfg, bot)"

text \<open>Termination: the exact (widening-free) solve returns a non-empty reached set.  Before
  the interval fix this \<^const>\<open>TD_side_always_join_Interp_solve\<close> looped forever.\<close>
lemma rdiv_clean_runs: "fst rdiv_clean_solution \<noteq> {}"
  unfolding rdiv_clean_solution_def rdiv_clean_eqs_def rdiv_cfg_def rdiv_prog_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>Context sensitivity: each call site keeps its own context\<close>

text \<open>\<open>f\<close>'s entry (node 0) is solved under the distinct contexts the activation visits:
  \<open>[0,0]\<close> from \<^emph>\<open>main\<close>, then \<open>[1,1]\<close>, \<open>[2,2]\<close>, \<open>[3,3]\<close> down the live recursion, and
  \<^const>\<open>bot\<close> from the guard-killed deeper recursion.  The callee-entry local carries the
  context's \<open>G\<close>.\<close>

definition rdiv_ctxk :: "Int.int \<Rightarrow> ivl st" where
  "rdiv_ctxk k = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin k) (Fin k)))"

lemma rdiv_callee_entry_by_context:
  "lookup_st (snd rdiv_clean_solution (Inl (0, rdiv_ctxk 0))) ''G'' = Ivl (Fin 0) (Fin 0)
   \<and> lookup_st (snd rdiv_clean_solution (Inl (0, rdiv_ctxk 1))) ''G'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd rdiv_clean_solution (Inl (0, rdiv_ctxk 2))) ''G'' = Ivl (Fin 2) (Fin 2)
   \<and> lookup_st (snd rdiv_clean_solution (Inl (0, rdiv_ctxk 3))) ''G'' = Ivl (Fin 3) (Fin 3)"
  unfolding rdiv_clean_solution_def rdiv_clean_eqs_def rdiv_cfg_def rdiv_prog_def
    rdiv_ctxk_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>The published global \<open>G\<close> is likewise context-separated and precise: each live
  context contributes exactly its reachable band, whose union is the sound
  flow-insensitive bound \<open>[0,3]\<close>.\<close>
lemma rdiv_published_global_by_context:
  "lookup_st (snd rdiv_clean_solution (Inr (rdiv_ctxk 0))) ''G'' = Ivl (Fin 0) (Fin 1)
   \<and> lookup_st (snd rdiv_clean_solution (Inr (rdiv_ctxk 1))) ''G'' = Ivl (Fin 1) (Fin 2)
   \<and> lookup_st (snd rdiv_clean_solution (Inr (rdiv_ctxk 2))) ''G'' = Ivl (Fin 2) (Fin 3)
   \<and> lookup_st (snd rdiv_clean_solution (Inr (rdiv_ctxk 3))) ''G'' = Ivl (Fin 3) (Fin 3)"
  unfolding rdiv_clean_solution_def rdiv_clean_eqs_def rdiv_cfg_def rdiv_prog_def
    rdiv_ctxk_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>Context-clustered GraphViz of the solved run\<close>

text \<open>One cluster per activation context: \<^emph>\<open>main\<close> (context \<^const>\<open>bot\<close>), the four live
  \<open>f\<close> copies at \<open>[0,0]\<close>, \<open>[1,1]\<close>, \<open>[2,2]\<close>, \<open>[3,3]\<close>, and the collapsed \<open>f @ \<bottom>\<close> the killed
  recursion folds into.  \<^const>\<open>EA_Enter\<close> edges wire the descending context chain; combine
  edges wire each callee exit back to its caller's continuation.\<close>

datatype rdiv_rctx = RMain | RF0 | RF1 | RF2 | RF3 | RFbot

definition rdiv_rctx_ctx :: "rdiv_rctx \<Rightarrow> ivl st" where
  "rdiv_rctx_ctx r = (case r of RMain \<Rightarrow> bot | RF0 \<Rightarrow> rdiv_ctxk 0 | RF1 \<Rightarrow> rdiv_ctxk 1
                        | RF2 \<Rightarrow> rdiv_ctxk 2 | RF3 \<Rightarrow> rdiv_ctxk 3 | RFbot \<Rightarrow> bot)"

definition rdiv_rctx_key :: "rdiv_rctx \<Rightarrow> string" where
  "rdiv_rctx_key r = (case r of RMain \<Rightarrow> ''main'' | RF0 \<Rightarrow> ''f0'' | RF1 \<Rightarrow> ''f1''
                        | RF2 \<Rightarrow> ''f2'' | RF3 \<Rightarrow> ''f3'' | RFbot \<Rightarrow> ''fBot'')"

definition rdiv_rctx_label :: "rdiv_rctx \<Rightarrow> string" where
  "rdiv_rctx_label r = (case r of RMain \<Rightarrow> ''main'' | RF0 \<Rightarrow> ''f @ G=[0,0]''
                          | RF1 \<Rightarrow> ''f @ G=[1,1]'' | RF2 \<Rightarrow> ''f @ G=[2,2]''
                          | RF3 \<Rightarrow> ''f @ G=[3,3]'' | RFbot \<Rightarrow> ''f @ G=bot (dead)'')"

definition rdiv_f_pps :: "pp list" where "rdiv_f_pps = [0, 1, 2, 3, 4, 5, 6, 7]"

definition rdiv_main_pps :: "pp list" where
  "rdiv_main_pps = filter (\<lambda>p. p \<notin> set rdiv_f_pps) (sorted_list_of_set (nodes rdiv_cfg))"

definition rdiv_f_rctxs :: "rdiv_rctx list" where
  "rdiv_f_rctxs = [RF0, RF1, RF2, RF3, RFbot]"

text \<open>\<open>G\<close> is a global, so the auto local-var collector omits it; we render the seeded
  local \<open>G\<close> slot explicitly, exposing the intra-context flow (guard kill \<open>[3,3] \<rightarrow> [3,2]\<close>,
  increment \<open>\<rightarrow> \<bottom>\<close>, and the else branch coming alive at \<open>[3,3]\<close>).\<close>
definition rdiv_node_label :: "pp \<times> rdiv_rctx \<Rightarrow> string" where
  "rdiv_node_label = ctx_debug_state_node_label rdiv_cfg [''G'']
     (\<lambda>pc. case pc of (p, r) \<Rightarrow> snd rdiv_clean_solution (Inl (p, rdiv_rctx_ctx r)))"

definition rdiv_globals :: "rdiv_rctx \<Rightarrow> string" where
  "rdiv_globals r =
     ''G = '' @ show_val (lookup_st (snd rdiv_clean_solution (Inr (rdiv_rctx_ctx r))) ''G'')"

definition rdiv_gv_nodes :: "(pp \<times> rdiv_rctx) list" where
  "rdiv_gv_nodes =
     map (\<lambda>p. (p, RMain)) rdiv_main_pps
   @ concat (map (\<lambda>r. map (\<lambda>p. (p, r)) rdiv_f_pps) rdiv_f_rctxs)"

definition rdiv_gv_intra :: "((pp \<times> rdiv_rctx) \<times> edge_action \<times> (pp \<times> rdiv_rctx)) list" where
  "rdiv_gv_intra =
     [((u, RMain), a, (v, RMain)). (u, a, v) \<leftarrow> cfg_edges_list rdiv_cfg,
        a \<noteq> EA_Enter, u \<in> set rdiv_main_pps, v \<in> set rdiv_main_pps]
   @ [((u, r), a, (v, r)). (u, a, v) \<leftarrow> cfg_edges_list rdiv_cfg,
        a \<noteq> EA_Enter, u \<in> set rdiv_f_pps, v \<in> set rdiv_f_pps, r \<leftarrow> rdiv_f_rctxs]"

text \<open>The \<^emph>\<open>value-dependent\<close> call chain: \<^emph>\<open>main\<close> enters \<open>f @ [0,0]\<close>, and each \<open>f\<close> copy's
  self-call descends one context, the last two collapsing into \<open>f @ \<bottom>\<close>.\<close>
definition rdiv_callpairs :: "(rdiv_rctx \<times> rdiv_rctx) list" where
  "rdiv_callpairs =
     [(RMain, RF0), (RF0, RF1), (RF1, RF2), (RF2, RF3), (RF3, RFbot), (RFbot, RFbot)]"

definition rdiv_call_node :: "rdiv_rctx \<Rightarrow> pp" where
  "rdiv_call_node cl = (case cl of RMain \<Rightarrow> 10 | _ \<Rightarrow> 3)"

definition rdiv_ret_node :: "rdiv_rctx \<Rightarrow> pp" where
  "rdiv_ret_node cl = (case cl of RMain \<Rightarrow> 11 | _ \<Rightarrow> 4)"

definition rdiv_gv_calls :: "((pp \<times> rdiv_rctx) \<times> (pp \<times> rdiv_rctx)) list" where
  "rdiv_gv_calls = map (\<lambda>(cl, ce). ((rdiv_call_node cl, cl), (0, ce))) rdiv_callpairs"

definition rdiv_gv_returns ::
  "((pp \<times> rdiv_rctx) \<times> (pp \<times> pp \<times> pp) \<times> (pp \<times> rdiv_rctx)) list" where
  "rdiv_gv_returns =
     map (\<lambda>(cl, ce). ((7, ce), (rdiv_call_node cl, 7, rdiv_ret_node cl), (rdiv_ret_node cl, cl)))
       rdiv_callpairs"

definition rdiv_dot :: String.literal where
  "rdiv_dot = String.implode
     (ctx_debug_graphviz_with_globals
        rdiv_rctx_key rdiv_rctx_label rdiv_globals rdiv_node_label (\<lambda>_. ''shape=box'')
        [RMain, RF0, RF1, RF2, RF3, RFbot]
        rdiv_gv_nodes rdiv_gv_intra rdiv_gv_calls rdiv_gv_returns)"

text \<open>@{command ML_val} \<open>writeln (@{code rdiv_dot})\<close> emits the DOT source: six context
  clusters, the \<^const>\<open>EA_Enter\<close> chain \<open>main \<rightarrow> f0 \<rightarrow> f1 \<rightarrow> f2 \<rightarrow> f3 \<rightarrow> fBot\<close>, and each node
  annotated with its local \<open>G\<close>.  The \<open>f3\<close> cluster makes the fix legible: \<open>pp0 [3,3]\<close>, the
  guard kills to \<open>pp1 [3,2]\<close>, the increment normalises to canonical \<open>\<bottom>\<close> at \<open>pp2\<close>, and the
  else branch \<open>![G<3]\<close> is the live one, exiting \<open>[3,3]\<close>.\<close>

ML_val \<open>writeln (@{code rdiv_dot})\<close>

end
