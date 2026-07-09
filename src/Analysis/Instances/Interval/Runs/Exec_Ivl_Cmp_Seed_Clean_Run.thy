theory Exec_Ivl_Cmp_Seed_Clean_Run
  imports Exec_Ivl_Ctx_Gen_Run Exec_Cmp_Bridge Exec_Ivl_Cmp_Seed_Sound
begin

section \<open>Executable interval seeded-clean (R_read) run on a two-call program\<close>

text \<open>
  The Goblint-faithful seeded-clean spine, run end to end on the interval domain ---
  the executable interval sibling of the sign run in
  \<open>Exec_Sign_Cmp_Seed_Sound\<close>.  It combines three pieces, all
  reused from the generic layer with only interval-executable constructors added:

    \<^item> the \<^emph>\<open>seeded\<close> generator \<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close> with the faithful seed
      \<^const>\<open>restrict_global_st\<close> (delivers the caller's globals to the callee-entry
      local --- Goblint's \<open>sidel (FunctionEntry f, fc) v\<close>);
    \<^item> the \<^emph>\<open>clean\<close> executable transfer \<open>ivl_etf_clean_st\<close>, built from the generic
      \<^const>\<open>clean_edge_tree_st\<close> and the interval \<^const>\<open>ivl_tf_st\<close> --- it reads only
      the local slot (no \<open>\<squnion> g\<close>);
    \<^item> the R_read combine \<open>ivl_combine_rread\<close>, which selects the callee context
      from the caller \<^emph>\<open>local\<close> (\<open>ivl_ec\<close>, Goblint's \<open>Spec.context\<close>).

  The program is deliberately non-recursive and loop-free, so the run exercises the
  D/G/C spine without engaging interval widening.
\<close>

subsection \<open>Interval clean transfer, context selector, and R_read combine\<close>

text \<open>The clean interval executable transfer: the generic \<^const>\<open>clean_edge_tree_st\<close>
  at the interval base transfer \<^const>\<open>ivl_tf_st\<close>.  Reads only the local slot.\<close>

definition ivl_etf_clean_st :: "(unit, ivl st) effectful_st_transfer" where
  "ivl_etf_clean_st = \<lparr>
    etf_st_nop        = clean_edge_tree_st (ivl_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. clean_edge_tree_st (ivl_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. clean_edge_tree_st (ivl_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. clean_edge_tree_st (ivl_tf_st (EA_AssumeNot b))),
    etf_st_enter      = clean_edge_tree_st (ivl_tf_st EA_Enter),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

text \<open>Context = the surviving global state, read from the caller \<^emph>\<open>local\<close> (R_read);
  the key is the context itself (\<open>gkey = id\<close>).\<close>

definition ivl_ec :: "ivl st \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "ivl_ec ctx sc = restrict_global_st sc"

text \<open>The R_read seeding combine (interval sibling of the sign \<open>kgen_combine_rread\<close>):
  the callee context is selected from the caller local \<open>sc\<close> (not \<open>sc \<squnion> g\<close>), and the
  caller's globals are seeded into the callee activation via \<open>Side callee\<close>.\<close>

definition ivl_combine_rread ::
  "pp \<Rightarrow> pp \<Rightarrow> ivl st \<Rightarrow> (pp \<times> ivl st, ivl st, ivl st) strategy_tree"
where
  "ivl_combine_rread cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let callee = ivl_ec ctx sc in
       Side callee (restrict_global_st sc)
         (QueryL (ex, callee) (\<lambda>se.
           let res = restrict_local_st sc \<squnion> restrict_global_st (se \<squnion> g) in
           Side ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

subsection \<open>A non-recursive two-call interval program\<close>

text \<open>\<open>f\<close> increments the global; \<open>main\<close> calls it at two sites where \<open>G\<close> holds the
  distinct points \<open>[0,0]\<close> and \<open>[10,10]\<close>.  No loop, so no widening.\<close>

definition iseed_prog :: imp_prog where
  "iseed_prog = \<lbrakk>
     int G;

     void f() {
       G := G + 1
     }
     void main() {
       G := 0;
       f();
       G := 10;
       f()
     }
   \<rbrakk>"

definition iseed_cfg :: cfg where
  "iseed_cfg = compile_prog (prog_table iseed_prog) (prog_procs iseed_prog) (prog_main iseed_prog)"

definition iseed_clean_eqs :: "(pp \<times> ivl st, ivl st, ivl st) eqsT" where
  "iseed_clean_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. ivl_combine_rread cc ex c)
     restrict_global_st iseed_cfg ivl_etf_clean_st bot cinit_ivl_st"

definition iseed_clean_solution ::
  "(pp \<times> ivl st) set \<times> ((pp \<times> ivl st) + ivl st \<Rightarrow> ivl st)" where
  "iseed_clean_solution = TD_side_always_join_Interp_solve iseed_clean_eqs (cfg_exit iseed_cfg, bot)"

lemma iseed_clean_runs: "fst iseed_clean_solution \<noteq> {}"
  unfolding iseed_clean_solution_def iseed_clean_eqs_def iseed_cfg_def iseed_prog_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The two call contexts (global-derived, distinct points)\<close>

text \<open>The context of an activation is the surviving global (\<^const>\<open>ivl_ec\<close> reads it
  from the caller local): \<open>[0,0]\<close> at the first call site, \<open>[10,10]\<close> at the second.\<close>

definition iseed_ctx_lo :: "ivl st" where
  "iseed_ctx_lo = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 0) (Fin 0)))"

definition iseed_ctx_hi :: "ivl st" where
  "iseed_ctx_hi = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 10) (Fin 10)))"

subsection \<open>The transfer reads the local, not \<open>local \<squnion> global\<close>\<close>

text \<open>
  The two caller call-site locals (\<^const>\<open>iseed_cfg\<close> nodes \<open>4\<close> and \<open>7\<close>, in the
  \<^emph>\<open>main\<close> context \<open>\<bottom>\<close>) hold the \<^emph>\<open>distinct points\<close> \<open>[0,0]\<close> and \<open>[10,10]\<close>.
  Because the clean transfer reads only the local slot, the two call sites stay
  separated; a \<open>local \<squnion> global\<close> read would fold the published global back in.
\<close>

lemma iseed_caller_locals_points:
  "lookup_st (snd iseed_clean_solution (Inl (4, bot::ivl st))) ''G'' = Ivl (Fin 0) (Fin 0)
   \<and> lookup_st (snd iseed_clean_solution (Inl (7, bot::ivl st))) ''G'' = Ivl (Fin 10) (Fin 10)"
  unfolding iseed_clean_solution_def iseed_clean_eqs_def iseed_cfg_def iseed_prog_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The seed delivers the caller globals to the callee-entry local\<close>

text \<open>
  Under each context the callee-entry local (\<^const>\<open>iseed_cfg\<close> node \<open>0\<close>, \<open>f\<close>'s entry)
  carries the caller's global --- \<open>[0,0]\<close> in the \<open>iseed_ctx_lo\<close> activation, \<open>[10,10]\<close>
  in \<open>iseed_ctx_hi\<close>.  This is Goblint's \<open>sidel (FunctionEntry f, fc) v\<close>: the seed put
  the caller's \<open>G\<close> into the callee \<^emph>\<open>local\<close>, so the clean transfer sees it without
  reading the published global.
\<close>

lemma iseed_callee_entry_seeded:
  "lookup_st (snd iseed_clean_solution (Inl (0, iseed_ctx_lo))) ''G'' = Ivl (Fin 0) (Fin 0)
   \<and> lookup_st (snd iseed_clean_solution (Inl (0, iseed_ctx_hi))) ''G'' = Ivl (Fin 10) (Fin 10)"
  unfolding iseed_clean_solution_def iseed_clean_eqs_def iseed_cfg_def iseed_prog_def
    iseed_ctx_lo_def iseed_ctx_hi_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The clean transfer computes the increment on the local (sound)\<close>

text \<open>
  \<open>f\<close> executes \<open>G := G + 1\<close> reading the seeded local, so the callee-exit local
  (\<^const>\<open>iseed_cfg\<close> node \<open>1\<close>) is \<open>[1,1]\<close> in the low context and \<open>[11,11]\<close> in the high
  context --- the exact increment of each context's entry.
\<close>

lemma iseed_callee_increment:
  "lookup_st (snd iseed_clean_solution (Inl (1, iseed_ctx_lo))) ''G'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd iseed_clean_solution (Inl (1, iseed_ctx_hi))) ''G'' = Ivl (Fin 11) (Fin 11)"
  unfolding iseed_clean_solution_def iseed_clean_eqs_def iseed_cfg_def iseed_prog_def
    iseed_ctx_lo_def iseed_ctx_hi_def
    ivl_ec_def ivl_combine_rread_def ivl_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>Soundness of the two callee-exit results: the concrete run computes \<open>G = 1\<close>
  (from \<open>G = 0\<close>) and \<open>G = 11\<close> (from \<open>G = 10\<close>), and both lie in the concretisation of
  the analyzer's interval.\<close>

lemma iseed_increment_in_gamma:
  "1 \<in> gamma_ivl (Ivl (Fin 1) (Fin 1)) \<and> 11 \<in> gamma_ivl (Ivl (Fin 11) (Fin 11))"
  by simp

subsection \<open>The two contexts stay separate (D/G/C precision)\<close>

text \<open>
  The global-derived context split keeps the two activations apart: the callee-exit
  local is \<open>[1,1]\<close> in one context and \<open>[11,11]\<close> in the other, distinct points.  A
  context-insensitive (monovariant) analysis would join the two entries to
  \<open>[0,10]\<close> and the exits to \<open>[1,11]\<close>, losing the per-call-site precision.
\<close>

theorem iseed_contexts_separate:
  "lookup_st (snd iseed_clean_solution (Inl (1, iseed_ctx_lo))) ''G'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd iseed_clean_solution (Inl (1, iseed_ctx_hi))) ''G'' = Ivl (Fin 11) (Fin 11)
   \<and> (Ivl (Fin 1) (Fin 1) :: ivl) \<noteq> Ivl (Fin 11) (Fin 11)"
  using iseed_callee_increment by simp

text \<open>
  \<^bold>\<open>What this run certifies.\<close>  The executable interval seeded-clean spine runs end to
  end through the vendored side solver on a non-recursive, loop-free program: the
  seed (\<^const>\<open>restrict_global_st\<close>) delivers the caller's globals to the callee-entry
  local (\<open>iseed_callee_entry_seeded\<close>), the clean transfer reads only that local
  (\<open>iseed_caller_locals_points\<close>) and computes the sound increment
  (\<open>iseed_callee_increment\<close>, \<open>iseed_increment_in_gamma\<close>), and the global-derived
  context keeps the two activations at distinct points (\<open>iseed_contexts_separate\<close>).
  The abstract D/G/C soundness this run instances lives in
  \<^theory>\<open>Voblint_Analysis.Exec_Ivl_Cmp_Seed_Sound\<close>
  (@{thm [source] ivl_clean_ctx_collect_rread}).  No loop is analysed, so interval
  widening is not engaged; interval loop precision is a widening matter, orthogonal
  to this D/G/C run.
\<close>

end
