theory Exec_Sign_Cmp_Shared
  imports Voblint_Analysis.Sign_Exec_Sound Voblint_Analysis.Exec_Cmp_Bridge Voblint_Analysis.Solver_Side_RG
begin

section \<open>Shared executable keyed support for the sign seeded-clean cone\<close>

definition kgen_prog :: imp_prog where
  "kgen_prog = \<lbrakk>
     int G;

     void f() {
       G := G + G
     }
     void main() {
       G := 0;
       f();
       G := 1;
       f()
     }
   \<rbrakk>"

definition kgen_cfg :: cfg where
  "kgen_cfg = compile_prog (prog_table kgen_prog) (prog_procs kgen_prog) (prog_main kgen_prog)"

definition kgen_ec :: "sign st \<Rightarrow> sign st \<Rightarrow> sign st" where
  "kgen_ec ctx sc = restrict_global_st sc"

definition sign_etf_clean_st :: "(unit, sign st) effectful_st_transfer" where
  "sign_etf_clean_st = \<lparr>
    etf_st_nop        = clean_edge_tree_st (sign_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. clean_edge_tree_st (sign_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. clean_edge_tree_st (sign_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. clean_edge_tree_st (sign_tf_st (EA_AssumeNot b))),
    etf_st_enter      = clean_edge_tree_st (sign_tf_st EA_Enter),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

definition kgen_combine_rread :: "pp \<Rightarrow> pp \<Rightarrow> sign st \<Rightarrow> (pp \<times> sign st, sign st, sign st) strategy_tree" where
  "kgen_combine_rread cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let callee = kgen_ec ctx sc in
       Side callee (restrict_global_st sc)
         (QueryL (ex, callee) (\<lambda>se.
           let res = restrict_local_st sc \<squnion> restrict_global_st (se \<squnion> g) in
           Side ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

definition sign_etf_retain_st :: "(unit, sign st) effectful_st_transfer" where
  "sign_etf_retain_st = \<lparr>
    etf_st_nop        = retain_edge_tree_st (sign_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. retain_edge_tree_st (sign_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. retain_edge_tree_st (sign_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. retain_edge_tree_st (sign_tf_st (EA_AssumeNot b))),
    etf_st_enter      = retain_edge_tree_st (sign_tf_st EA_Enter),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

definition kgen_combine_st ::
  "pp \<Rightarrow> pp \<Rightarrow> sign st \<Rightarrow> (pp \<times> sign st, sign st, sign st) strategy_tree"
where
  "kgen_combine_st cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let caller = sc \<squnion> g;
           callee = kgen_ec ctx caller in
       Side callee (restrict_global_st caller)
         (QueryL (ex, callee) (\<lambda>se.
           let res = restrict_local_st caller \<squnion> restrict_global_st (se \<squnion> g) in
           Side ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

definition kgen_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "kgen_eqs = side_cfg_T_eff_cmp_st id
                (\<lambda>c cc ex. kgen_combine_st cc ex c)
                kgen_cfg sign_etf_st bot bot cinit_sign_st"

definition kgen_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "kgen_solution = TD_side_always_join_Interp_solve kgen_eqs (cfg_exit kgen_cfg, bot)"

definition kgen_retain_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "kgen_retain_eqs = side_cfg_T_eff_cmp_st id
                       (\<lambda>c cc ex. kgen_combine_st cc ex c)
                       kgen_cfg sign_etf_retain_st bot bot cinit_sign_st"

definition kgen_retain_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "kgen_retain_solution = TD_side_always_join_Interp_solve kgen_retain_eqs (cfg_exit kgen_cfg, bot)"

definition kgen_ctx_zero :: "sign st" where
  "kgen_ctx_zero = Abs_st (SBot, SZero, [])"

definition kgen_ctx_merged :: "sign st" where
  "kgen_ctx_merged = Abs_st (SBot, SZero, [(''G'', SNonNeg)])"

end
