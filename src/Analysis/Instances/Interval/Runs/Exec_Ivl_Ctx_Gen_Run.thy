theory Exec_Ivl_Ctx_Gen_Run
  imports Exec_Ivl_Run Exec_Ctx_Bridge
begin

section \<open>Generator-driven executable context analysis on a compiled CFG (interval)\<close>

text \<open>
  Interval analogue of the sign witness \<open>Exec_Sign_Ctx_Gen_Run\<close>: the
  context-indexed equation system produced by \<^const>\<open>side_cfg_T_eff_ctx_st\<close> from
  a CFG compiled by \<^const>\<open>compile_prog\<close> runs through the real vendored side
  solver on the interval domain.  Contexts are keyed by the abstract entry state
  \<^typ>\<open>ivl st\<close> with the full caller state as context (\<open>ec ctx sc = sc\<close>).
\<close>

definition igctx_prog :: imp_prog where
  "igctx_prog = \<lbrakk>
     int Gx, G;
     void f() { G := Gx }
     void main() { f() }
   \<rbrakk>"

definition igctx_cfg :: cfg where
  "igctx_cfg = compile_prog (prog_table igctx_prog) (prog_procs igctx_prog) (prog_main igctx_prog)"

definition ivl_ctx_ec :: "ivl st \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "ivl_ctx_ec ctx sc = sc"

definition igctx_eqs :: "(pp \<times> ivl st, unit, ivl st) eqsT" where
  "igctx_eqs = side_cfg_T_eff_ctx_st
                 (\<lambda>c cc ex. unit_combine_tree_ctx_st ivl_ctx_ec cc ex c)
                 igctx_cfg ivl_etf_st bot cinit_ivl_st ()"

definition igctx_solution ::
  "(pp \<times> ivl st) set \<times> ((pp \<times> ivl st) + unit \<Rightarrow> ivl st)" where
  "igctx_solution = TD_side_always_join_Interp_solve igctx_eqs (cfg_exit igctx_cfg, bot)"

value "fst igctx_solution"
value "string_of_ivl (lookup_st (snd igctx_solution (Inr ())) ''G'')"

subsection \<open>Machine-checked runnability (code generator)\<close>

text \<open>
  The generator-built context system materialises context-indexed unknowns over
  \<^typ>\<open>pp \<times> ivl st\<close> and the solver returns: program point \<open>0\<close> at the C-faithful
  entry context is in the solved variable set.
\<close>

lemma igctx_context_materialized:
  "(0, cinit_ivl_st) \<in> fst igctx_solution"
  by eval

text \<open>
  The shared global slot carries the value computed through the value-dependent
  combine: \<open>f\<close> writes \<open>G := Gx\<close>, and against the C-faithful seed (\<open>Gx = [0,0]\<close>)
  the analyzer derives \<open>G = [0,0]\<close>.
\<close>

lemma igctx_run_global_G:
  "lookup_st (snd igctx_solution (Inr ())) ''G'' = Ivl (Fin 0) (Fin 0)"
  by eval

end
