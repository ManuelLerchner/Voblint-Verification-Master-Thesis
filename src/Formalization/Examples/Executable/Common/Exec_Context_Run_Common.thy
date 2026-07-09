theory Exec_Context_Run_Common
  imports Voblint_Analysis.Exec_St "TD.TD_side_upd_rule"
begin

section \<open>Shared executable two-context run scaffold\<close>

text \<open>
  A compact equation-system skeleton for executable context-sensitivity witnesses.
  The unknown is a program point paired with an abstract entry context.  Entry
  answers the context, body transforms that context, and exit joins the two
  context-specialised body results.  Concrete example theories instantiate the
  two contexts and the body transfer for a specific domain.
\<close>

datatype ctx_pp = CtxEntry | CtxBody | CtxExit
datatype ctx_glob = CtxGlobal

fun ctx_two_call_eqs ::
  "('d::bounded_warrowing st \<Rightarrow> 'd st) \<Rightarrow> 'd st \<Rightarrow> 'd st \<Rightarrow>
   ctx_pp \<times> 'd st \<Rightarrow> (ctx_pp \<times> 'd st, ctx_glob, 'd st) strategy_tree"
where
  "ctx_two_call_eqs body ctx0 ctx1 (CtxEntry, ctx) = Answer ctx"
| "ctx_two_call_eqs body ctx0 ctx1 (CtxBody, ctx) =
     QueryL (CtxEntry, ctx) (\<lambda>s. Answer (body s))"
| "ctx_two_call_eqs body ctx0 ctx1 (CtxExit, _) =
     QueryL (CtxBody, ctx0) (\<lambda>s0.
       QueryL (CtxBody, ctx1) (\<lambda>s1. Answer (s0 \<squnion> s1)))"

definition ctx_two_call_solution ::
  "('d::bounded_warrowing st \<Rightarrow> 'd st) \<Rightarrow> 'd st \<Rightarrow> 'd st \<Rightarrow>
   (ctx_pp \<times> 'd st) set \<times> ((ctx_pp \<times> 'd st) + ctx_glob \<Rightarrow> 'd st)"
where
  "ctx_two_call_solution body ctx0 ctx1 =
     TD_side_always_join_Interp_solve (ctx_two_call_eqs body ctx0 ctx1) (CtxExit, bot)"

end
