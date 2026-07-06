theory Exec_Ivl_Ctx_Run
  imports Exec_Ivl_Run
begin

section \<open>Executable semantic entry-state context analysis (interval)\<close>

text \<open>
  The interval analogue of \<open>Exec_Sign_Ctx_Run\<close>: the context-indexed analysis
  EXECUTES through the real vendored side solver and SEPARATES call contexts on the
  interval domain.  Contexts are keyed by the abstract entry state \<open>ivl st\<close> (the
  Goblint encoding \<open>c = enter#(state)\<close>).

  Procedure \<open>f\<close> doing \<open>Gg := x\<close> is called from two sites with abstract caller
  states \<open>x = [0,0]\<close> and \<open>x = [5,5]\<close>.  Context-sensitively the two activations stay
  separate (\<open>Gg = [0,0]\<close> resp. \<open>[5,5]\<close>); the monovariant merge of the two returns is
  \<open>[0,5]\<close> -- the precision the context split recovers.
\<close>

definition d0 :: "ivl st" where "d0 = update_st bot ''x'' (Ivl (Fin 0) (Fin 0))"
definition d1 :: "ivl st" where "d1 = update_st bot ''x'' (Ivl (Fin 5) (Fin 5))"

datatype fp = Fentry | Fbody | Mexit
datatype glob = G0

fun ictx_eqs :: "fp \<times> ivl st \<Rightarrow> (fp \<times> ivl st, glob, ivl st) strategy_tree" where
  "ictx_eqs (Fentry, ctx) = Answer ctx"
| "ictx_eqs (Fbody, ctx) =
     QueryL (Fentry, ctx) (\<lambda>s. Answer (update_st s ''Gg'' (lookup_st s ''x'')))"
| "ictx_eqs (Mexit, _) =
     QueryL (Fbody, d0) (\<lambda>s0. QueryL (Fbody, d1) (\<lambda>s1. Answer (s0 \<squnion> s1)))"

definition ictx_solution ::
  "(fp \<times> ivl st) set \<times> ((fp \<times> ivl st) + glob \<Rightarrow> ivl st)" where
  "ictx_solution = TD_side_always_join_Interp_solve ictx_eqs (Mexit, bot)"

text \<open>Per-context: [0,0] in context d0, [5,5] in context d1.\<close>
value "string_of_ivl (lookup_st (snd ictx_solution (Inl (Fbody, d0))) ''Gg'')"
value "string_of_ivl (lookup_st (snd ictx_solution (Inl (Fbody, d1))) ''Gg'')"

text \<open>Monovariant merge of the two returns: [0,5] -- the lost precision.\<close>
value "string_of_ivl (lookup_st (snd ictx_solution (Inl (Mexit, bot))) ''Gg'')"

subsection \<open>Machine-checked executable results (code generator)\<close>

lemma ictx_run_context_d0:
  "lookup_st (snd ictx_solution (Inl (Fbody, d0))) ''Gg'' = Ivl (Fin 0) (Fin 0)"
  by eval

lemma ictx_run_context_d1:
  "lookup_st (snd ictx_solution (Inl (Fbody, d1))) ''Gg'' = Ivl (Fin 5) (Fin 5)"
  by eval

lemma ictx_run_merge:
  "lookup_st (snd ictx_solution (Inl (Mexit, bot))) ''Gg'' = Ivl (Fin 0) (Fin 5)"
  by eval

text \<open>
  The executable precision payoff on the interval domain: each context-specialised
  result is STRICTLY below the monovariant merge it would otherwise collapse into.
\<close>

theorem ictx_context_strictly_more_precise:
  "lookup_st (snd ictx_solution (Inl (Fbody, d0))) ''Gg''
     < lookup_st (snd ictx_solution (Inl (Mexit, bot))) ''Gg''
   \<and> lookup_st (snd ictx_solution (Inl (Fbody, d1))) ''Gg''
     < lookup_st (snd ictx_solution (Inl (Mexit, bot))) ''Gg''"
  by eval

end
