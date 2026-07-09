theory Exec_Ivl_Ctx_Run
  imports Exec_Context_Run_Common Exec_Ivl_Run
begin

section \<open>Executable semantic entry-state context analysis (interval)\<close>

text \<open>
  The interval instance of the shared two-context run scaffold.  Contexts are
  keyed by the abstract entry state \<open>ivl st\<close>, the Goblint encoding
  \<open>c = enter#(state)\<close>.

  Procedure \<open>f\<close> doing \<open>Gg := x\<close> is called from two sites with abstract caller
  states \<open>x = [0,0]\<close> and \<open>x = [5,5]\<close>.  Context-sensitively the two activations stay
  separate (\<open>Gg = [0,0]\<close> resp. \<open>[5,5]\<close>); the monovariant merge of the two returns is
  \<open>[0,5]\<close>.
\<close>

definition d0 :: "ivl st" where "d0 = update_st bot ''x'' (Ivl (Fin 0) (Fin 0))"
definition d1 :: "ivl st" where "d1 = update_st bot ''x'' (Ivl (Fin 5) (Fin 5))"

definition ictx_body :: "ivl st \<Rightarrow> ivl st" where
  "ictx_body s = update_st s ''Gg'' (lookup_st s ''x'')"

definition ictx_solution ::
  "(ctx_pp \<times> ivl st) set \<times> ((ctx_pp \<times> ivl st) + ctx_glob \<Rightarrow> ivl st)" where
  "ictx_solution = ctx_two_call_solution ictx_body d0 d1"

text \<open>Per-context: [0,0] in context d0, [5,5] in context d1.\<close>
value "string_of_ivl (lookup_st (snd ictx_solution (Inl (CtxBody, d0))) ''Gg'')"
value "string_of_ivl (lookup_st (snd ictx_solution (Inl (CtxBody, d1))) ''Gg'')"

text \<open>Monovariant merge of the two returns: [0,5].\<close>
value "string_of_ivl (lookup_st (snd ictx_solution (Inl (CtxExit, bot))) ''Gg'')"

subsection \<open>Machine-checked executable results (code generator)\<close>

lemma ictx_run_context_d0:
  "lookup_st (snd ictx_solution (Inl (CtxBody, d0))) ''Gg'' = Ivl (Fin 0) (Fin 0)"
  unfolding ictx_solution_def ictx_body_def by eval

lemma ictx_run_context_d1:
  "lookup_st (snd ictx_solution (Inl (CtxBody, d1))) ''Gg'' = Ivl (Fin 5) (Fin 5)"
  unfolding ictx_solution_def ictx_body_def by eval

lemma ictx_run_merge:
  "lookup_st (snd ictx_solution (Inl (CtxExit, bot))) ''Gg'' = Ivl (Fin 0) (Fin 5)"
  unfolding ictx_solution_def ictx_body_def by eval

text \<open>
  The executable precision payoff on the interval domain: each context-specialised
  result is strictly below the monovariant merge it would otherwise collapse into.
\<close>

theorem ictx_context_strictly_more_precise:
  "lookup_st (snd ictx_solution (Inl (CtxBody, d0))) ''Gg''
     < lookup_st (snd ictx_solution (Inl (CtxExit, bot))) ''Gg''
   \<and> lookup_st (snd ictx_solution (Inl (CtxBody, d1))) ''Gg''
     < lookup_st (snd ictx_solution (Inl (CtxExit, bot))) ''Gg''"
  unfolding ictx_solution_def ictx_body_def by eval

end
