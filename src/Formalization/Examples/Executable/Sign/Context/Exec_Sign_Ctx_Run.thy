theory Exec_Sign_Ctx_Run
  imports Exec_Context_Run_Common Exec_Sign_Run
begin

section \<open>Executable semantic entry-state context analysis (sign)\<close>

text \<open>
  A runnable witness that the context-indexed analysis executes through the real
  vendored side solver and separates call contexts.  Contexts are keyed by the
  abstract entry state (\<open>sign st\<close>, finite for sign), the Goblint encoding
  \<open>c = enter#(state)\<close>.

  Procedure \<open>f\<close> doing \<open>Gg := x\<close> is called from two sites with abstract caller
  states \<open>x = SZero\<close> and \<open>x = SPos\<close>.  Context-sensitively the two activations stay
  separate (\<open>Gg = SZero\<close> resp. \<open>SPos\<close>); the monovariant merge of the two returns is
  \<open>SNonNeg\<close>.
\<close>

definition c0 :: "sign st" where "c0 = update_st bot ''x'' SZero"
definition c1 :: "sign st" where "c1 = update_st bot ''x'' SPos"

definition fctx_body :: "sign st \<Rightarrow> sign st" where
  "fctx_body s = assign_st s ''Gg'' (BaseN (AExp.V ''x''))"

definition fctx_solution ::
  "(ctx_pp \<times> sign st) set \<times> ((ctx_pp \<times> sign st) + ctx_glob \<Rightarrow> sign st)" where
  "fctx_solution = ctx_two_call_solution fctx_body c0 c1"

text \<open>Per-context: SZero in context c0, SPos in context c1.\<close>
value "lookup_st (snd fctx_solution (Inl (CtxBody, c0))) ''Gg''"
value "lookup_st (snd fctx_solution (Inl (CtxBody, c1))) ''Gg''"

text \<open>Monovariant merge of the two returns: the lost precision.\<close>
value "lookup_st (snd fctx_solution (Inl (CtxExit, bot))) ''Gg''"

subsection \<open>Machine-checked executable results (code generator)\<close>

lemma fctx_run_context_c0:
  "lookup_st (snd fctx_solution (Inl (CtxBody, c0))) ''Gg'' = SZero"
  unfolding fctx_solution_def fctx_body_def by eval

lemma fctx_run_context_c1:
  "lookup_st (snd fctx_solution (Inl (CtxBody, c1))) ''Gg'' = SPos"
  unfolding fctx_solution_def fctx_body_def by eval

lemma fctx_run_merge:
  "lookup_st (snd fctx_solution (Inl (CtxExit, bot))) ''Gg'' = SNonNeg"
  unfolding fctx_solution_def fctx_body_def by eval

text \<open>
  The executable precision payoff: each context-specialised result is strictly
  below the monovariant merge it would otherwise collapse into.
\<close>

theorem fctx_context_strictly_more_precise:
  "lookup_st (snd fctx_solution (Inl (CtxBody, c0))) ''Gg''
     < lookup_st (snd fctx_solution (Inl (CtxExit, bot))) ''Gg''
   \<and> lookup_st (snd fctx_solution (Inl (CtxBody, c1))) ''Gg''
     < lookup_st (snd fctx_solution (Inl (CtxExit, bot))) ''Gg''"
  unfolding fctx_solution_def fctx_body_def by eval

end
