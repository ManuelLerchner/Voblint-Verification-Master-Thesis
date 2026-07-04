theory Exec_Sign_Ctx_Run
  imports Exec_Sign_Run
begin

section \<open>Executable semantic entry-state context analysis (sign)\<close>

text \<open>
  A runnable witness that the context-indexed analysis EXECUTES through the real
  vendored side solver and SEPARATES call contexts.  The soundness instance keys
  contexts by the concrete entry-store digest (an infinite store set, not
  code-generatable); the executable analysis keys them by the ABSTRACT entry state
  (\<open>sign st\<close>, finite for sign) -- the genuine Goblint encoding \<open>c = enter#(state)\<close>.

  Program shape: a procedure \<open>f\<close> doing \<open>Gg := x\<close> is called from two sites with
  abstract caller states \<open>x = SZero\<close> and \<open>x = SPos\<close>.  Context-sensitively the two
  activations stay separate (\<open>Gg = SZero\<close> resp. \<open>SPos\<close>); the monovariant merge of
  the two returns is \<open>STop\<close> -- the precision the context split recovers.
\<close>

definition c0 :: "sign st" where "c0 = update_st bot ''x'' SZero"
definition c1 :: "sign st" where "c1 = update_st bot ''x'' SPos"

datatype fp = Fentry | Fbody | Mexit

text \<open>
  Unknown = \<open>fp \<times> sign st\<close> (program point paired with the abstract entry context).
  \<open>Fentry\<close> at context \<open>c\<close> answers \<open>c\<close>; \<open>Fbody\<close> queries its own context entry and
  performs \<open>Gg := x\<close>; \<open>Mexit\<close> joins the two context-specialised returns.
\<close>

fun fctx_eqs :: "fp \<times> sign st \<Rightarrow> (fp \<times> sign st, glob, sign st) strategy_tree" where
  "fctx_eqs (Fentry, ctx) = Answer ctx"
| "fctx_eqs (Fbody, ctx) =
     QueryL (Fentry, ctx) (\<lambda>s. Answer (assign_st s ''Gg'' (BaseN (AExp.V ''x''))))"
| "fctx_eqs (Mexit, _) =
     QueryL (Fbody, c0) (\<lambda>s0. QueryL (Fbody, c1) (\<lambda>s1. Answer (s0 \<squnion> s1)))"

definition fctx_solution ::
  "(fp \<times> sign st) set \<times> ((fp \<times> sign st) + glob \<Rightarrow> sign st)" where
  "fctx_solution = TD_side_always_join_Interp_solve fctx_eqs (Mexit, bot)"

text \<open>Per-context: SZero in context c0, SPos in context c1.\<close>
value "lookup_st (snd fctx_solution (Inl (Fbody, c0))) ''Gg''"
value "lookup_st (snd fctx_solution (Inl (Fbody, c1))) ''Gg''"

text \<open>Monovariant merge of the two returns: the lost precision.\<close>
value "lookup_st (snd fctx_solution (Inl (Mexit, bot))) ''Gg''"

subsection \<open>Machine-checked executable results (code generator)\<close>

text \<open>
  The \<open>value\<close> printouts above, sealed as theorems via the code generator: the
  solver actually returns these per-context values, proved by \<open>eval\<close>.
\<close>

lemma fctx_run_context_c0: "lookup_st (snd fctx_solution (Inl (Fbody, c0))) ''Gg'' = SZero"
  by eval

lemma fctx_run_context_c1: "lookup_st (snd fctx_solution (Inl (Fbody, c1))) ''Gg'' = SPos"
  by eval

lemma fctx_run_merge: "lookup_st (snd fctx_solution (Inl (Mexit, bot))) ''Gg'' = SNonNeg"
  by eval

text \<open>
  The executable precision payoff: each context-specialised result is STRICTLY
  below the monovariant merge it would otherwise collapse into.
\<close>

theorem fctx_context_strictly_more_precise:
  "lookup_st (snd fctx_solution (Inl (Fbody, c0))) ''Gg''
     < lookup_st (snd fctx_solution (Inl (Mexit, bot))) ''Gg''
   \<and> lookup_st (snd fctx_solution (Inl (Fbody, c1))) ''Gg''
     < lookup_st (snd fctx_solution (Inl (Mexit, bot))) ''Gg''"
  by eval

end
