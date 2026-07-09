theory Example_Seed_Clean_Context
  imports Voblint_Analysis.Exec_Sign_Cmp_Seed_Sound
begin

section \<open>The Goblint-faithful seeded-clean spine on a two-call program\<close>

text \<open>
  End-to-end demonstration of the seeded-clean (R_read) spine --- the Goblint
  sequential \<open>D/G/C\<close> model --- on the two-call program \<^const>\<open>kgen_prog\<close>
  (\<open>f(){G:=G+G}; main(){G:=0; f(); G:=1; f()}\<close>).  The spine combines three pieces:

    \<^item> the \<^emph>\<open>seeded\<close> generator \<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close> with the faithful
      seed \<^const>\<open>restrict_global_st\<close> --- Goblint's \<open>sidel (FunctionEntry f, fc) v\<close>
      putting the caller's globals into the callee-entry \<^emph>\<open>local\<close>;
    \<^item> the \<^emph>\<open>clean\<close> transfer \<^const>\<open>sign_etf_clean_st\<close> --- reading only the local
      \<open>D.t\<close>, never rejoining the published global;
    \<^item> the \<^emph>\<open>R_read\<close> combine \<^const>\<open>kgen_combine_rread\<close> --- selecting the callee
      context from the local.

  Its soundness is certified against the context-sliced collecting semantics by
  \<open>clean_ctx_collect_rread\<close>; the digest-propagation obligations reduce generically
  through \<open>clean_ctx_collect_rread_head\<close>.  The retain (\<open>\<squnion> g\<close>) run is preserved as
  the sound conservative baseline.
\<close>

subsection \<open>The run\<close>

text \<open>The seeded-clean generator solves the program via the vendored side solver.\<close>

lemma seed_clean_example_runs: "fst kgen_seed_clean_solution \<noteq> {}"
  by (rule kgen_seed_clean_runs)

subsection \<open>Precision: the global-derived context split\<close>

text \<open>
  The two call sites hold value-distinct globals (\<open>G = 0\<close> then \<open>G = 1\<close>).  The seed
  carries each into the callee-entry local, so the clean transfer reads a
  \<^emph>\<open>point\<close>: caller local \<^const>\<open>SZero\<close> at the first call site (pp 4), \<^const>\<open>SPos\<close>
  at the second (pp 7).
\<close>

lemma seed_clean_example_caller_locals:
  "lookup_st (snd kgen_seed_clean_solution (Inl (4, bot::sign st))) ''G'' = SZero
   \<and> lookup_st (snd kgen_seed_clean_solution (Inl (7, bot::sign st))) ''G'' = SPos"
  by (rule kgen_seed_clean_caller_locals)

text \<open>
  Consequently the two activations land in \<^emph>\<open>separate point contexts\<close>: the first
  call context reads \<open>G = SZero\<close> (GZero), the second \<open>G = SPos\<close> (GPos).
\<close>

theorem seed_clean_example_context_split:
  "lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''G'' = SPos"
  by (rule kgen_seed_clean_precision)

subsection \<open>Contrast: the retain baseline merges the two contexts\<close>

text \<open>
  Under the retain (\<open>\<squnion> g\<close>) run the two value-distinct activations share one keyed
  context slot, joining to the non-point \<^const>\<open>SNonNeg\<close> --- the \<open>fctx\<close> obstruction.
  The seeded-clean context slots are \<^emph>\<open>strictly\<close> below it (\<^const>\<open>SZero\<close>,
  \<^const>\<open>SPos\<close> \<open><\<close> \<^const>\<open>SNonNeg\<close>): the \<^const>\<open>SNonNeg\<close> obstruction is dissolved.
\<close>

theorem seed_clean_example_sharper_than_retain:
  "lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''G'' = SPos
   \<and> lookup_st (snd kgen_retain_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg
   \<and> SZero < SNonNeg \<and> SPos < SNonNeg"
  using kgen_seed_clean_precision retain_keyed_merged_G sign_strict_precision by simp

text \<open>
  \<^bold>\<open>Summary.\<close>  The seeded-clean spine is the Goblint-faithful model: it keeps globals
  flow-sensitively in the callee local (via the seed), reads only that local (the
  clean transfer), and routes contexts off it (R_read).  Its soundness against
  \<^const>\<open>cfg_collect_ctx\<close> is certified (\<open>clean_ctx_collect_rread\<close>); its precision
  strictly exceeds the retain baseline on the global-derived context split, which
  is preserved here as \<^const>\<open>kgen_retain_solution\<close>.
\<close>

end
