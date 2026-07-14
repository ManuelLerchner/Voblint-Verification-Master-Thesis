theory Exec_Sign_Cmp_Keyed_Retain_EnterMono
  imports Exec_Sign_Cmp_Shared "Voblint_Analysis.TD_Side_Eff_Cmp_Sound"
begin

section \<open>Why ENTER_MONO fails for the value-keyed retain routing\<close>

text \<open>
  The context-indexed keyed soundness theorem
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close> reduces the concrete retain run's
  soundness to the semantic obligation \<open>ENTER_MONO\<close>:

    \<open>s \<in> \<lbrakk>side_env_cmp gcmp \<sigma> (cl, ctx)\<rbrakk>
       \<Longrightarrow> cmp (entdg s) (route cl ctx (route_read_cmp \<sigma> (cl, ctx)))\<close>

  with \<^const>\<open>route_read_cmp\<close> \<open>\<sigma> vk = \<sigma> (Inl vk)\<close> --- the routing already reads the
  \<^emph>\<open>local\<close> slot (the R_read discipline).  This theory records two machine-backed
  obstructions to that obligation for the value-keyed retain run.

  \<^bold>\<open>(A) The context type is not finite.\<close>  The keyed soundness stack requires
  \<open>'g :: finite\<close> (the global key type is enumerated in \<^const>\<open>glob_env_cmp\<close> /
  \<^const>\<open>side_env_cmp\<close>).  The value-keyed context here is \<^typ>\<open>sign st\<close>, which is
  \<^emph>\<open>not\<close> a \<^class>\<open>finite\<close> instance (\<open>No type arity st :: finite\<close>).  So
  \<^const>\<open>side_env_cmp\<close> does not even type-apply to this run; a finite context
  quotient is a prerequisite, independent of ENTER_MONO.

  \<^bold>\<open>(B) The read is dominated by a coarse per-context keyed slot.\<close>  Even granting a
  finite context, the routing precision is invisible to ENTER_MONO's soundness
  gamma, for the reason developed below.
\<close>

subsection \<open>The per-context keyed global slot is coarse\<close>

text \<open>At \<^const>\<open>kgen_ctx_merged\<close> the two value-distinct activations that share this
  context both publish to its single keyed global slot, joining to \<open>SNonNeg\<close> --- a
  non-point sign.\<close>

lemma retain_keyed_merged_G:
  "lookup_st (snd kgen_retain_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg"
  unfolding kgen_retain_solution_def kgen_retain_eqs_def kgen_cfg_def kgen_ec_def
    kgen_ctx_merged_def by eval

subsection \<open>The soundness read is \<open>\<ge>\<close> the coarse keyed slot\<close>

text \<open>For the value-keyed compatibility \<open>(=)\<close> the filtered global read collapses to
  the single keyed slot, so the read \<open>\<sigma>(Inl (cl,ctx)) \<squnion> \<sigma>(Inr ctx)\<close> (which is
  \<^const>\<open>side_env_cmp\<close> after the singleton collapse) is \<open>\<ge> SNonNeg\<close> on \<open>G\<close> at every
  call site of the merged context --- \<^emph>\<open>whatever\<close> the local slot
  \<^const>\<open>route_read_cmp\<close> reads.  The retain invariant \<open>inl_glob_le_keyed_ctx\<close>
  (\<open>local \<le> keyed\<close>) guarantees the keyed slot dominates the join, so routing
  precision cannot sharpen this read.\<close>

definition retain_read_merged :: "pp \<Rightarrow> sign st" where
  "retain_read_merged cl =
     snd kgen_retain_solution (Inl (cl, kgen_ctx_merged))
       \<squnion> snd kgen_retain_solution (Inr kgen_ctx_merged)"

lemma retain_read_merged_G_coarse:
  "SNonNeg \<le> lookup_st (retain_read_merged cl) ''G''"
proof -
  have "SNonNeg = lookup_st (snd kgen_retain_solution (Inr kgen_ctx_merged)) ''G''"
    by (rule retain_keyed_merged_G[symmetric])
  also have "\<dots> \<le> lookup_st (retain_read_merged cl) ''G''"
    unfolding retain_read_merged_def by simp
  finally show ?thesis .
qed

subsection \<open>The read concretises to two distinct point-sign classes\<close>

text \<open>\<open>SNonNeg\<close> (and anything above it) admits both \<open>0\<close> and \<open>2\<close>; \<open>0\<close> lies in the point
  class \<open>SZero\<close> and \<open>2\<close> does not.  So the read at the merged context concretises to
  integers of two different point-sign classes.\<close>

lemma read_admits_two_point_classes:
  "0 \<in> gamma_sign (lookup_st (retain_read_merged cl) ''G'')
   \<and> 2 \<in> gamma_sign (lookup_st (retain_read_merged cl) ''G'')
   \<and> 0 \<in> gamma_sign SZero \<and> 2 \<notin> gamma_sign SZero"
proof -
  have "gamma_sign SNonNeg \<subseteq> gamma_sign (lookup_st (retain_read_merged cl) ''G'')"
    by (rule gamma_sign_mono[OF retain_read_merged_G_coarse[unfolded less_eq_sign_def]])
  thus ?thesis by auto
qed

subsection \<open>Characterisation\<close>

text \<open>
  \<^bold>\<open>The obstruction, machine-backed.\<close>  Package the two facts: the retain read at
  \<^const>\<open>kgen_ctx_merged\<close> concretises to \<open>0\<close> and \<open>2\<close>, which fall in different
  point-sign classes (\<open>0 \<in> SZero\<close>, \<open>2 \<notin> SZero\<close>).  \<open>ENTER_MONO\<close> with \<open>cmp = (=)\<close>
  demands a \<^emph>\<open>single\<close> routed context \<open>c\<^sub>0 = route cl ctx (\<sigma>(Inl (cl,ctx)))\<close> equal to
  \<open>entdg s\<close> for \<^emph>\<open>every\<close> concrete \<open>s\<close> in the read's concretisation.  A value-keyed
  \<open>entdg\<close> --- the digest kind this context uses --- maps the two admitted stores to
  different contexts, so no single \<open>c\<^sub>0\<close> works: ENTER_MONO is false at
  \<^const>\<open>kgen_ctx_merged\<close>.
\<close>

theorem enter_mono_read_not_point:
  "\<exists>n m. n \<in> gamma_sign (lookup_st (retain_read_merged cl) ''G'')
       \<and> m \<in> gamma_sign (lookup_st (retain_read_merged cl) ''G'')
       \<and> n \<in> gamma_sign SZero \<and> m \<notin> gamma_sign SZero"
  using read_admits_two_point_classes by blast

text \<open>
  \<^bold>\<open>The exact missing invariant.\<close>  ENTER_MONO is provable at a context iff the
  soundness read \<^const>\<open>side_env_cmp\<close> there is \<^emph>\<open>entry-digest-uniform\<close> (its
  concretisation lies in one \<open>cmp\<close>-class).  The read is \<open>local \<squnion> keyed\<close>; the retain
  invariant \<open>inl_glob_le_keyed_ctx\<close> gives \<open>local \<le> keyed\<close>, so the read equals the
  \<^emph>\<open>keyed\<close> slot on globals.  Uniformity of the read therefore requires the
  \<^emph>\<open>keyed\<close> slot to be a point --- i.e. the converse invariant \<open>keyed \<le> local\<close>.
  That converse is exactly what a per-context keyed global \<^emph>\<open>cannot\<close> supply when two
  value-distinct activations share a context: they join in the one keyed slot
  (here to \<open>SNonNeg\<close>).  The retain (R_read) discipline sharpens the routing read
  \<^const>\<open>route_read_cmp\<close> \<open>= \<sigma>(Inl \<dots>)\<close> but that precision never reaches ENTER_MONO's
  gamma, which is dominated by the coarse keyed slot.

  \<^bold>\<open>Conclusion.\<close>  ENTER_MONO is \<^emph>\<open>not\<close> provable for the value-keyed retain run under
  the current read architecture --- not for want of a stronger retain-transfer
  lemma, but because the soundness gamma \<^const>\<open>side_env_cmp\<close> reintroduces the
  coarse per-context keyed global.  The minimal architectural change (documented,
  not implemented here) is the D/G/C read split: state ENTER_MONO's gamma over the
  routing read \<^const>\<open>route_read_cmp\<close> (the local slot), decoupled from the
  global-read \<^const>\<open>side_env_cmp\<close> used in the soundness conclusion --- the
  \<open>DGC_ALIGNMENT_ANALYSIS.md\<close> \<section>6b \<open>Obs\<close> / \<open>R_read\<close> separation.  That decoupling
  changes what the theorem certifies (the read the conclusion is stated against),
  so it is a genuine architecture change, not a local proof repair.
\<close>

end
