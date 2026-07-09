theory Example_Global_Ctx_Read_Precision
  imports "Voblint_Analysis.Global_Cmp_Read" "Voblint_Analysis.Sign_Domain"
begin

section \<open>Read-layer witness: cmp-filtered globals separate two call contexts\<close>

text \<open>
  \<^bold>\<open>Sound read-layer witness.\<close>  This is the sound counterpart to the
  \<open>Exec_Sign_Ctx_Seeded_Run\<close> demo: it recovers per-context precision from the
  \<^emph>\<open>global\<close> state, which \<^const>\<open>enter_state\<close> preserves, rather than from caller
  locals, which it erases.

  \<^const>\<open>enter_state\<close> resets every local to \<open>0\<close> and keeps only the globals
  (\<open>enter_state s n = (if is_global n then s n else 0)\<close>).  So the only information a
  parameterless callee receives from its caller is the global state; the context
  used to key a call must therefore be global-derived.  Reading it back per context
  is exactly \<^const>\<open>glob_env_cmp\<close>.

  Two call contexts keyed by \<^typ>\<open>bool\<close>: context \<open>False\<close> enters with global
  \<open>G = 0\<close> (\<^const>\<open>SZero\<close>), context \<open>True\<close> with \<open>G = 1\<close> (\<^const>\<open>SPos\<close>).  The
  cmp-filtered read (\<open>cmp = (=)\<close>, one compatible key per context) recovers the
  per-context value; the join-all \<^const>\<open>glob_env\<close> merges them to
  \<^const>\<open>SNonNeg\<close> --- the monovariant precision loss.

  This isolates the read discipline of the redesign: with no generator or
  analyzer solution in play, \<^const>\<open>glob_env_cmp\<close> already carries the context
  precision that \<^const>\<open>glob_env\<close> destroys.  Because the split reads only globals,
  it is sound where the seeded caller-local split is not.  The end-to-end \<open>by eval\<close>
  precision claim over an actual keyed analysis result is deferred to the
  executable keyed generator.
\<close>

definition wsig :: "nat + bool \<Rightarrow> sign abs_state" where
  "wsig x = (case x of Inl _ \<Rightarrow> (\<lambda>_. SBot)
                     | Inr False \<Rightarrow> (\<lambda>_. SZero)
                     | Inr True \<Rightarrow> (\<lambda>_. SPos))"

lemma keys_False: "{k. (=) False k} = {False}" by auto
lemma keys_True:  "{k. (=) True k} = {True}"  by auto

subsection \<open>Per-context reads are exact\<close>

lemma read_ctx_False: "glob_env_cmp (=) False wsig = (\<lambda>_. SZero)"
proof -
  have "glob_env_cmp (=) False wsig = wsig (Inr False)"
    using keys_False by (rule glob_env_cmp_singleton)
  thus ?thesis by (simp add: wsig_def)
qed

lemma read_ctx_True: "glob_env_cmp (=) True wsig = (\<lambda>_. SPos)"
proof -
  have "glob_env_cmp (=) True wsig = wsig (Inr True)"
    using keys_True by (rule glob_env_cmp_singleton)
  thus ?thesis by (simp add: wsig_def)
qed

subsection \<open>Join-all read merges the two contexts (monovariant)\<close>

lemma read_join_all_at: "glob_env wsig ''G'' = SNonNeg"
  by eval

subsection \<open>The filtered read separates contexts; the join-all cannot\<close>

lemma contexts_separated:
  "glob_env_cmp (=) False wsig \<noteq> glob_env_cmp (=) True wsig"
  by (simp add: read_ctx_False read_ctx_True fun_eq_iff)

text \<open>
  Both context reads sit below the join-all read (precision, not soundness):
  \<^const>\<open>glob_env_cmp\<close> is never coarser than \<^const>\<open>glob_env\<close>.
\<close>
lemma filtered_below_join_all:
  "glob_env_cmp (=) cx wsig \<le> glob_env wsig"
  by (rule glob_env_cmp_le_glob_env)

subsection \<open>Contrast: this split is sound, the caller-local seeded split is not\<close>

text \<open>
  The \<open>Exec_Sign_Ctx_Seeded_Run\<close> demo obtains a similar two-way split
  (\<open>{SZero, SPos}\<close> against the monovariant \<^const>\<open>STop\<close>), but keys it on caller
  locals under \<open>ent = id\<close>.  \<^const>\<open>enter_state\<close> erases those locals, so that split
  reconstructs information the callee never receives and does not over-approximate
  the concrete semantics --- it is unsound.

  The split here keys on \<^const>\<open>SZero\<close> / \<^const>\<open>SPos\<close> \<^emph>\<open>global\<close> values read back
  through  \<^const>\<open>glob_env_cmp\<close>.  Those globals survive \<^const>\<open>enter_state\<close>, so
  \<open>filtered_below_join_all\<close> makes the split a precision refinement of the
  join-all read with no soundness cost.  Soundness of the full keyed analysis rests
  on \<open>CMP_SOUND\<close> in \<open>post_fixpoint_sound_at_ctx_semantic_cmp_final\<close>; this witness
  discharges only its read layer.
\<close>

text \<open>
  \<^bold>\<open>Two distinct ``seeded'' constructions --- do not conflate.\<close>  The unsound split
  named above is \<open>Exec_Sign_Ctx_Seeded_Run\<close>, which seeds the callee-entry local from
  the \<^emph>\<open>full caller local\<close> (\<open>seed_ec ctx sc = restrict_local_st sc\<close>, \<open>ent = id\<close>);
  \<^const>\<open>enter_state\<close> erases those locals, so it reconstructs information the callee
  never receives.  The \<^emph>\<open>seeded-clean\<close> spine (\<open>Exec_Sign_Cmp_Seed_Sound\<close>,
  \<open>Example_Seed_Clean_Context\<close>) is a \<^emph>\<open>different\<close> construction: it seeds the
  callee-entry local from the caller \<^emph>\<open>global\<close> (\<open>kgen_ec ctx sc = restrict_global_st
  sc\<close>), which \<^const>\<open>enter_state\<close> \<^emph>\<open>preserves\<close> --- the same global-derived channel
  this witness uses.  It is certified sound (\<open>clean_ctx_collect_rread\<close>) over the
  R_read local slot.  So ``the seeded caller-local split is unsound'' applies only to
  the \<^emph>\<open>local\<close>-seed run, not to the global-seeded seeded-clean spine.
\<close>

end
