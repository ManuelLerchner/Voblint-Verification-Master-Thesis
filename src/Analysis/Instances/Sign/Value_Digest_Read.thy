theory Value_Digest_Read
  imports
    Value_Digest_Reader
    Sign_Domain
begin

section \<open>Sign instance of the value-carried digest reader\<close>

text \<open>
  The value-derived digest family instantiated at the sign domain: a two-point
  \<^emph>\<open>mode\<close> projected from the sign of a ghost local \<open>''mode''\<close>.  All machinery ---
  the read @{const value_digest_reader.vd_obs}, its reduced shape, and the
  context-sliced collecting soundness --- is the generic
  \<^locale>\<open>value_digest_reader\<close>; the only sign-specific content is the projection
  \<open>mode_decode\<close>.  A different domain reuses the locale with its own decode.
\<close>

subsection \<open>The finite mode partition\<close>

datatype mode = MZero | MOne

instance mode :: finite
proof
  show "finite (UNIV :: mode set)"
  proof (rule finite_subset[of _ "{MZero, MOne}"])
    show "(UNIV :: mode set) \<subseteq> {MZero, MOne}" using mode.exhaust by blast
    show "finite {MZero, MOne}" by simp
  qed
qed

text \<open>An \<^class>\<open>enum\<close> instance so the mode-filtered read \<^const>\<open>glob_env_cmp\<close>
  code-generates: its filtered join folds over the finite mode key type.\<close>
instantiation mode :: enum
begin
definition "enum_mode = [MZero, MOne]"
definition "enum_all_mode P \<longleftrightarrow> P MZero \<and> P MOne"
definition "enum_ex_mode P \<longleftrightarrow> P MZero \<or> P MOne"
instance
proof
  show "(UNIV :: mode set) = set enum_class.enum"
    using mode.exhaust by (auto simp: enum_mode_def)
qed (auto simp: enum_mode_def enum_all_mode_def enum_ex_mode_def, (metis mode.exhaust)+)
end

subsection \<open>Decode and compatibility (the only sign-specific content)\<close>

text \<open>The mode carried by a slot: the sign of the ghost variable, collapsed to two points.
  \<^const>\<open>SPos\<close> is mode one; every other sign --- including the unset default \<^const>\<open>STop\<close> ---
  is the initial mode zero, so an unkeyed initial global lands in \<^term>\<open>MZero\<close>, not \<^term>\<open>MOne\<close>.\<close>
definition mode_decode :: "sign \<Rightarrow> mode" where
  "mode_decode s = (if s = SPos then MOne else MZero)"

text \<open>A read at mode \<open>d\<close> sees exactly the partition keyed by \<open>d\<close>.\<close>
definition mode_compatible :: "mode \<Rightarrow> mode \<Rightarrow> bool" where
  "mode_compatible d g = (d = g)"

lemma mode_compatible_singleton: "{g. mode_compatible d g} = {d}"
  unfolding mode_compatible_def by auto

subsection \<open>The sign interpretation and its re-exposed reader\<close>

text \<open>
  Interpret the generic reader at \<^const>\<open>mode_decode\<close> and the ghost variable \<open>''mode''\<close>.
  The read and every soundness theorem are inherited; the names below re-expose the
  locale facts under the projection-specific names the runs and examples use.
\<close>
interpretation mode: value_digest_reader mode_decode "''mode''" .

abbreviation mode_reader ::
  "((nat \<times> 'c) + mode \<Rightarrow> sign abs_state) \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> mode" where
  "mode_reader \<equiv> mode.vd_reader"

abbreviation mode_obs ::
  "((nat \<times> 'c) + mode \<Rightarrow> sign abs_state) \<Rightarrow> (nat \<times> 'c) \<Rightarrow> sign abs_state" where
  "mode_obs \<equiv> mode.vd_obs"

lemmas mode_obs_reduce = mode.vd_obs_reduce
lemmas mode_obs_global = mode.vd_obs_global
lemmas mode_collect_ctx_sound_bot = mode.vd_collect_ctx_sound_bot
lemmas mode_collect_ctx_sound_bot_reduced = mode.vd_collect_ctx_sound_bot_reduced
lemmas mode_obs_eq_side_env_cmp = mode.vd_obs_eq_side_env_cmp

end
