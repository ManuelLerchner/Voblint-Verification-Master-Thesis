theory Exec_Sign_Mode_Value_Run
  imports Value_Digest_Read Exec_Sign_Cmp_Keyed_Run Exec_Sign_Run
begin

section \<open>Executable value-carried mode digest: the solver is the source of truth\<close>

text \<open>
  A value-carried mode-digest run.  A
  finite \<^typ>\<open>mode\<close> partitions the global \<open>G\<close>; each partition slot \<^term>\<open>Inr MZero\<close> /
  \<^term>\<open>Inr MOne\<close> is written by the vendored \<^const>\<open>TD_side_always_join_Interp_solve\<close>.  The
  \<^emph>\<open>projection reader\<close> \<^const>\<open>mode_obs\<close> --- which recovers the mode from the solved local variable
  \<open>''mode''\<close> and reads only that partition --- is run on the solver's own output.  It separates
  the two modes where the context-blind join-all merges them.  Read soundness is the keystone
  \<^theory_text>\<open>mode_obs_eq_side_env_cmp\<close>: under the alignment the projection read equals the
  certified context read.
\<close>

subsection \<open>The mode-keyed side-effecting equation system\<close>

text \<open>
  Local point \<^term>\<open>(0::nat, ctx)\<close> is the driver; it queries both mode activations so the
  solver materialises both partition slots.  Point \<^term>\<open>(Suc n, ctx)\<close> is the mode worker:
  it side-effects \<open>G\<close> (valued by the context's sign) to its own partition \<^term>\<open>Inr ctx\<close> and
  answers a local state whose local \<open>''mode''\<close> carries that same sign --- so the projection
  reader recovers the context from the solved local slot.
\<close>

fun mode_eqs :: "nat \<times> mode \<Rightarrow> (nat \<times> mode, mode, sign st) strategy_tree" where
  "mode_eqs (0, ctx) =
     QueryL (1, MZero) (\<lambda>_. QueryL (1, MOne) (\<lambda>_. Answer bot))"
| "mode_eqs (Suc n, ctx) =
     (let m = (if ctx = MZero then SZero else SPos)
      in Side ctx (update_st bot ''G'' m) (Answer (update_st bot ''mode'' m)))"

definition mode_solution :: "(nat \<times> mode) set \<times> ((nat \<times> mode) + mode \<Rightarrow> sign st)" where
  "mode_solution = TD_side_always_join_Interp_solve mode_eqs (0, MZero)"

subsection \<open>The solver computes separated mode partitions\<close>

lemma mode_runs: "fst mode_solution \<noteq> {}"
  unfolding mode_solution_def by eval

lemma slot_MZero: "lookup_st (snd mode_solution (Inr MZero)) ''G'' = SZero"
  unfolding mode_solution_def by eval

lemma slot_MOne: "lookup_st (snd mode_solution (Inr MOne)) ''G'' = SPos"
  unfolding mode_solution_def by eval

lemma slot_join_all:
  "lookup_st (snd mode_solution (Inr MZero) \<squnion> snd mode_solution (Inr MOne)) ''G'' = SNonNeg"
  unfolding mode_solution_def by eval

subsection \<open>The projection reader recovers the per-mode value\<close>

text \<open>The solved environment as a plain-function abstract state, feeding \<^const>\<open>mode_obs\<close>.\<close>
definition mode_env :: "(nat \<times> mode) + mode \<Rightarrow> sign abs_state" where
  "mode_env = (\<lambda>k. fun_of_st (snd mode_solution k))"

text \<open>
  The projection read at each activation.  \<^const>\<open>mode_obs\<close> decodes the local \<open>''mode''\<close> from
  the local slot and reads exactly that partition: \<^const>\<open>SZero\<close> under \<^const>\<open>MZero\<close>,
  \<^const>\<open>SPos\<close> under \<^const>\<open>MOne\<close>.  Rewriting by \<^theory_text>\<open>mode_obs_reduce\<close> exposes the
  code-generatable local-join-single-slot shape.
\<close>

lemma read_mode_zero: "mode_obs mode_env (1, MZero) ''G'' = SZero"
  unfolding mode_obs_reduce mode_env_def mode_solution_def by eval

lemma read_mode_one: "mode_obs mode_env (1, MOne) ''G'' = SPos"
  unfolding mode_obs_reduce mode_env_def mode_solution_def by eval

text \<open>The monovariant loss, isolated to the read: the context-blind join-all read merges the
  two modes back to \<^const>\<open>SNonNeg\<close> --- the precision the mode keying recovers.\<close>
lemma read_join_all: "glob_env_cmp (\<lambda>_ _. True) MZero mode_env ''G'' = SNonNeg"
  unfolding mode_env_def mode_solution_def by eval

theorem mode_reads_point_sensitive:
  "mode_obs mode_env (1, MZero) ''G'' = SZero
   \<and> mode_obs mode_env (1, MOne) ''G'' = SPos
   \<and> mode_obs mode_env (1, MZero) ''G'' < glob_env_cmp (\<lambda>_ _. True) MZero mode_env ''G''"
proof -
  have "SZero < SNonNeg" by eval
  thus ?thesis using read_mode_zero read_mode_one read_join_all by simp
qed

subsection \<open>The executable read is the certified context read\<close>

text \<open>
  The alignment invariant holds on the solved environment: the local \<open>''mode''\<close> decoded at each
  activation equals its context.  This is \<^const>\<open>mode_decode\<close> of the local slot; the solver
  answered \<open>''mode'' := m\<close> with \<open>m\<close> the context's sign.
\<close>

lemma mode_align_zero: "mode_decode (mode_env (Inl (1, MZero)) ''mode'') = MZero"
  unfolding mode_env_def mode_solution_def mode_decode_def by eval

lemma mode_align_one: "mode_decode (mode_env (Inl (1, MOne)) ''mode'') = MOne"
  unfolding mode_env_def mode_solution_def mode_decode_def by eval

text \<open>
  Hence, by the keystone \<^theory_text>\<open>mode_obs_eq_side_env_cmp\<close>, the projection read at each
  activation \<^emph>\<open>is\<close> the certified context read \<^const>\<open>side_env_cmp\<close> --- the value the keyed
  generator soundness theorem \<^theory_text>\<open>side_cfg_T_eff_cmp_collect_sound_gen\<close> over-approximates.
  The executable value-carried analysis is the one whose soundness is proved.
\<close>
theorem exec_read_is_certified_read:
  "mode_obs mode_env (1, MZero) = side_env_cmp (=) mode_env (1, MZero)
   \<and> mode_obs mode_env (1, MOne) = side_env_cmp (=) mode_env (1, MOne)"
  by (rule conjI;
      rule mode_obs_eq_side_env_cmp;
      simp only: mode_align_zero mode_align_one)

end
