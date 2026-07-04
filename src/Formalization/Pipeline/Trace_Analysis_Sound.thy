theory Trace_Analysis_Sound
  imports "Voblint_Analysis.Analysis_Sound" "Voblint_CFG.CFG_Collect_Trace"
begin

section \<open>Trace overlay as a soundness morphism\<close>

text \<open>
  Composes the interprocedural projection
    alpha_last (cfg_collect_trace g S v) \<subseteq> cfg_collect g S v
  with the unified interprocedural soundness
    cfg_collect g S v \<le> gamma_state (env v)
  to obtain: the analyzer is sound w.r.t. the interprocedural TRACE semantics,
  projected to last stores.  alpha_last is thus a soundness-preserving morphism --
  no separate trace soundness stack is needed.

  This is the digest extension point: a digest-indexed combine_at refining
  cfg_collect_trace keeps the same shape

      alpha_last (precise trace collecting) \<subseteq> cfg_collect \<le> gamma_state env,

  so the global-read soundness a digest hook adds plugs in below the projection
  without forking a new soundness chain.
\<close>

context sound_transfer
begin

theorem trace_analysis_sound:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "alpha_last (cfg_collect_trace g S v) \<le> \<lbrakk>env v\<rbrakk>"
proof -
  have proj: "alpha_last (cfg_collect_trace g S v) \<le> cfg_collect g S v"
    by (rule alpha_last_cfg_collect_trace_le)
  have st: "cfg_collect g S v \<le> \<lbrakk>env v\<rbrakk>"
    by (rule unified_post_fixpoint_sound[OF fin finC post_fp S_sound])
  from proj st show ?thesis by (rule subset_trans)
qed

text \<open>
  History-sensitive read soundness over reaching traces.

  For ANY variable x (global or local) and ANY interprocedural trace tr reaching
  program point v, the value that x holds at the end of tr is contained in the
  analysis result's concretization \<gamma> (env v x).  The ''history'' is the
  reaching trace itself: this is the soundness of reading a variable's value over
  the set of reaching interprocedural traces, which is exactly the
  flow-insensitive global read once specialised to a G-prefixed variable and
  joined over program points.

  It is an immediate consequence of trace_analysis_sound (last tr is in
  alpha_last of the trace set, hence in \<lbrakk>env v\<rbrakk>) and the per-coordinate
  shape of gamma_state.

  The precision half -- digest-indexed (context-sensitive) summaries that keep
  callers apart -- refines cfg_collect_trace with a digest hook. It strengthens
  the trace set (smaller), so this soundness statement is preserved unchanged.
  That refinement is reaching_global_read_sound_d below.
\<close>
theorem reaching_global_read_sound:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes tr: "tr \<in> cfg_collect_trace g S v"
  shows "(last tr) x \<in> gamma (env v x)"
proof -
  have mem: "last tr \<in> alpha_last (cfg_collect_trace g S v)"
    using tr unfolding alpha_last_def by blast
  have le: "alpha_last (cfg_collect_trace g S v) \<le> \<lbrakk>env v\<rbrakk>"
    by (rule trace_analysis_sound[OF fin finC post_fp S_sound])
  from mem le have "last tr \<in> \<lbrakk>env v\<rbrakk>" by blast
  thus ?thesis unfolding gamma_state_def by blast
qed


text \<open>
  Digest-refined corollary: soundness of the digest-REFINED reaching-trace read.
  cfg_collect_trace_d (any digest dg, any compatibility cmp) is a subset of
  cfg_collect_trace (cfg_collect_trace_d_subset), so the soundness core
  transfers unchanged: the SAME analysis env soundly over-approximates every
  digest-restricted reaching trace.  The digest hook buys precision at zero
  soundness cost.
\<close>
theorem reaching_global_read_sound_d:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes tr: "tr \<in> cfg_collect_trace_d dg cmp g S v"
  shows "(last tr) x \<in> gamma (env v x)"
proof -
  have "tr \<in> cfg_collect_trace g S v"
    using tr cfg_collect_trace_d_subset by blast
  thus ?thesis
    using reaching_global_read_sound[OF fin finC post_fp S_sound] by blast
qed

text \<open>
  The digest-INDEXED analyzer contract.

  A digest-indexed env  envd :: pp => 'd => 'a abs_state  assigns each
  (program point, reader-digest) pair its own abstract state.  It is sound when,
  at every point and digest, it over-approximates exactly the reaching traces
  compatible with that digest (reaching_compat).  digest_read_sound is then the
  history-sensitive global read: a reader holding digest d sees only the values
  produced along digest-compatible traces.  flat_env_is_digest_sound shows the
  existing (flow-insensitive) analyzer is the trivial constant-in-d
  digest-indexed env -- so the contract is realizable with no instantiation gap;
  precision is the freedom to pick a TIGHTER envd
  (see Example_Trace_Digest_Precision).
\<close>
definition digest_env_sound ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set
     \<Rightarrow> (pp \<Rightarrow> 'd \<Rightarrow> 'a abs_state) \<Rightarrow> bool" where
  "digest_env_sound dg cmp g S envd =
     (\<forall>d v. alpha_last (reaching_compat dg cmp d g S v) \<le> \<lbrakk>envd v d\<rbrakk>)"

theorem digest_read_sound:
  fixes envd :: "pp \<Rightarrow> 'd \<Rightarrow> 'a abs_state"
  assumes snd: "digest_env_sound dg cmp g S envd"
  assumes tr: "tr \<in> cfg_collect_trace g S v"
  assumes cm: "cmp (dg tr) d"
  shows "(last tr) x \<in> gamma (envd v d x)"
proof -
  have "tr \<in> reaching_compat dg cmp d g S v"
    using tr cm unfolding reaching_compat_def by blast
  hence "last tr \<in> alpha_last (reaching_compat dg cmp d g S v)"
    unfolding alpha_last_def by blast
  with snd have "last tr \<in> \<lbrakk>envd v d\<rbrakk>"
    unfolding digest_env_sound_def by blast
  thus ?thesis unfolding gamma_state_def by blast
qed

theorem flat_env_is_digest_sound:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "digest_env_sound dg cmp g S (\<lambda>v d. env v)"
  unfolding digest_env_sound_def
proof (intro allI)
  fix d v
  have "reaching_compat dg cmp d g S v \<subseteq> cfg_collect_trace g S v"
    unfolding reaching_compat_def by blast
  hence "alpha_last (reaching_compat dg cmp d g S v) \<le> alpha_last (cfg_collect_trace g S v)"
    unfolding alpha_last_def by blast
  also have "... \<le> \<lbrakk>env v\<rbrakk>"
    by (rule trace_analysis_sound[OF fin finC post_fp S_sound])
  finally show "alpha_last (reaching_compat dg cmp d g S v) \<le> \<lbrakk>(\<lambda>v d. env v) v d\<rbrakk>"
    by simp
qed

text \<open>
  The digest soundness contract, stated against the named context-collecting
  semantics \<open>cfg_collect_ctx\<close> (CFG_Collect_Trace) instead of the unfolded
  \<open>alpha_last (reaching_compat ...)\<close>.  A one-step rewrite via
  \<open>cfg_collect_ctx_reaching_compat\<close>; both are literally the same proposition.  This
  is the \<open>(pp, c)\<close>-indexed shape a context-sensitive solver must satisfy.
\<close>
theorem context_collect_sound:
  "digest_env_sound dg cmp g S envd
     = (\<forall>c v. cfg_collect_ctx dg cmp g S v c \<le> \<lbrakk>envd v c\<rbrakk>)"
  unfolding digest_env_sound_def cfg_collect_ctx_reaching_compat
  by (rule refl)

end

end

