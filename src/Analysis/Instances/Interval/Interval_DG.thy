theory Interval_DG
  imports
    "Voblint_Core.DG_LTR_Sound"
    Interval_Transfer
begin

section \<open>Interval on the heterogeneous DG spine\<close>

text \<open>
  Interval uses the same carrier for local answers and global side effects.  The diagonal
  specification \<^const>\<open>unit_dg_spec_for\<close> therefore provides its D/G operations, while
  \<^locale>\<open>sound_dg_spec\<close> supplies collecting soundness.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
  assumes reserved: "reserved_ret_var gs"
begin

interpretation ivl_dg: sound_dg_spec "unit_dg_spec_for gs (ivl_tf_for gs)" "gamma_unit gs" gs
  by (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for reserved])

text \<open>The reachability-lifted interpretation is a one-line
  corollary of \<open>sound_dg_spec_unit_for_lifted\<close> -- reuses the existing
  \<open>ivl_is_sound_transfer_for\<close>/\<open>reserved\<close> leaf facts unchanged, with \<^const>\<open>is_bot_state\<close>
  itself as the exact bottom predicate (\<open>refl\<close>). No new DG architecture reasoning.\<close>
interpretation ivl_dg_lifted: sound_dg_spec
  "unit_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)" "gamma_unit_lifted gs" gs
  by (rule sound_dg_spec_unit_for_lifted[OF ivl_is_sound_transfer_for reserved refl])

end

subsection \<open>Native endpoint\<close>

definition ivl_dg_gamma ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "ivl_dg_gamma gs \<equiv> sound_dg_spec.dg_gamma (gamma_unit gs)"

definition ivl_dg_generator ::
  "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit, unit, (ivl abs_state, ivl abs_state) dg_state) eqsT"
where
  "ivl_dg_generator gs \<equiv> sound_dg_spec.dg_gen (unit_dg_spec_for gs (ivl_tf_for gs))"

text \<open>
  Public DG API for the Interval domain, generic in the classifier \<open>gs\<close>.  The
  sublocale interpretation rewrites facts inherited from @{locale sound_dg_spec}
  into this native vocabulary, so the exported theorem below cites the generic
  collecting-soundness fact directly with no manual unfold/fold bridging.
\<close>
locale ivl_dg_api =
  fixes gs :: "vname \<Rightarrow> bool"
  assumes reserved: "reserved_ret_var gs"

sublocale ivl_dg_api \<subseteq> sound_dg_spec_ltr_for "unit_dg_spec_for gs (ivl_tf_for gs)" "gamma_unit gs" gs
  rewrites "sound_dg_spec.dg_gamma (gamma_unit gs) = ivl_dg_gamma gs"
       and "sound_dg_spec.dg_gen (unit_dg_spec_for gs (ivl_tf_for gs)) = ivl_dg_generator gs"
  apply (unfold sound_dg_spec_ltr_for_def)
   apply (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for reserved])
  apply (simp add: ivl_dg_gamma_def)
  apply (simp add: ivl_dg_generator_def)
  done

context ivl_dg_api
begin

text \<open>
  Trace-native collecting soundness from a post-solution of the configured generator.
\<close>

theorem ivl_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (ivl_dg_generator gs g bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover g vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> \<lbrakk>combine_env_abs gs s0d s0g\<rbrakk>"
  shows "ltr_collect gs g S0 v \<subseteq> ivl_dg_gamma gs sigma v"
  by (rule dg_post_solution_collect_sound_ltr_for
        [OF pp cover finI finC sound0[folded gamma_unit_def]])

end

end
