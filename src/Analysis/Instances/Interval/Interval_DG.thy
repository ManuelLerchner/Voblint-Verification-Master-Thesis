theory Interval_DG
  imports
    "Voblint_Core.DG_LTR_Sound"
    Interval_Transfer
begin

section \<open>Interval on the heterogeneous DG spine\<close>

text \<open>
  Interval uses the same carrier for local answers and global side effects.  The diagonal
  specification \<^const>\<open>unit_dg_spec\<close> therefore provides its D/G operations, while
  \<^locale>\<open>sound_dg_spec\<close> supplies collecting soundness.
\<close>

interpretation ivl_dg: sound_dg_spec "unit_dg_spec ivl_tf" gamma_unit is_global
  by (rule sound_dg_spec_unit[OF ivl_is_sound_transfer])

subsection \<open>Native endpoint\<close>

definition ivl_dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "ivl_dg_gamma \<equiv> sound_dg_spec.dg_gamma gamma_unit"

definition ivl_dg_generator ::
  "cfg \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit, unit, (ivl abs_state, ivl abs_state) dg_state) eqsT"
where
  "ivl_dg_generator \<equiv> sound_dg_spec.dg_gen (unit_dg_spec ivl_tf)"

text \<open>
  Public DG API for the Interval domain.  The sublocale interpretation
  rewrites facts inherited from @{locale sound_dg_spec} into this native
  vocabulary, so the exported theorem below cites the generic
  collecting-soundness fact directly with no manual unfold/fold bridging.
  The trailing bare interpretation flattens the locale so consumers see the
  same top-level names as before; \<open>ivl_dg\<close> above stays untouched for the
  existing \<open>ivl_dg.\<close>-qualified call sites.
\<close>
locale ivl_dg_api

sublocale ivl_dg_api \<subseteq> sound_dg_spec_ltr "unit_dg_spec ivl_tf" gamma_unit
  rewrites "sound_dg_spec.dg_gamma gamma_unit = ivl_dg_gamma"
       and "sound_dg_spec.dg_gen (unit_dg_spec ivl_tf) = ivl_dg_generator"
  apply (unfold sound_dg_spec_ltr_def)
   apply (rule sound_dg_spec_unit[OF ivl_is_sound_transfer])
  apply (simp add: ivl_dg_gamma_def)
  apply (simp add: ivl_dg_generator_def)
  done

context ivl_dg_api
begin

text \<open>
  Trace-native collecting soundness from a post-solution of the configured generator.
\<close>

theorem ivl_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (ivl_dg_generator g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_enter:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> \<lbrakk>s0d \<squnion> s0g\<rbrakk>"
  shows "ltr_collect is_global g S0 v \<subseteq> ivl_dg_gamma sigma v"
  by (rule dg_post_solution_collect_sound_ltr
        [OF pp cover_entry cover_edge cover_enter cover_combine
            finI finC sound0[folded gamma_unit_def]])

end

interpretation ivl_dg_api .

end
