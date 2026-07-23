theory Interval_DG
  imports
    "Voblint_Analysis.DG_LTR_Sound"
    Interval_Transfer
begin

section \<open>Interval on the heterogeneous DG spine\<close>

text \<open>
  Interval is a diagonal DG instance: answer and side domains both use the
  existing interval carrier, so the native interface is \<^const>\<open>unit_dg_spec\<close>.
  The resulting collecting theorem has the same statement shape as the
  homogeneous exit theorem, but it is now derived from \<^locale>\<open>sound_dg_spec\<close>.
\<close>

interpretation ivl_dg: sound_dg_spec "unit_dg_spec ivl_tf" gamma_unit
  by (rule sound_dg_spec_unit[OF ivl_is_sound_transfer])

subsection \<open>Native endpoint\<close>

definition ivl_dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "ivl_dg_gamma sigma v = ivl_dg.dg_gamma sigma v"

definition ivl_dg_generator ::
  "cfg \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit, unit, (ivl abs_state, ivl abs_state) dg_state) eqsT"
where
  "ivl_dg_generator g bot0 s0d s0g = ivl_dg.dg_gen g bot0 s0d s0g"

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
  shows "ltr_collect g S0 v \<subseteq> ivl_dg_gamma sigma v"
  unfolding ivl_dg_gamma_def
  by (rule ivl_dg.dg_post_solution_collect_sound_ltr
        [OF pp[unfolded ivl_dg_generator_def] cover_entry cover_edge cover_enter cover_combine
            finI finC sound0[folded gamma_unit_def]])

end
