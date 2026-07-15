theory Interval_DG
  imports
    "Voblint_Analysis.DG_Context_Soundness"
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
  Collecting soundness from a post-solution of the configured generator, with the
  same premises as the homogeneous Interval theorem and the same conclusion shape.
\<close>

theorem ivl_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (ivl_dg_generator g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine: "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines g \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges g)"
    and no_enter: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> \<not> is_enter_action a"
    and finC: "finite (combines g)"
    and sound0: "S0 \<subseteq> \<lbrakk>s0d \<squnion> s0g\<rbrakk>"
  shows "cfg_collect g S0 v \<subseteq> ivl_dg_gamma sigma v"
  unfolding ivl_dg_gamma_def
  by (rule ivl_dg.dg_post_solution_collect_sound
        [OF pp[unfolded ivl_dg_generator_def] cover_entry cover_edge cover_combine
            finE no_enter finC sound0[folded gamma_unit_def]])

subsection \<open>Keyed context probe\<close>

text \<open>
  The same diagonal DG instance also proves a nontrivial context-sensitive
  collecting theorem: one abstract solution serves two boolean contexts, and the
  result is still read through the DG accessors rather than through a
  homogeneous compatibility layer.
\<close>

lemma ivl_dg_two_context_sound:
  fixes sigma :: "pp \<times> bool + bool \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state"
  assumes pfT: "ivl_dg.dg_postfix_c g True s0dT s0gT sigma"
    and pfF: "ivl_dg.dg_postfix_c g False s0dF s0gF sigma"
    and soundT: "S \<subseteq> \<lbrakk>s0dT \<squnion> s0gT\<rbrakk>"
    and soundF: "S \<subseteq> \<lbrakk>s0dF \<squnion> s0gF\<rbrakk>"
  shows "cfg_collect g S v \<subseteq> ivl_dg.dg_gamma_c sigma True v"
    and "cfg_collect g S v \<subseteq> ivl_dg.dg_gamma_c sigma False v"
  using ivl_dg.dg_postfix_c_collect_sound[OF pfT soundT[folded gamma_unit_def]]
    ivl_dg.dg_postfix_c_collect_sound[OF pfF soundF[folded gamma_unit_def]]
  by blast+

end
