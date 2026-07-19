theory Sign_DG
  imports
    "Voblint_Analysis.DG_LTR_Sound"
    Sign_Transfer
begin

section \<open>Sign on the heterogeneous DG spine\<close>

text \<open>
  The monovariant Sign analysis as a native \<^locale>\<open>sound_dg_spec\<close> instance --- the
  same carrier-opaque spine the mixed Sign/Interval analysis and Retain ride.
  Sign is the \<^emph>\<open>diagonal\<close> case: answer and side domains coincide
  (\<open>D = G = sign abs_state\<close>), so the spec is \<^const>\<open>unit_dg_spec\<close> and the joint
  concretization is \<^const>\<open>gamma_unit\<close>.  The entry frame is the caller's \<open>D\<close> read by the
  FM 2026 caller-state \<open>enter\<close>: \<^const>\<open>unit_dg_spec\<close>'s \<open>dgs_enter\<close> is \<^const>\<open>unit_step\<close>
  applied to the sign transfer, which consumes \<open>d \<squnion> g\<close> --- the caller state --- with
  no context-indexed seed.

  Every generator and collecting fact is inherited from the locale; the sign-specific
  content is only \<open>sign_is_sound_transfer\<close>.
\<close>

interpretation sign_dg: sound_dg_spec "unit_dg_spec sign_tf" gamma_unit
  by (rule sound_dg_spec_unit[OF sign_is_sound_transfer])

subsection \<open>Native endpoint\<close>

text \<open>
  The joint concretization at a program point and the configured equation system,
  named natively so consumers do not reach through the locale prefix.
\<close>

definition sign_dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow> (sign abs_state, sign abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "sign_dg_gamma sigma v = sign_dg.dg_gamma sigma v"

definition sign_dg_generator ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state
   \<Rightarrow> (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) eqsT"
where
  "sign_dg_generator g bot0 s0d s0g = sign_dg.dg_gen g bot0 s0d s0g"

text \<open>
  Trace-native collecting soundness from a post-solution of the configured generator.
\<close>

theorem sign_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (sign_dg_generator g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine: "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines g \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and sound0: "S0 \<subseteq> \<lbrakk>s0d \<squnion> s0g\<rbrakk>"
  shows "ltr_collect g S0 v \<subseteq> sign_dg_gamma sigma v"
  unfolding sign_dg_gamma_def
  by (rule sign_dg.dg_post_solution_collect_sound_ltr
        [OF pp[unfolded sign_dg_generator_def] cover_entry cover_edge cover_combine
            finE finC sound0[folded gamma_unit_def]])

end
