theory Sign_DG
  imports
    "Voblint_Core.DG_LTR_Sound"
    Sign_Transfer
begin

section \<open>Sign on the heterogeneous DG spine\<close>

text \<open>Sign is the diagonal D/G instance: answers and side effects use the same
  abstract-state domain. The entry transfer therefore combines the caller answer and
  global side effect before binding parameters. All generator and collecting results
  follow from the generic locale; only transfer soundness is domain-specific.\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
begin

interpretation sign_dg: sound_dg_spec "unit_dg_spec_for gs (sign_tf_for gs)" gamma_unit gs
  by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for])

end

subsection \<open>Native endpoint\<close>

text \<open>
  The joint concretization at a program point and the configured equation system,
  named natively so consumers do not reach through the locale prefix.
\<close>

definition sign_dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow> (sign abs_state, sign abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "sign_dg_gamma \<equiv> sound_dg_spec.dg_gamma gamma_unit"

definition sign_dg_generator ::
  "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state
   \<Rightarrow> (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) eqsT"
where
  "sign_dg_generator gs \<equiv> sound_dg_spec.dg_gen (unit_dg_spec_for gs (sign_tf_for gs))"

text \<open>
  Public DG API for the Sign domain, generic in the classifier \<open>gs\<close>.  The
  sublocale interpretation rewrites facts inherited from @{locale sound_dg_spec}
  into this native vocabulary, so the exported theorem below cites the generic
  collecting-soundness fact directly with no manual unfold/fold bridging.
\<close>
locale sign_dg_api =
  fixes gs :: "vname \<Rightarrow> bool"

sublocale sign_dg_api \<subseteq> sound_dg_spec_ltr_for "unit_dg_spec_for gs (sign_tf_for gs)" gamma_unit gs
  rewrites "sound_dg_spec.dg_gamma gamma_unit = sign_dg_gamma"
       and "sound_dg_spec.dg_gen (unit_dg_spec_for gs (sign_tf_for gs)) = sign_dg_generator gs"
  apply (unfold sound_dg_spec_ltr_for_def)
   apply (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for])
  apply (simp add: sign_dg_gamma_def)
  apply (simp add: sign_dg_generator_def)
  done

context sign_dg_api
begin

text \<open>
  Trace-native collecting soundness from a post-solution of the configured generator.
\<close>

theorem sign_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (sign_dg_generator gs g bot0 s0d s0g) x sigma vars"
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
  shows "ltr_collect gs g S0 v \<subseteq> sign_dg_gamma sigma v"
  by (rule dg_post_solution_collect_sound_ltr_for
        [OF pp cover_entry cover_edge cover_enter cover_combine
            finI finC sound0[folded gamma_unit_def]])

end

end
