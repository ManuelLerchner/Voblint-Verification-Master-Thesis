theory Int_DG
  imports "Voblint_Core.DG_LTR_Sound" Int_Transfer
begin

section \<open>Composite integer domain on the heterogeneous DG spine\<close>

text \<open>
  Registers each of the three mode-specific transfer bundles
  (\<open>int_tf_never_for\<close>, \<open>int_tf_once_for\<close>, \<open>int_tf_fixpoint_for\<close>) against
  the generic diagonal D/G construction \<open>unit_dg_spec_for\<close>, mirroring the
  abstract layer of Sign's own \<open>Sign_DG\<close>. Soundness follows
  entirely from \<open>sound_dg_spec_unit_for\<close>, already proved generically over
  any \<^locale>\<open>sound_transfer_for\<close> instance: no domain mathematics is added
  here, only registration. The three refinement modes stay separate at this
  layer for the same reason as \<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>:
  three distinct transfer bundles get three distinct D/G registrations,
  rather than one mode-parameterised registration hiding the asymmetry.

  This is the abstract (non-executable) registration only: it establishes
  collecting-semantics soundness for any post-solution of the generated
  equation system, but \<open>vname => int_dom\<close> is not itself code-generatable,
  so no solver run is produced here. An executable endpoint needs a
  per-domain finite-map mirror of this transfer bundle (as Sign's own
  \<open>Sign_Exec\<close> provides for Sign) plus its own agreement proofs -- a
  separate, larger phase, not attempted in this file.
\<close>

context
  fixes gs :: "vname => bool"
  assumes reserved: "reserved_ret_var gs"
begin

interpretation int_never_dg:
  sound_dg_spec "unit_dg_spec_for gs (int_tf_never_for gs)" "gamma_unit gs" gs
  by (rule sound_dg_spec_unit_for[OF int_never_is_sound_transfer_for reserved])

interpretation int_once_dg:
  sound_dg_spec "unit_dg_spec_for gs (int_tf_once_for gs)" "gamma_unit gs" gs
  by (rule sound_dg_spec_unit_for[OF int_once_is_sound_transfer_for reserved])

interpretation int_fixpoint_dg:
  sound_dg_spec "unit_dg_spec_for gs (int_tf_fixpoint_for gs)" "gamma_unit gs" gs
  by (rule sound_dg_spec_unit_for[OF int_fixpoint_is_sound_transfer_for reserved])

end

subsection \<open>Native endpoints, one per refinement mode\<close>

text \<open>
  The joint concretization at a program point and the configured equation
  system, named natively per mode so consumers do not reach through the
  locale prefix, matching \<open>sign_dg_gamma\<close>/\<open>sign_dg_generator\<close>.
\<close>

definition int_never_dg_gamma ::
  "(vname => bool)
   => (pp * unit + unit => (int_dom abs_state, int_dom abs_state) dg_state)
   => pp => store set"
where
  "int_never_dg_gamma gs \<equiv> sound_dg_spec.dg_gamma (gamma_unit gs)"

definition int_never_dg_generator ::
  "(vname => bool) => cfg => int_dom abs_state => int_dom abs_state => int_dom abs_state
   => (pp * unit, unit, (int_dom abs_state, int_dom abs_state) dg_state) eqsT"
where
  "int_never_dg_generator gs \<equiv> sound_dg_spec.dg_gen (unit_dg_spec_for gs (int_tf_never_for gs))"

definition int_once_dg_gamma ::
  "(vname => bool)
   => (pp * unit + unit => (int_dom abs_state, int_dom abs_state) dg_state)
   => pp => store set"
where
  "int_once_dg_gamma gs \<equiv> sound_dg_spec.dg_gamma (gamma_unit gs)"

definition int_once_dg_generator ::
  "(vname => bool) => cfg => int_dom abs_state => int_dom abs_state => int_dom abs_state
   => (pp * unit, unit, (int_dom abs_state, int_dom abs_state) dg_state) eqsT"
where
  "int_once_dg_generator gs \<equiv> sound_dg_spec.dg_gen (unit_dg_spec_for gs (int_tf_once_for gs))"

definition int_fixpoint_dg_gamma ::
  "(vname => bool)
   => (pp * unit + unit => (int_dom abs_state, int_dom abs_state) dg_state)
   => pp => store set"
where
  "int_fixpoint_dg_gamma gs \<equiv> sound_dg_spec.dg_gamma (gamma_unit gs)"

definition int_fixpoint_dg_generator ::
  "(vname => bool) => cfg => int_dom abs_state => int_dom abs_state => int_dom abs_state
   => (pp * unit, unit, (int_dom abs_state, int_dom abs_state) dg_state) eqsT"
where
  "int_fixpoint_dg_generator gs \<equiv> sound_dg_spec.dg_gen (unit_dg_spec_for gs (int_tf_fixpoint_for gs))"

text \<open>
  Public DG API per refinement mode, generic in the classifier \<open>gs\<close>. Each
  sublocale interpretation rewrites facts inherited from
  \<^locale>\<open>sound_dg_spec\<close> into that mode's native vocabulary, so the exported
  collecting-soundness theorem below cites the generic fact directly with no
  manual unfold/fold bridging, mirroring \<open>sign_dg_api\<close>.
\<close>

locale int_never_dg_api =
  fixes gs :: "vname => bool"
  assumes reserved: "reserved_ret_var gs"

sublocale int_never_dg_api \<subseteq>
  sound_dg_spec_ltr_for "unit_dg_spec_for gs (int_tf_never_for gs)" "gamma_unit gs" gs
  rewrites "sound_dg_spec.dg_gamma (gamma_unit gs) = int_never_dg_gamma gs"
       and "sound_dg_spec.dg_gen (unit_dg_spec_for gs (int_tf_never_for gs)) = int_never_dg_generator gs"
  apply (unfold sound_dg_spec_ltr_for_def)
   apply (rule sound_dg_spec_unit_for[OF int_never_is_sound_transfer_for reserved])
  apply (simp add: int_never_dg_gamma_def)
  apply (simp add: int_never_dg_generator_def)
  done

context int_never_dg_api
begin

theorem int_never_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (int_never_dg_generator gs g bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover g vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> \<lbrakk>combine_env_abs gs s0d s0g\<rbrakk>"
  shows "ltr_collect gs g S0 v \<subseteq> int_never_dg_gamma gs sigma v"
  by (rule dg_post_solution_collect_sound_ltr_for
        [OF pp cover finI finC sound0[folded gamma_unit_def]])

end

locale int_once_dg_api =
  fixes gs :: "vname => bool"
  assumes reserved: "reserved_ret_var gs"

sublocale int_once_dg_api \<subseteq>
  sound_dg_spec_ltr_for "unit_dg_spec_for gs (int_tf_once_for gs)" "gamma_unit gs" gs
  rewrites "sound_dg_spec.dg_gamma (gamma_unit gs) = int_once_dg_gamma gs"
       and "sound_dg_spec.dg_gen (unit_dg_spec_for gs (int_tf_once_for gs)) = int_once_dg_generator gs"
  apply (unfold sound_dg_spec_ltr_for_def)
   apply (rule sound_dg_spec_unit_for[OF int_once_is_sound_transfer_for reserved])
  apply (simp add: int_once_dg_gamma_def)
  apply (simp add: int_once_dg_generator_def)
  done

context int_once_dg_api
begin

theorem int_once_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (int_once_dg_generator gs g bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover g vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> \<lbrakk>combine_env_abs gs s0d s0g\<rbrakk>"
  shows "ltr_collect gs g S0 v \<subseteq> int_once_dg_gamma gs sigma v"
  by (rule dg_post_solution_collect_sound_ltr_for
        [OF pp cover finI finC sound0[folded gamma_unit_def]])

end

locale int_fixpoint_dg_api =
  fixes gs :: "vname => bool"
  assumes reserved: "reserved_ret_var gs"

sublocale int_fixpoint_dg_api \<subseteq>
  sound_dg_spec_ltr_for "unit_dg_spec_for gs (int_tf_fixpoint_for gs)" "gamma_unit gs" gs
  rewrites "sound_dg_spec.dg_gamma (gamma_unit gs) = int_fixpoint_dg_gamma gs"
       and "sound_dg_spec.dg_gen (unit_dg_spec_for gs (int_tf_fixpoint_for gs)) = int_fixpoint_dg_generator gs"
  apply (unfold sound_dg_spec_ltr_for_def)
   apply (rule sound_dg_spec_unit_for[OF int_fixpoint_is_sound_transfer_for reserved])
  apply (simp add: int_fixpoint_dg_gamma_def)
  apply (simp add: int_fixpoint_dg_generator_def)
  done

context int_fixpoint_dg_api
begin

theorem int_fixpoint_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (int_fixpoint_dg_generator gs g bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover g vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> \<lbrakk>combine_env_abs gs s0d s0g\<rbrakk>"
  shows "ltr_collect gs g S0 v \<subseteq> int_fixpoint_dg_gamma gs sigma v"
  by (rule dg_post_solution_collect_sound_ltr_for
        [OF pp cover finI finC sound0[folded gamma_unit_def]])

end

subsection \<open>Non-vacuous instantiation witness\<close>

text \<open>
  Each mode's \<open>_dg_api\<close> locale is genuinely satisfiable, not vacuously
  discharged by an unmeetable assumption: the trivial classifier that
  declares nothing global always keeps \<open>ret_var\<close> reserved.
\<close>

lemma int_never_dg_api_trivial_gs: "int_never_dg_api (%_. False)"
  by unfold_locales (simp add: reserved_ret_var_def)

lemma int_once_dg_api_trivial_gs: "int_once_dg_api (%_. False)"
  by unfold_locales (simp add: reserved_ret_var_def)

lemma int_fixpoint_dg_api_trivial_gs: "int_fixpoint_dg_api (%_. False)"
  by unfold_locales (simp add: reserved_ret_var_def)

end
