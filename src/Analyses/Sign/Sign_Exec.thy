theory Sign_Exec
  imports
    "Voblint_Exec.Exec_St_Restriction_Refinement"
    "Voblint_Nonrelational.Numeric_Ops"
    Sign_Transfer
begin

section \<open>Sign per-domain seam: executable transfer mirror and commutation\<close>

instance sign :: bounded_warrowing ..

text \<open>
  \<open>afilter_sign_st\<close> / \<open>bfilter_sign_st\<close> commute with the abstract filters
  through @{const fun_of_resolved_st_q_for}; the generic executable mirror
  provides the shared induction.
\<close>

lift_definition top_sign_st :: "sign resolved_st_q" is "(STop, STop, [])" .

lemma lookup_top_sign_st [simp]:
  "fun_of_resolved_st_q_for gs top_sign_st x = STop"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_sign_st:
  "fun_of_resolved_st_q_for gs top_sign_st = (\<lambda>_. STop)"
  by (rule ext) simp

lift_definition cinit_sign_st :: "sign resolved_st_q" is "(STop, SZero, [])" .

lemma lookup_cinit_sign_st [simp]:
  "fun_of_resolved_st_q_for gs cinit_sign_st x =
   (if gs x then SZero else STop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_sign_st:
  "fun_of_resolved_st_q_for gs cinit_sign_st =
   (\<lambda>x. if gs x then SZero else STop)"
  by (rule ext) simp

lemma lookup_cinit_sign_st_for:
  "fun_of_resolved_st_q_for gs cinit_sign_st x =
   (if gs x then SZero else STop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_sign_st_for:
  "fun_of_resolved_st_q_for gs cinit_sign_st =
   (\<lambda>x. if gs x then SZero else STop)"
  by (rule ext) simp

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>
  The executable mirror of \<open>sign_tf_abs\<close>/\<open>enter_sign_for\<close>, parametric in the
  classifier.

  \<open>sign_ops\<close>, Sign's primitive bundle, is defined beside the abstract transfer in
  \<^theory>\<open>Voblint_Analysis_Sign.Sign_Transfer\<close>, so both layers read one value.
  The two constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close> instantiated at it, not independent
  definitions; Interval, Parity, Congruence and each of the Int product's three
  refinement modes instantiate the same two at their own bundles. The guard
  transfer needs no third: \<^const>\<open>generic_tf_st_for\<close> reads \<open>n_bfilter\<close> off the
  bundle directly, so naming that projection separately would only rename
  \<^const>\<open>branch_sign_st\<close>.
\<close>

definition sign_enter_st_for ::
  "(vname => bool) => call_info =>
   sign resolved_st_q => sign resolved_st_q" where
  "sign_enter_st_for = generic_enter_st_for sign_ops"

lemma sign_enter_st_for_eq [simp]:
  "sign_enter_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_sign e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q STop s)"
  by (simp add: sign_enter_st_for_def generic_enter_st_for_def)

definition sign_tf_st_for ::
  "(vname => bool) => edge_action =>
   sign resolved_st_q => sign resolved_st_q" where
  "sign_tf_st_for = generic_tf_st_for sign_ops"

lemmas sign_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of sign_ops, folded sign_tf_st_for_def]

text \<open>The Nop/Assign executable-abstract correspondence facts, mirroring
  \<open>ivl_tf_st_for_nop_agree\<close>/\<open>ivl_tf_st_for_assign_agree\<close> for the interval
  domain: given only scoped input agreement (and, for a write, that the
  written expression's value already agrees), the executable step agrees
  with the abstract step at every location the scope covers.\<close>

lemma sign_tf_st_for_nop_agree:
  fixes s_exec :: "sign resolved_st_q" and s_abs :: "sign abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs EA_Nop s_exec) location =
      sign_tf_abs EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: sign_tf.op_defs)

lemma sign_tf_st_for_assign_agree:
  fixes y :: vname and a :: exp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_sign a (fun_of_resolved_st_q_for gs s_exec) = aval_sign a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs (EA_Assign y a) s_exec) location =
      sign_tf_abs (EA_Assign y a) s_abs (location_vname location)"
proof (cases "location_vname location = y")
  case True
  then have "location = location_of gs y" using canonical by simp
  then show ?thesis using val_agree True by (simp add: sign_tf.op_defs)
next
  case False
  have neq: "location \<noteq> location_of gs y"
  proof
    assume eq: "location = location_of gs y"
    have "location_vname location = y" using eq by (simp add: location_of_def)
    with False show False by simp
  qed
  show ?thesis
    using agree[OF location_in] neq False by (simp add: sign_tf.op_defs)
qed

lemma sign_tf_st_for_ret_none_agree:
  fixes s_exec :: "sign resolved_st_q" and s_abs :: "sign abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs (EA_Ret None p) s_exec) location =
      sign_tf_abs (EA_Ret None p) s_abs (location_vname location)"
  using sign_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: sign_tf.op_defs)

subsection \<open>Classifier-parametric commutation\<close>

text \<open>The classifier-parametric commutation of the executable and abstract sign
  transfer: the registered D/G pipeline for a program with a real declared global
  needs the executable transfer to commute with the abstract transfer at an
  arbitrary classifier \<open>gs\<close>.

  Only the guard is Sign's to discharge. Every other action is settled once for
  any bundle by \<open>sign_tf.tf_st_for_commute\<close>, so what remains is
  \<open>sign_backward_domain\<close>'s own filter commutation, which holds on a live state.\<close>

theorem sign_tf_st_for_commute:
  assumes live: "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (sign_tf_st_for gs a s) =
     sign_tf_abs a (fun_of_resolved_st_q_for gs s)"
  unfolding sign_tf_st_for_def
  by (rule sign_tf.tf_st_for_commute)
     (simp add: sign_backward_domain.branch_st_commute[OF live])

lemma enter_frame_sign_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q STop s) =
   enter_frame_sign_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: sign_tf.op_defs)

lemma sign_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (sign_enter_st_for gs ci s) =
   enter_sign_ci_for gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: sign_tf.op_defs enter_binding_def enter_frame_def
                enter_frame_sign_st_for_commute)

end

