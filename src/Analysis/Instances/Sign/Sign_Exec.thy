theory Sign_Exec
  imports "Voblint_Exec.Exec_Refinement" Numeric_Ops Sign_Domain
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
  "fun_of_resolved_st_q_for is_global top_sign_st x = STop"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_sign_st:
  "fun_of_resolved_st_q_for is_global top_sign_st = (\<lambda>_. STop)"
  by (rule ext) simp

lift_definition cinit_sign_st :: "sign resolved_st_q" is "(STop, SZero, [])" .

lemma lookup_cinit_sign_st [simp]:
  "fun_of_resolved_st_q_for is_global cinit_sign_st x =
   (if is_global x then SZero else STop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_sign_st:
  "fun_of_resolved_st_q_for is_global cinit_sign_st =
   (\<lambda>x. if is_global x then SZero else STop)"
  by (rule ext) simp

lemma lookup_cinit_sign_st_for [simp]:
  "fun_of_resolved_st_q_for gs cinit_sign_st x =
   (if gs x then SZero else STop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_sign_st_for:
  "fun_of_resolved_st_q_for gs cinit_sign_st =
   (\<lambda>x. if gs x then SZero else STop)"
  by (rule ext) simp

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>The executable mirror of \<open>sign_tf_for\<close>/\<open>enter_sign_for\<close>, parametric in
  the classifier, following the same pattern as \<open>ivl_tf_st_for\<close>/
  \<open>ivl_enter_st_for\<close> for the interval domain.\<close>

text \<open>
  \<open>sign_ops\<close> bundles Sign's own primitives for the generic
  \<open>generic_branch_st_for\<close>/\<open>generic_enter_st_for\<close> construction
  (\<^theory>\<open>Voblint_Analysis.Numeric_Ops\<close>): \<open>branch_sign_st_for\<close>/\<open>sign_enter_st_for\<close>
  below are exactly those generic constructions instantiated at \<open>sign_ops\<close>,
  not independent definitions -- Interval and Parity instantiate the same
  generic pair at their own primitives.
\<close>

definition sign_ops :: "sign numeric_ops" where
  "sign_ops = \<lparr> n_aval = aval_sign, n_bfilter = branch_sign_st, n_top = STop \<rparr>"

definition branch_sign_st_for ::
  "(vname => bool) => exp => bool => sign resolved_st_q => sign resolved_st_q" where
  "branch_sign_st_for = generic_branch_st_for sign_ops"

lemma branch_sign_st_for_eq [simp]:
  "branch_sign_st_for gs b pol s = branch_sign_st gs b pol s"
  by (simp add: branch_sign_st_for_def generic_branch_st_for_def sign_ops_def)

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
  by (simp add: sign_enter_st_for_def generic_enter_st_for_def sign_ops_def)

fun sign_tf_st_for ::
  "(vname => bool) => edge_action =>
   sign resolved_st_q => sign resolved_st_q" where
    "sign_tf_st_for gs EA_Nop s = s"
  | "sign_tf_st_for gs (EA_Assign x a) s =
       update_resolved_st_q s (location_of gs x)
         (aval_sign a (fun_of_resolved_st_q_for gs s))"
  | "sign_tf_st_for gs (EA_Special sc x) s =
       update_resolved_st_q s (location_of gs x)
         (case sc of
            Nondet_Int => STop
          | Min a b => sign_min (aval_sign a (fun_of_resolved_st_q_for gs s))
                                 (aval_sign b (fun_of_resolved_st_q_for gs s))
          | Max a b => sign_max (aval_sign a (fun_of_resolved_st_q_for gs s))
                                 (aval_sign b (fun_of_resolved_st_q_for gs s)))"
  | "sign_tf_st_for gs (EA_Assume b) s =
       branch_sign_st_for gs b True s"
  | "sign_tf_st_for gs (EA_AssumeNot b) s =
       branch_sign_st_for gs b False s"
  | "sign_tf_st_for gs (EA_Ret None p) s = s"
  | "sign_tf_st_for gs (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of gs ret_var)
         (aval_sign a (fun_of_resolved_st_q_for gs s))"
  | "sign_tf_st_for gs (EA_Check cnd) s = s"

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
      apply_tf (sign_tf_for gs) EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: sign_tf_for_def skip_sign_def)

lemma sign_tf_st_for_assign_agree:
  fixes y :: vname and a :: exp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_sign a (fun_of_resolved_st_q_for gs s_exec) = aval_sign a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs (EA_Assign y a) s_exec) location =
      apply_tf (sign_tf_for gs) (EA_Assign y a) s_abs (location_vname location)"
proof (cases "location_vname location = y")
  case True
  then have "location = location_of gs y" using canonical by simp
  then show ?thesis using val_agree True by (simp add: sign_tf_for_def assign_sign_def)
next
  case False
  have neq: "location \<noteq> location_of gs y"
  proof
    assume eq: "location = location_of gs y"
    have "location_vname location = y" using eq by (simp add: location_of_def)
    with False show False by simp
  qed
  show ?thesis
    using agree[OF location_in] neq False by (simp add: sign_tf_for_def assign_sign_def)
qed

lemma sign_tf_st_for_ret_none_agree:
  fixes s_exec :: "sign resolved_st_q" and s_abs :: "sign abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs (EA_Ret None p) s_exec) location =
      apply_tf (sign_tf_for gs) (EA_Ret None p) s_abs (location_vname location)"
  using sign_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: sign_tf_for_def skip_sign_def return_sign_def)

subsection \<open>Classifier-parametric commutation\<close>

text \<open>The classifier-parametric commutation of the executable and abstract sign
  transfer, mirroring \<open>parity_tf_st_for_commute\<close>/\<open>parity_enter_st_for_commute\<close>
  for the parity domain: the registered D/G pipeline for a program with a real
  declared global needs the executable transfer to commute with the abstract
  transfer at an arbitrary classifier \<open>gs\<close>.\<close>

theorem sign_tf_st_for_commute:
  assumes "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (sign_tf_st_for gs a s) =
     apply_tf (sign_tf_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by (simp add: sign_tf_for_def skip_sign_def)
next
  case (EA_Assign x e)
  then show ?thesis by (simp add: sign_tf_for_def assign_sign_def)
next
  case (EA_Special sc x)
  then show ?thesis by (auto simp: sign_tf_for_def split: special_call.splits)
next
  case (EA_Assume b)
  then show ?thesis
    using assms by (simp add: sign_tf_for_def sign_backward_domain.branch_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis
    using assms by (simp add: sign_tf_for_def sign_backward_domain.branch_st_commute)
next
  case (EA_Ret ea p)
  then show ?thesis
  proof (cases ea)
    case None
    then show ?thesis using \<open>a = EA_Ret ea p\<close> by (simp add: sign_tf_for_def return_sign_def)
  next
    case (Some av)
    then show ?thesis using \<open>a = EA_Ret ea p\<close> by (simp add: sign_tf_for_def return_sign_def assign_sign_def)
  qed
next
  case (EA_Check c)
  then show ?thesis by (simp add: sign_tf_for_def event_sign_def)
qed

lemma enter_frame_sign_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q STop s) =
   enter_frame_sign_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_frame_sign_for_def)

lemma sign_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (sign_enter_st_for gs ci s) =
   snd (enter\<^sup># (sign_tf_for gs) ci (fun_of_resolved_st_q_for gs s))"
  by (simp add: sign_tf_for_def enter_sign_for_def enter_D_def enter_frame_def
                enter_pair_sign_for_def enter_pair_D_def
                enter_frame_sign_for_def enter_frame_sign_st_for_commute
                fun_of_resolved_st_q_for_enter_frame)

end

