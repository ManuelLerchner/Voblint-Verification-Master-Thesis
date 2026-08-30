theory Parity_Exec
  imports "Voblint_Exec.Exec_Refinement" Numeric_Ops Parity_Transfer
begin

section \<open>Parity executable seam: transfer mirror and commutation\<close>

instance parity :: bounded_warrowing ..

lift_definition top_parity_st :: "parity resolved_st_q" is "(PTop, PTop, [])" .

lemma lookup_top_parity_st [simp]:
  "fun_of_resolved_st_q_for is_global top_parity_st x = PTop"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_parity_st:
  "fun_of_resolved_st_q_for is_global top_parity_st = (\<lambda>_. PTop)"
  by (rule ext) simp

lift_definition cinit_parity_st :: "parity resolved_st_q" is "(PTop, PEven, [])" .

lemma lookup_cinit_parity_st [simp]:
  "fun_of_resolved_st_q_for is_global cinit_parity_st x =
   (if is_global x then PEven else PTop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_parity_st:
  "fun_of_resolved_st_q_for is_global cinit_parity_st =
   (\<lambda>x. if is_global x then PEven else PTop)"
  by (rule ext) simp

lemma lookup_cinit_parity_st_for [simp]:
  "fun_of_resolved_st_q_for gs cinit_parity_st x =
   (if gs x then PEven else PTop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_parity_st_for:
  "fun_of_resolved_st_q_for gs cinit_parity_st =
   (\<lambda>x. if gs x then PEven else PTop)"
  by (rule ext) simp

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>The executable mirror of \<open>parity_tf_for\<close>/\<open>enter_parity_for\<close>, parametric
  in the classifier, following the same pattern as \<open>sign_tf_st_for\<close>/
  \<open>sign_enter_st_for\<close> for the sign domain. Parity's branch transfer is the
  identity (\<open>branch_parity_def\<close>), so unlike the sign mirror there is no
  separate \<open>bfilter\<close>-based executable step to parametrize.\<close>

text \<open>
  \<open>parity_ops\<close> bundles Parity's own primitives for the generic
  \<open>generic_enter_st_for\<close> construction (\<^theory>\<open>Voblint_Analysis.Numeric_Ops\<close>), the
  same way \<open>sign_ops\<close>/\<open>ivl_ops\<close> do for Sign/Interval. Parity's branch
  transfer is the identity, so unlike Sign/Interval there is no
  \<open>branch_parity_st_for\<close> to generalize -- only \<open>n_bfilter\<close>'s VALUE would be
  the identity function, and nothing here needs to name that value
  separately since \<open>generic_branch_st_for\<close> is never applied to Parity.
\<close>

definition parity_ops :: "parity numeric_ops" where
  "parity_ops = \<lparr> n_aval = aval_parity, n_bfilter = (\<lambda>_ _ _ s. s), n_top = PTop \<rparr>"

definition parity_enter_st_for ::
  "(vname => bool) => call_info =>
   parity resolved_st_q => parity resolved_st_q" where
  "parity_enter_st_for = generic_enter_st_for parity_ops"

lemma parity_enter_st_for_eq [simp]:
  "parity_enter_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_parity e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q PTop s)"
  by (simp add: parity_enter_st_for_def generic_enter_st_for_def parity_ops_def)

fun parity_tf_st_for ::
  "(vname => bool) => edge_action =>
   parity resolved_st_q => parity resolved_st_q" where
    "parity_tf_st_for gs EA_Nop s = s"
  | "parity_tf_st_for gs (EA_Assign x a) s =
       update_resolved_st_q s (location_of gs x)
         (aval_parity a (fun_of_resolved_st_q_for gs s))"
  | "parity_tf_st_for gs (EA_Special sc x) s =
       update_resolved_st_q s (location_of gs x)
         (case sc of
            Nondet_Int => PTop
          | Min a b => parity_min (aval_parity a (fun_of_resolved_st_q_for gs s))
                                   (aval_parity b (fun_of_resolved_st_q_for gs s))
          | Max a b => parity_max (aval_parity a (fun_of_resolved_st_q_for gs s))
                                   (aval_parity b (fun_of_resolved_st_q_for gs s)))"
  | "parity_tf_st_for gs (EA_Assume b) s = s"
  | "parity_tf_st_for gs (EA_AssumeNot b) s = s"
  | "parity_tf_st_for gs (EA_Ret None p) s = s"
  | "parity_tf_st_for gs (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of gs ret_var)
         (aval_parity a (fun_of_resolved_st_q_for gs s))"
  | "parity_tf_st_for gs (EA_Check cnd) s = s"

theorem parity_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_tf_st_for gs a s) =
   apply_tf (parity_tf_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by (simp add: parity_tf_for_def skip_parity_def)
next
  case (EA_Assign x e)
  then show ?thesis by (simp add: parity_tf_for_def assign_parity_def)
next
  case (EA_Special sc x)
  then show ?thesis by (auto simp: parity_tf_for_def split: special_call.splits)
next
  case (EA_Assume b)
  then show ?thesis by (simp add: parity_tf_for_def branch_parity_def)
next
  case (EA_AssumeNot b)
  then show ?thesis by (simp add: parity_tf_for_def branch_parity_def)
next
  case (EA_Ret ea p)
  then show ?thesis
  proof (cases ea)
    case None
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: parity_tf_for_def skip_parity_def return_parity_def)
  next
    case (Some av)
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: parity_tf_for_def return_parity_def assign_parity_def)
  qed
next
  case (EA_Check c)
  then show ?thesis by (simp add: parity_tf_for_def event_parity_def)
qed

lemma enter_frame_parity_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q PTop s) =
   enter_frame_parity_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_frame_parity_for_def)

lemma parity_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_enter_st_for gs ci s) =
   snd (enter\<^sup># (parity_tf_for gs) ci (fun_of_resolved_st_q_for gs s))"
  by (simp add: parity_tf_for_def enter_parity_for_def enter_D_def enter_frame_def
                enter_pair_parity_for_def enter_pair_D_def
                enter_frame_parity_for_def enter_frame_parity_st_for_commute
                fun_of_resolved_st_q_for_enter_frame)

text \<open>The Nop/Assign executable-abstract correspondence facts, mirroring
  \<open>sign_tf_st_for_nop_agree\<close>/\<open>sign_tf_st_for_assign_agree\<close> for the sign
  domain: given only scoped input agreement (and, for a write, that the
  written expression's value already agrees), the executable step agrees
  with the abstract step at every location the scope covers.\<close>

lemma parity_tf_st_for_nop_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs EA_Nop s_exec) location =
      apply_tf (parity_tf_for gs) EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def skip_parity_def)

lemma parity_tf_st_for_assign_agree:
  fixes y :: vname and a :: exp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_parity a (fun_of_resolved_st_q_for gs s_exec) = aval_parity a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Assign y a) s_exec) location =
      apply_tf (parity_tf_for gs) (EA_Assign y a) s_abs (location_vname location)"
proof (cases "location_vname location = y")
  case True
  then have "location = location_of gs y" using canonical by simp
  then show ?thesis using val_agree True by (simp add: parity_tf_for_def assign_parity_def)
next
  case False
  have neq: "location \<noteq> location_of gs y"
  proof
    assume eq: "location = location_of gs y"
    have "location_vname location = y" using eq by (simp add: location_of_def)
    with False show False by simp
  qed
  show ?thesis
    using agree[OF location_in] neq False by (simp add: parity_tf_for_def assign_parity_def)
qed

text \<open>Parity's branch transfer is the identity on both sides (\<open>branch_parity_def\<close>,
  \<open>parity_tf_st_for\<close>'s own \<open>EA_Assume\<close>/\<open>EA_AssumeNot\<close> cases), so these two
  agreement facts have the same shape as \<open>parity_tf_st_for_nop_agree\<close>.\<close>

lemma parity_tf_st_for_assume_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Assume b) s_exec) location =
      apply_tf (parity_tf_for gs) (EA_Assume b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def branch_parity_def)

lemma parity_tf_st_for_assume_not_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_AssumeNot b) s_exec) location =
      apply_tf (parity_tf_for gs) (EA_AssumeNot b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def branch_parity_def)

lemma parity_tf_st_for_ret_none_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Ret None p) s_exec) location =
      apply_tf (parity_tf_for gs) (EA_Ret None p) s_abs (location_vname location)"
  using parity_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: parity_tf_for_def skip_parity_def return_parity_def)


end

