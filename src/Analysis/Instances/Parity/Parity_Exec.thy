theory Parity_Exec
  imports Voblint_Core.Exec_Bridge Parity_Transfer
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
  \<open>sign_enter_st_for\<close> for the sign domain. Parity's assume/assume-not
  transfer is the identity (\<open>assume_parity_def\<close>), so unlike the sign mirror
  there is no separate \<open>bfilter\<close>-based executable step to parametrize.\<close>

definition parity_enter_st_for ::
  "(vname => bool) => vname list => aexp list =>
   parity resolved_st_q => parity resolved_st_q" where
  "parity_enter_st_for source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map (\<lambda>e. aval_parity e
        (fun_of_resolved_st_q_for source_global s)) es)
      (enter_frame_D_resolved_q PTop s)"

fun parity_tf_st_for ::
  "(vname => bool) => edge_action =>
   parity resolved_st_q => parity resolved_st_q" where
    "parity_tf_st_for source_global EA_Nop s = s"
  | "parity_tf_st_for source_global (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (aval_parity a (fun_of_resolved_st_q_for source_global s))"
  | "parity_tf_st_for source_global (EA_Random x) s =
       update_resolved_st_q s (location_of source_global x) PTop"
  | "parity_tf_st_for source_global (EA_Assume b) s = s"
  | "parity_tf_st_for source_global (EA_AssumeNot b) s = s"
  | "parity_tf_st_for source_global (EA_Ret None p) s = s"
  | "parity_tf_st_for source_global (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of source_global ret_var)
         (aval_parity a (fun_of_resolved_st_q_for source_global s))"
  | "parity_tf_st_for source_global (EA_Check cnd) s = s"

lemma parity_tf_st_for_reduces: "action_reduces (parity_tf_st_for gs)"
  by unfold_locales (rule ext, simp)+

theorem parity_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_tf_st_for gs a s) =
   apply_tf (parity_tf_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for gs s)"])
  show "action_reduces (\<lambda>a. fun_of_resolved_st_q_for gs (parity_tf_st_for gs a s))"
    by (rule action_reduces_comp[OF parity_tf_st_for_reduces])
  show "fun_of_resolved_st_q_for gs (parity_tf_st_for gs EA_Nop s) =
      apply_tf (parity_tf_for gs) EA_Nop (fun_of_resolved_st_q_for gs s)" by simp
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs (EA_Assign x e) s) =
    apply_tf (parity_tf_for gs) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def assign_parity_def)
  show "\<And>x. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs (EA_Random x) s) =
    apply_tf (parity_tf_for gs) (EA_Random x) (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def random_parity_def)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs (EA_Assume b) s) =
    apply_tf (parity_tf_for gs) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def assume_parity_def)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs (EA_AssumeNot b) s) =
    apply_tf (parity_tf_for gs) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def assume_not_parity_def)
qed

lemma enter_frame_parity_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q PTop s) =
   enter_frame_parity_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_frame_parity_for_def)

lemma parity_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_enter_st_for gs xs es s) =
   tf_enter (parity_tf_for gs) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: parity_enter_st_for_def parity_tf_for_def enter_parity_for_def enter_D_def
                enter_frame_parity_for_def enter_frame_parity_st_for_commute)

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
  using agree[OF location_in] by simp

lemma parity_tf_st_for_assign_agree:
  fixes y :: vname and a :: aexp
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

text \<open>Parity's assume/assume-not transfer is the identity on both sides
  (\<open>assume_parity_def\<close>/\<open>assume_not_parity_def\<close>, \<open>parity_tf_st_for\<close>'s own
  \<open>EA_Assume\<close>/\<open>EA_AssumeNot\<close> cases), so these two agreement facts have the
  same shape as \<open>parity_tf_st_for_nop_agree\<close>.\<close>

lemma parity_tf_st_for_assume_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Assume b) s_exec) location =
      apply_tf (parity_tf_for gs) (EA_Assume b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def assume_parity_def)

lemma parity_tf_st_for_assume_not_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_AssumeNot b) s_exec) location =
      apply_tf (parity_tf_for gs) (EA_AssumeNot b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def assume_not_parity_def)

lemma parity_tf_st_for_ret_none_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Ret None p) s_exec) location =
      apply_tf (parity_tf_for gs) (EA_Ret None p) s_abs (location_vname location)"
  using parity_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: apply_tf_EA_Ret_None)

subsection \<open>Executable effectful transfer record, generic in the classifier\<close>

text \<open>Mirrors \<open>ivl_etf_st_for\<close> \<open>Voblint_Analysis.Ivl_Exec\<close>: the executable
  effectful transfer record consumed by \<open>side_cfg_T_eff_st\<close>, built once from
  \<open>parity_tf_st_for\<close>/\<open>parity_enter_st_for\<close> above through the generic
  \<^theory>\<open>Voblint_Core.Exec_Bridge\<close> wrapper.\<close>

definition parity_etf_st_for ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (unit, parity resolved_st_q) effectful_st_transfer" where
  "parity_etf_st_for gs = unit_etf_st_of_transfer gs (parity_tf_st_for gs) (parity_enter_st_for gs)"

lemma parity_etf_st_for_edge_tree:
  "apply_etf_st (parity_etf_st_for gs) a u = unit_edge_tree_st (parity_tf_st_for gs a) u"
  unfolding parity_etf_st_for_def
  by (rule apply_etf_st_unit_of_transfer[OF parity_tf_st_for_reduces])

lemma parity_etf_st_for_combine_tree:
  "etf_combine_st (parity_etf_st_for gs) dst cc ex = unit_combine_tree_st gs dst cc ex"
  unfolding parity_etf_st_for_def by (rule etf_combine_st_unit_of_transfer)

lemma parity_etf_st_for_enter_tree:
  "etf_st_enter (parity_etf_st_for gs) xs es u = unit_edge_tree_st (parity_enter_st_for gs xs es) u"
  unfolding parity_etf_st_for_def by (rule etf_st_enter_unit_of_transfer)

lemma parity_etf_st_for_enter_exists_unit:
  "\<And>u xs es. \<exists>f. etf_st_enter (parity_etf_st_for gs) xs es u = unit_edge_tree_st f u"
  using parity_etf_st_for_enter_tree by blast

lemma parity_etf_st_for_exists_unit:
  "\<And>a u. \<exists>f. apply_etf_st (parity_etf_st_for gs) a u = unit_edge_tree_st f u"
  using parity_etf_st_for_edge_tree by blast

end

