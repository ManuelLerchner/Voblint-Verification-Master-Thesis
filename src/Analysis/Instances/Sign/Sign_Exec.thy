theory Sign_Exec
  imports Voblint_Core.Exec_Bridge Sign_Domain
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

definition branch_sign_st_for ::
  "(vname => bool) => bexp => bool => sign resolved_st_q => sign resolved_st_q" where
  "branch_sign_st_for source_global b pol s =
    bfilter_sign_st source_global b pol s"

definition sign_enter_st_for ::
  "(vname => bool) => vname list => aexp list =>
   sign resolved_st_q => sign resolved_st_q" where
  "sign_enter_st_for source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map (\<lambda>e. aval_sign e
        (fun_of_resolved_st_q_for source_global s)) es)
      (enter_frame_D_resolved_q STop s)"

fun sign_tf_st_for ::
  "(vname => bool) => edge_action =>
   sign resolved_st_q => sign resolved_st_q" where
    "sign_tf_st_for source_global EA_Nop s = s"
  | "sign_tf_st_for source_global (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (aval_sign a (fun_of_resolved_st_q_for source_global s))"
  | "sign_tf_st_for source_global (EA_Special sc x) s =
       update_resolved_st_q s (location_of source_global x) STop"
  | "sign_tf_st_for source_global (EA_Assume b) s =
       branch_sign_st_for source_global b True s"
  | "sign_tf_st_for source_global (EA_AssumeNot b) s =
       branch_sign_st_for source_global b False s"
  | "sign_tf_st_for source_global (EA_Ret None p) s = s"
  | "sign_tf_st_for source_global (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of source_global ret_var)
         (aval_sign a (fun_of_resolved_st_q_for source_global s))"
  | "sign_tf_st_for source_global (EA_Check cnd) s = s"

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
  fixes y :: vname and a :: aexp
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

lemma sign_tf_st_for_reduces: "action_reduces (sign_tf_st_for gs)"
  by unfold_locales (rule ext, simp)+

theorem sign_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (sign_tf_st_for gs a s) =
   apply_tf (sign_tf_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for gs s)"])
  show "fun_of_resolved_st_q_for gs (sign_tf_st_for gs EA_Nop s) =
      apply_tf (sign_tf_for gs) EA_Nop (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def skip_sign_def)
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs (EA_Assign x e) s) =
    apply_tf (sign_tf_for gs) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def assign_sign_def)
  show "\<And>sc x. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs (EA_Special sc x) s) =
    apply_tf (sign_tf_for gs) (EA_Special sc x) (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def special_sign_def)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs (EA_Assume b) s) =
    apply_tf (sign_tf_for gs) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def branch_sign_st_for_def apply_tf.simps bfilter_sign_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs (EA_AssumeNot b) s) =
    apply_tf (sign_tf_for gs) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def branch_sign_st_for_def apply_tf.simps bfilter_sign_st_commute)
  show "\<And>ea p. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs (EA_Ret ea p) s) =
    apply_tf (sign_tf_for gs) (EA_Ret ea p) (fun_of_resolved_st_q_for gs s)"
  proof -
    fix ea p
    show "fun_of_resolved_st_q_for gs (sign_tf_st_for gs (EA_Ret ea p) s) =
      apply_tf (sign_tf_for gs) (EA_Ret ea p) (fun_of_resolved_st_q_for gs s)"
    proof (cases ea)
      case None
      then show ?thesis by (simp add: sign_tf_for_def return_sign_def)
    next
      case (Some a)
      then show ?thesis by (simp add: sign_tf_for_def return_sign_def assign_sign_def)
    qed
  qed
  show "\<And>c. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs (EA_Check c) s) =
    apply_tf (sign_tf_for gs) (EA_Check c) (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def event_sign_def)
qed

lemma enter_frame_sign_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q STop s) =
   enter_frame_sign_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_frame_sign_for_def)

lemma sign_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (sign_enter_st_for gs xs es s) =
   enter\<^sup># (sign_tf_for gs) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: sign_enter_st_for_def sign_tf_for_def enter_sign_for_def enter_D_def
                enter_frame_sign_for_def enter_frame_sign_st_for_commute)

subsection \<open>Executable effectful transfer record, generic in the classifier\<close>

text \<open>
  \<open>is_bot_pred\<close> is the executable witness-bottom check
  \<^const>\<open>unit_edge_tree_st\<close>/\<^const>\<open>unit_combine_tree_st\<close> take -- see
  @{theory Voblint_Core.Exec_Bridge}. Callers with a concrete program supply
  \<^const>\<open>resolved_st_q_is_bot_for\<close> at that program's own declared-global list,
  which is exact for @{const is_bot_state}
  (@{thm resolved_st_q_is_bot_for_iff}); this layer stays generic in it so it
  does not itself need to know that a program exists yet.
\<close>

definition sign_etf_st_for ::
  "(sign resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool)
   \<Rightarrow> (unit, sign resolved_st_q lifted) effectful_st_transfer" where
  "sign_etf_st_for is_bot_pred gs = unit_etf_st_of_transfer is_bot_pred gs (sign_tf_st_for gs) (sign_enter_st_for gs)"

lemma sign_etf_st_for_edge_tree:
  "apply_etf_st (sign_etf_st_for is_bot_pred gs) a u = unit_edge_tree_st is_bot_pred (sign_tf_st_for gs a) u"
  unfolding sign_etf_st_for_def
  by (rule apply_etf_st_unit_of_transfer[OF sign_tf_st_for_reduces])

lemma sign_etf_st_for_combine_tree:
  "etf_combine_collect_st (sign_etf_st_for is_bot_pred gs) dst cc ex = unit_combine_tree_st is_bot_pred gs dst cc ex"
  unfolding sign_etf_st_for_def by (rule etf_combine_collect_st_unit_of_transfer)

lemma sign_etf_st_for_enter_tree:
  "etf_st_enter (sign_etf_st_for is_bot_pred gs) xs es u = unit_edge_tree_st is_bot_pred (sign_enter_st_for gs xs es) u"
  unfolding sign_etf_st_for_def by (rule etf_st_enter_unit_of_transfer)

lemma sign_etf_st_for_enter_exists_unit:
  "\<And>u xs es. \<exists>f. etf_st_enter (sign_etf_st_for is_bot_pred gs) xs es u = unit_edge_tree_st is_bot_pred f u"
  using sign_etf_st_for_enter_tree by blast

lemma sign_etf_st_for_exists_unit:
  "\<And>a u. \<exists>f. apply_etf_st (sign_etf_st_for is_bot_pred gs) a u = unit_edge_tree_st is_bot_pred f u"
  using sign_etf_st_for_edge_tree by blast

text \<open>
  Side-free counterpart of \<^const>\<open>sign_etf_st_for\<close>, built from the same
  \<^const>\<open>sign_tf_st_for\<close>/\<^const>\<open>sign_enter_st_for\<close> domain-transfer functions via the
  generic \<^const>\<open>unit_etf_st_contribution_of_transfer\<close> factory. The buffered
  generator's correspondence with the original \<^const>\<open>sign_etf_st_for\<close>-driven
  generator follows directly from the generic
  \<open>unit_etf_st_of_transfer_buffered_correspondence\<close> theorem, reusing
  \<open>sign_tf_st_for_reduces\<close> -- no Sign-specific correspondence proof.
\<close>
definition sign_etf_st_contribution_for ::
  "(sign resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool)
   \<Rightarrow> (unit, sign resolved_st_q lifted) effectful_st_transfer" where
  "sign_etf_st_contribution_for is_bot_pred gs
     = unit_etf_st_contribution_of_transfer is_bot_pred gs (sign_tf_st_for gs) (sign_enter_st_for gs)"

lemma sign_buffered_correspondence:
  shows "traverse_rhs (make_side_rhs_tree_eff_st_buffered g
      (sign_etf_st_contribution_for is_bot_pred gs) bot s0_st () v) \<sigma>
    = traverse_rhs (make_side_rhs_tree_eff_st g (sign_etf_st_for is_bot_pred gs) bot s0_st () v) \<sigma>"
    (is ?T)
    and "sides_of_rhs (make_side_rhs_tree_eff_st_buffered g
      (sign_etf_st_contribution_for is_bot_pred gs) bot s0_st () v) \<sigma> (Inr ())
    = sides_of_rhs (make_side_rhs_tree_eff_st g (sign_etf_st_for is_bot_pred gs) bot s0_st () v) \<sigma> (Inr ())"
    (is ?S)
  unfolding sign_etf_st_contribution_for_def sign_etf_st_for_def
  by (rule unit_etf_st_of_transfer_buffered_correspondence[OF sign_tf_st_for_reduces])+

lemma sign_buffered_dep_aux:
  "dep_aux \<sigma> (make_side_rhs_tree_eff_st_buffered g (sign_etf_st_contribution_for is_bot_pred gs) bot s0_st () v)
     = dep_aux \<sigma> (make_side_rhs_tree_eff_st g (sign_etf_st_for is_bot_pred gs) bot s0_st () v)"
  unfolding sign_etf_st_contribution_for_def sign_etf_st_for_def
  by (rule unit_etf_st_of_transfer_buffered_dep_aux[OF sign_tf_st_for_reduces])

lemma sides_of_rhs_sign_st_Inl_bot:
  "sides_of_rhs (t :: (pp, unit, 'a::bounded_semilattice_sup_bot) strategy_tree) \<sigma> (Inl a) = bot"
  by (induction t) (auto simp: Let_def)

text \<open>
  Full-function \<^const>\<open>sides_of_rhs\<close> form of \<open>sign_buffered_correspondence\<close>,
  needed to transport \<open>part_post_solution\<close>-style facts (which compare
  \<^const>\<open>sides_of_rhs\<close> as a whole function, not only at the single unit global
  key): \<open>sides_of_rhs_sign_st_Inl_bot\<close> closes the \<open>Inl\<close> branch generically
  for either generator, and \<open>sign_buffered_correspondence\<close> closes \<open>Inr ()\<close>.
\<close>
lemma sign_buffered_sides_full:
  "sides_of_rhs (make_side_rhs_tree_eff_st_buffered g
      (sign_etf_st_contribution_for is_bot_pred gs) bot s0_st () v) \<sigma>
    = sides_of_rhs (make_side_rhs_tree_eff_st g (sign_etf_st_for is_bot_pred gs) bot s0_st () v) \<sigma>"
proof (rule ext)
  fix y
  show "sides_of_rhs (make_side_rhs_tree_eff_st_buffered g
          (sign_etf_st_contribution_for is_bot_pred gs) bot s0_st () v) \<sigma> y
       = sides_of_rhs (make_side_rhs_tree_eff_st g (sign_etf_st_for is_bot_pred gs) bot s0_st () v) \<sigma> y"
  proof (cases y)
    case (Inl a) then show ?thesis by (simp add: sides_of_rhs_sign_st_Inl_bot)
  next
    case (Inr b) then show ?thesis using sign_buffered_correspondence by simp
  qed
qed

end

