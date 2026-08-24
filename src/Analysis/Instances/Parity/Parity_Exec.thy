theory Parity_Exec
  imports Voblint_Core.Exec_Refinement Voblint_Core.Numeric_Ops Parity_Transfer
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
  \<open>generic_enter_st_for\<close> construction (\<^theory>\<open>Voblint_Core.Numeric_Ops\<close>), the
  same way \<open>sign_ops\<close>/\<open>ivl_ops\<close> do for Sign/Interval. Parity's branch
  transfer is the identity, so unlike Sign/Interval there is no
  \<open>branch_parity_st_for\<close> to generalize -- only \<open>n_bfilter\<close>'s VALUE would be
  the identity function, and nothing here needs to name that value
  separately since \<open>generic_branch_st_for\<close> is never applied to Parity.
\<close>

definition parity_ops :: "parity numeric_ops" where
  "parity_ops = \<lparr> n_aval = aval_parity_t, n_cast = parity_cast, n_bfilter = (\<lambda>_ _ _ _ s. s),
                  n_top = PTop \<rparr>"

definition parity_enter_st_for ::
  "tyenv => (vname => bool) => vname list => exp list =>
   parity resolved_st_q => parity resolved_st_q" where
  "parity_enter_st_for = generic_enter_st_for parity_ops"

lemma parity_enter_st_for_eq [simp]:
  "parity_enter_st_for \<Gamma> source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map2 (\<lambda>x e. parity_cast (\<Gamma> x)
               (aval_parity_t (elaborate_syn \<Gamma> e) (fun_of_resolved_st_q_for source_global s)))
        xs es)
      (enter_frame_D_resolved_q PTop s)"
  by (simp add: parity_enter_st_for_def generic_enter_st_for_def parity_ops_def)

fun parity_tf_st_for ::
  "(vname => bool) => tyenv => edge_action =>
   parity resolved_st_q => parity resolved_st_q" where
    "parity_tf_st_for source_global \<Gamma> EA_Nop s = s"
  | "parity_tf_st_for source_global \<Gamma> (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (parity_cast (\<Gamma> x)
           (aval_parity_t (elaborate_syn \<Gamma> a) (fun_of_resolved_st_q_for source_global s)))"
  | "parity_tf_st_for source_global \<Gamma> (EA_Special sc x) s =
       update_resolved_st_q s (location_of source_global x)
         (case sc of
            Nondet_Int => PTop
          | Min a b => parity_cast (\<Gamma> x)
              (parity_min (aval_parity_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a)
                             (fun_of_resolved_st_q_for source_global s))
                          (aval_parity_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b)
                             (fun_of_resolved_st_q_for source_global s)))
          | Max a b => parity_cast (\<Gamma> x)
              (parity_max (aval_parity_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a)
                             (fun_of_resolved_st_q_for source_global s))
                          (aval_parity_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b)
                             (fun_of_resolved_st_q_for source_global s))))"
  | "parity_tf_st_for source_global \<Gamma> (EA_Assume b) s = s"
  | "parity_tf_st_for source_global \<Gamma> (EA_AssumeNot b) s = s"
  | "parity_tf_st_for source_global \<Gamma> (EA_Ret None p rk) s = s"
  | "parity_tf_st_for source_global \<Gamma> (EA_Ret (Some a) p rk) s =
       update_resolved_st_q s (location_of source_global ret_var) PTop"
  | "parity_tf_st_for source_global \<Gamma> (EA_Check cnd) s = s"

text \<open>
  Unlike its siblings, \<open>parity_tf_st_for\<close> does not satisfy \<open>action_reduces\<close>:
  @{const return_parity}'s value-return case sets the result to \<open>PTop\<close>
  unconditionally rather than reusing @{const assign_parity}, since \<open>rk\<close> is
  not threaded to \<open>tf_return\<close> and \<open>PTop\<close> is the only choice sound for every
  possible \<open>rk\<close> simultaneously (the same reasoning as Sign's own
  \<open>sign_tf_st_for\<close>). No caller in this codebase currently depends on
  \<open>action_reduces\<close> for Parity.
\<close>

theorem parity_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_tf_st_for gs \<Gamma> a s) =
   apply_tf (parity_tf_for gs \<Gamma>) a (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for gs s)"])
  show "fun_of_resolved_st_q_for gs (parity_tf_st_for gs \<Gamma> EA_Nop s) =
      apply_tf (parity_tf_for gs \<Gamma>) EA_Nop (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def skip_parity_def)
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs \<Gamma> (EA_Assign x e) s) =
    apply_tf (parity_tf_for gs \<Gamma>) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def assign_parity_def)
  show "\<And>sc x. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs \<Gamma> (EA_Special sc x) s) =
    apply_tf (parity_tf_for gs \<Gamma>) (EA_Special sc x) (fun_of_resolved_st_q_for gs s)"
    by (auto simp: parity_tf_for_def special_parity_def top_parity_def
             split: special_call.splits)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs \<Gamma> (EA_Assume b) s) =
    apply_tf (parity_tf_for gs \<Gamma>) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def branch_parity_def)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs \<Gamma> (EA_AssumeNot b) s) =
    apply_tf (parity_tf_for gs \<Gamma>) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def branch_parity_def)
  show "\<And>ea p rk. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs \<Gamma> (EA_Ret ea p rk) s) =
    apply_tf (parity_tf_for gs \<Gamma>) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
  proof -
    fix ea p rk
    show "fun_of_resolved_st_q_for gs (parity_tf_st_for gs \<Gamma> (EA_Ret ea p rk) s) =
      apply_tf (parity_tf_for gs \<Gamma>) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
    proof (cases ea)
      case None
      then show ?thesis by (simp add: parity_tf_for_def skip_parity_def return_parity_def)
    next
      case (Some a)
      then show ?thesis by (simp add: parity_tf_for_def return_parity_def)
    qed
  qed
  show "\<And>c. fun_of_resolved_st_q_for gs
      (parity_tf_st_for gs \<Gamma> (EA_Check c) s) =
    apply_tf (parity_tf_for gs \<Gamma>) (EA_Check c) (fun_of_resolved_st_q_for gs s)"
    by (simp add: parity_tf_for_def event_parity_def)
qed

lemma enter_frame_parity_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q PTop s) =
   enter_frame_parity_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_frame_parity_for_def)

lemma parity_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_enter_st_for \<Gamma> gs xs es s) =
   enter\<^sup># (parity_tf_for gs \<Gamma>) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: parity_tf_for_def enter_parity_for_def enter_D_typed_def
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
    "lookup_resolved_st_q (parity_tf_st_for gs \<Gamma> EA_Nop s_exec) location =
      apply_tf (parity_tf_for gs \<Gamma>) EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def skip_parity_def)

lemma parity_tf_st_for_assign_agree:
  fixes y :: vname and a :: exp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_parity_t (elaborate_syn \<Gamma> a) (fun_of_resolved_st_q_for gs s_exec) =
                    aval_parity_t (elaborate_syn \<Gamma> a) s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs \<Gamma> (EA_Assign y a) s_exec) location =
      apply_tf (parity_tf_for gs \<Gamma>) (EA_Assign y a) s_abs (location_vname location)"
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
    "lookup_resolved_st_q (parity_tf_st_for gs \<Gamma> (EA_Assume b) s_exec) location =
      apply_tf (parity_tf_for gs \<Gamma>) (EA_Assume b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def branch_parity_def)

lemma parity_tf_st_for_assume_not_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs \<Gamma> (EA_AssumeNot b) s_exec) location =
      apply_tf (parity_tf_for gs \<Gamma>) (EA_AssumeNot b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf_for_def branch_parity_def)

lemma parity_tf_st_for_ret_none_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs \<Gamma> (EA_Ret None p rk) s_exec) location =
      apply_tf (parity_tf_for gs \<Gamma>) (EA_Ret None p rk) s_abs (location_vname location)"
  using parity_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: parity_tf_for_def skip_parity_def return_parity_def)


end

