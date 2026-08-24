theory Sign_Exec
  imports Voblint_Core.Exec_Refinement Voblint_Core.Numeric_Ops Sign_Domain
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
  (\<^theory>\<open>Voblint_Core.Numeric_Ops\<close>): \<open>branch_sign_st_for\<close>/\<open>sign_enter_st_for\<close>
  below are exactly those generic constructions instantiated at \<open>sign_ops\<close>,
  not independent definitions -- Interval and Parity instantiate the same
  generic pair at their own primitives.
\<close>

definition sign_ops :: "sign numeric_ops" where
  "sign_ops = \<lparr> n_aval = aval_sign_t, n_cast = sign_cast, n_bfilter = branch_sign_st, n_top = STop \<rparr>"

definition branch_sign_st_for ::
  "tyenv => (vname => bool) => exp => bool => sign resolved_st_q => sign resolved_st_q" where
  "branch_sign_st_for = generic_branch_st_for sign_ops"

lemma branch_sign_st_for_eq [simp]:
  "branch_sign_st_for \<Gamma> source_global b pol s = branch_sign_st \<Gamma> source_global b pol s"
  by (simp add: branch_sign_st_for_def generic_branch_st_for_def sign_ops_def)

definition sign_enter_st_for ::
  "tyenv => (vname => bool) => vname list => exp list =>
   sign resolved_st_q => sign resolved_st_q" where
  "sign_enter_st_for = generic_enter_st_for sign_ops"

lemma sign_enter_st_for_eq [simp]:
  "sign_enter_st_for \<Gamma> source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map2 (\<lambda>x e. sign_cast (\<Gamma> x)
               (aval_sign_t (elaborate_syn \<Gamma> e) (fun_of_resolved_st_q_for source_global s)))
        xs es)
      (enter_frame_D_resolved_q STop s)"
  by (simp add: sign_enter_st_for_def generic_enter_st_for_def sign_ops_def)

fun sign_tf_st_for ::
  "(vname => bool) => tyenv => edge_action =>
   sign resolved_st_q => sign resolved_st_q" where
    "sign_tf_st_for source_global \<Gamma> EA_Nop s = s"
  | "sign_tf_st_for source_global \<Gamma> (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (sign_cast (\<Gamma> x) (aval_sign_t (elaborate_syn \<Gamma> a) (fun_of_resolved_st_q_for source_global s)))"
  | "sign_tf_st_for source_global \<Gamma> (EA_Special sc x) s =
       update_resolved_st_q s (location_of source_global x)
         (case sc of
            Nondet_Int => STop
          | Min a b => sign_cast (\<Gamma> x)
              (sign_min (aval_sign_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a)
                           (fun_of_resolved_st_q_for source_global s))
                        (aval_sign_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b)
                           (fun_of_resolved_st_q_for source_global s)))
          | Max a b => sign_cast (\<Gamma> x)
              (sign_max (aval_sign_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a)
                           (fun_of_resolved_st_q_for source_global s))
                        (aval_sign_t (elaborate \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b)
                           (fun_of_resolved_st_q_for source_global s))))"
  | "sign_tf_st_for source_global \<Gamma> (EA_Assume b) s =
       branch_sign_st_for \<Gamma> source_global b True s"
  | "sign_tf_st_for source_global \<Gamma> (EA_AssumeNot b) s =
       branch_sign_st_for \<Gamma> source_global b False s"
  | "sign_tf_st_for source_global \<Gamma> (EA_Ret None p rk) s = s"
  | "sign_tf_st_for source_global \<Gamma> (EA_Ret (Some a) p rk) s =
       update_resolved_st_q s (location_of source_global ret_var) STop"
  | "sign_tf_st_for source_global \<Gamma> (EA_Check cnd) s = s"

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
    "lookup_resolved_st_q (sign_tf_st_for gs \<Gamma> EA_Nop s_exec) location =
      apply_tf (sign_tf_for gs \<Gamma>) EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: sign_tf_for_def skip_sign_def)

lemma sign_tf_st_for_assign_agree:
  fixes y :: vname and a :: exp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_sign_t (elaborate_syn \<Gamma> a) (fun_of_resolved_st_q_for gs s_exec) =
                    aval_sign_t (elaborate_syn \<Gamma> a) s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs \<Gamma> (EA_Assign y a) s_exec) location =
      apply_tf (sign_tf_for gs \<Gamma>) (EA_Assign y a) s_abs (location_vname location)"
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
    "lookup_resolved_st_q (sign_tf_st_for gs \<Gamma> (EA_Ret None p rk) s_exec) location =
      apply_tf (sign_tf_for gs \<Gamma>) (EA_Ret None p rk) s_abs (location_vname location)"
  using sign_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: sign_tf_for_def skip_sign_def return_sign_def)

subsection \<open>Classifier-parametric commutation\<close>

text \<open>The classifier-parametric commutation of the executable and abstract sign
  transfer, mirroring \<open>parity_tf_st_for_commute\<close>/\<open>parity_enter_st_for_commute\<close>
  for the parity domain: the registered D/G pipeline for a program with a real
  declared global needs the executable transfer to commute with the abstract
  transfer at an arbitrary classifier \<open>gs\<close>.\<close>

text \<open>
  Unlike its siblings, \<open>sign_tf_st_for\<close> does not satisfy \<open>action_reduces\<close>:
  @{const return_sign}'s value-return case sets the result to \<open>STop\<close>
  unconditionally rather than reusing @{const assign_sign}, since \<open>rk\<close> is not
  threaded to \<open>tf_return\<close> and \<open>STop\<close> is the only choice sound for every
  possible \<open>rk\<close> simultaneously. No caller in this codebase currently depends
  on \<open>action_reduces\<close> for Sign.
\<close>

theorem sign_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (sign_tf_st_for gs \<Gamma> ea s) =
   apply_tf (sign_tf_for gs \<Gamma>) ea (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for gs s)"])
  show "fun_of_resolved_st_q_for gs (sign_tf_st_for gs \<Gamma> EA_Nop s) =
      apply_tf (sign_tf_for gs \<Gamma>) EA_Nop (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def skip_sign_def)
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs \<Gamma> (EA_Assign x e) s) =
    apply_tf (sign_tf_for gs \<Gamma>) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def assign_sign_def)
  show "\<And>sc x. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs \<Gamma> (EA_Special sc x) s) =
    apply_tf (sign_tf_for gs \<Gamma>) (EA_Special sc x) (fun_of_resolved_st_q_for gs s)"
    by (auto simp: sign_tf_for_def special_sign_def top_sign_def split: special_call.splits)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs \<Gamma> (EA_Assume b) s) =
    apply_tf (sign_tf_for gs \<Gamma>) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def sign_backward_domain.branch_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs \<Gamma> (EA_AssumeNot b) s) =
    apply_tf (sign_tf_for gs \<Gamma>) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def sign_backward_domain.branch_st_commute)
  show "\<And>ea p rk. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs \<Gamma> (EA_Ret ea p rk) s) =
    apply_tf (sign_tf_for gs \<Gamma>) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
  proof -
    fix ea p rk
    show "fun_of_resolved_st_q_for gs (sign_tf_st_for gs \<Gamma> (EA_Ret ea p rk) s) =
      apply_tf (sign_tf_for gs \<Gamma>) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
    proof (cases ea)
      case None
      then show ?thesis by (simp add: sign_tf_for_def return_sign_def)
    next
      case (Some a)
      then show ?thesis by (simp add: sign_tf_for_def return_sign_def)
    qed
  qed
  show "\<And>c. fun_of_resolved_st_q_for gs
      (sign_tf_st_for gs \<Gamma> (EA_Check c) s) =
    apply_tf (sign_tf_for gs \<Gamma>) (EA_Check c) (fun_of_resolved_st_q_for gs s)"
    by (simp add: sign_tf_for_def event_sign_def)
qed

lemma enter_frame_sign_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q STop s) =
   enter_frame_sign_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_frame_sign_for_def)

lemma sign_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (sign_enter_st_for \<Gamma> gs xs es s) =
   enter\<^sup># (sign_tf_for gs \<Gamma>) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: sign_tf_for_def enter_sign_for_def enter_D_typed_def
                enter_frame_sign_for_def enter_frame_sign_st_for_commute)

end

