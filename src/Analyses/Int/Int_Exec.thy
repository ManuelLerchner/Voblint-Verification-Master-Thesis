theory Int_Exec
  imports "Voblint_Exec.Exec_St_Restriction_Refinement" "Voblint_Nonrelational.Numeric_Ops"
    Int_Transfer
begin

section \<open>Composite integer domain: executable transfer mirror\<close>

text \<open>
  Executable finite-map mirror of the abstract composite transfer bundles
  registered in \<^theory>\<open>Voblint_Analysis_Int.Int_Transfer\<close>, mirroring Sign's own
  \<open>Sign_Exec\<close>'s shape. Every field's soundness proof
  reduces to unfolding both sides' definitions and, for the branch case,
  citing the backward-filter locale's own generic \<open>bfilter_st_commute\<close> --
  already available from \<^theory>\<open>Voblint_Analysis_Int.Int_Backward\<close>'s three
  interpretations with no new proof, since \<open>backward_domain\<close> provides an
  executable \<open>bfilter_st\<close> mirror and its commutation generically for any
  instance. \<open>Refine_Never\<close>, \<open>Refine_Once\<close>, and \<open>Refine_Fixpoint\<close> each get
  their own named adapter (\<open>int_tf_st_never_for\<close> etc.), matching
  \<open>Int_Transfer\<close>'s three registered bundles rather than hiding the mode
  inside one function.
\<close>

subsection \<open>Top and C-initial executable states\<close>

lift_definition top_int_dom_st :: "int_dom resolved_st_q" is "(top, top, [])" .

lemma lookup_top_int_dom_st [simp]:
  "fun_of_resolved_st_q_for gs top_int_dom_st x = top"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_int_dom_st:
  "fun_of_resolved_st_q_for gs top_int_dom_st = (\<lambda>_. top)"
  by (rule ext) simp

lift_definition cinit_int_dom_st :: "int_dom resolved_st_q" is "(top, int_dom_of_int 0, [])" .

lemma lookup_cinit_int_dom_st_for [simp]:
  "fun_of_resolved_st_q_for gs cinit_int_dom_st x =
   (if gs x then int_dom_of_int 0 else top)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_int_dom_st_for:
  "fun_of_resolved_st_q_for gs cinit_int_dom_st =
   (\<lambda>x. if gs x then int_dom_of_int 0 else top)"
  by (rule ext) simp

subsection \<open>The primitive bundle, per refinement mode\<close>

text \<open>
  \<open>Refine_Never\<close>, \<open>Refine_Once\<close> and \<open>Refine_Fixpoint\<close> differ only in the mode
  their operations carry, so each gets its own \<^type>\<open>numeric_ops\<close> bundle and the
  three executable constants per mode are
  \<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close>'s generic constructions instantiated
  at it --- the same constructions Sign, Interval, Parity and Congruence use.
  Only the bundles and the per-mode corollaries are written three times; the
  transfer itself is written once, elsewhere.

  Int's abstract operations stay its own (\<^theory>\<open>Voblint_Analysis_Int.Int_Transfer\<close>)
  rather than a \<open>nonrelational_transfer\<close> interpretation, because they carry
  the mode. Each \<open>_eq_generic\<close> lemma below records that they are nonetheless
  exactly what the bundle determines, which is what lets the generic commutation
  apply to them unchanged.
\<close>

definition int_dom_special_ops :: "refine_mode => int_dom special_ops" where
  "int_dom_special_ops mode =
     \<lparr> special_min = int_dom_min mode, special_max = int_dom_max mode \<rparr>"

lemma int_dom_special_ops_simps [simp]:
  "special_min (int_dom_special_ops mode) = int_dom_min mode"
  "special_max (int_dom_special_ops mode) = int_dom_max mode"
  by (simp_all add: int_dom_special_ops_def)

subsection \<open>No cross-component refinement\<close>

definition int_dom_ops_never :: "int_dom numeric_ops" where
  "int_dom_ops_never = \<lparr> n_aval = aval_int_dom Refine_Never,
                         n_special = int_dom_special_ops Refine_Never,
                         n_bfilter = branch_int_dom_never_st,
                         n_top = top \<rparr>"

lemma int_dom_ops_never_simps [simp]:
  "n_aval int_dom_ops_never = aval_int_dom Refine_Never"
  "n_special int_dom_ops_never = int_dom_special_ops Refine_Never"
  "n_bfilter int_dom_ops_never = branch_int_dom_never_st"
  "n_top int_dom_ops_never = top"
  by (simp_all add: int_dom_ops_never_def)


definition int_dom_enter_never_st_for ::
    "(vname => bool) => call_info =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_never_st_for = generic_enter_st_for int_dom_ops_never"

lemma int_dom_enter_never_st_for_eq [simp]:
  "int_dom_enter_never_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_int_dom Refine_Never e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_never_st_for_def generic_enter_st_for_def)

definition int_tf_st_never_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
  "int_tf_st_never_for = generic_tf_st_for int_dom_ops_never"

lemmas int_tf_st_never_for_simps [simp] =
  generic_tf_st_for.simps [of int_dom_ops_never, folded int_tf_st_never_for_def]

lemma int_tf_abs_never_eq_generic:
  "int_tf_abs Refine_Never = generic_tf_abs int_dom_ops_never branch_int_dom_never"
proof (rule ext, rule ext)
  fix a :: edge_action and sigma :: "int_dom abs_state"
  show "int_tf_abs Refine_Never a sigma =
        generic_tf_abs int_dom_ops_never branch_int_dom_never a sigma"
    by (cases a)
       (simp_all add: skip_int_dom_def assign_int_dom_def body_int_dom_def
          event_int_dom_def return_int_dom_def
          split: special_call.splits option.splits)
qed

theorem int_tf_st_never_for_commute:
  assumes live: "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (int_tf_st_never_for gs a s) =
     int_tf_abs Refine_Never a (fun_of_resolved_st_q_for gs s)"
  unfolding int_tf_st_never_for_def int_tf_abs_never_eq_generic
  by (rule generic_tf_st_for_commute)
     (simp add: int_dom_backward_never.branch_st_commute[OF live])

lemma int_dom_enter_never_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_never_st_for gs ci s) =
   enter_int_dom_ci_for Refine_Never gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_int_dom_ci_for_def enter_int_dom_for_def enter_binding_def
                enter_frame_def enter_frame_int_dom_for_def)


subsection \<open>One refinement round\<close>

definition int_dom_ops_once :: "int_dom numeric_ops" where
  "int_dom_ops_once = \<lparr> n_aval = aval_int_dom Refine_Once,
                        n_special = int_dom_special_ops Refine_Once,
                        n_bfilter = branch_int_dom_once_st,
                        n_top = top \<rparr>"

lemma int_dom_ops_once_simps [simp]:
  "n_aval int_dom_ops_once = aval_int_dom Refine_Once"
  "n_special int_dom_ops_once = int_dom_special_ops Refine_Once"
  "n_bfilter int_dom_ops_once = branch_int_dom_once_st"
  "n_top int_dom_ops_once = top"
  by (simp_all add: int_dom_ops_once_def)


definition int_dom_enter_once_st_for ::
    "(vname => bool) => call_info =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_once_st_for = generic_enter_st_for int_dom_ops_once"

lemma int_dom_enter_once_st_for_eq [simp]:
  "int_dom_enter_once_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_int_dom Refine_Once e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_once_st_for_def generic_enter_st_for_def)

definition int_tf_st_once_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
  "int_tf_st_once_for = generic_tf_st_for int_dom_ops_once"

lemmas int_tf_st_once_for_simps [simp] =
  generic_tf_st_for.simps [of int_dom_ops_once, folded int_tf_st_once_for_def]

lemma int_tf_abs_once_eq_generic:
  "int_tf_abs Refine_Once = generic_tf_abs int_dom_ops_once branch_int_dom_once"
proof (rule ext, rule ext)
  fix a :: edge_action and sigma :: "int_dom abs_state"
  show "int_tf_abs Refine_Once a sigma =
        generic_tf_abs int_dom_ops_once branch_int_dom_once a sigma"
    by (cases a)
       (simp_all add: skip_int_dom_def assign_int_dom_def body_int_dom_def
          event_int_dom_def return_int_dom_def
          split: special_call.splits option.splits)
qed

theorem int_tf_st_once_for_commute:
  assumes live: "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (int_tf_st_once_for gs a s) =
     int_tf_abs Refine_Once a (fun_of_resolved_st_q_for gs s)"
  unfolding int_tf_st_once_for_def int_tf_abs_once_eq_generic
  by (rule generic_tf_st_for_commute)
     (simp add: int_dom_backward_once.branch_st_commute[OF live])

lemma int_dom_enter_once_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_once_st_for gs ci s) =
   enter_int_dom_ci_for Refine_Once gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_int_dom_ci_for_def enter_int_dom_for_def enter_binding_def
                enter_frame_def enter_frame_int_dom_for_def)


subsection \<open>Refinement to a fixpoint\<close>

definition int_dom_ops_fixpoint :: "int_dom numeric_ops" where
  "int_dom_ops_fixpoint = \<lparr> n_aval = aval_int_dom Refine_Fixpoint,
                            n_special = int_dom_special_ops Refine_Fixpoint,
                            n_bfilter = branch_int_dom_fixpoint_st,
                            n_top = top \<rparr>"

lemma int_dom_ops_fixpoint_simps [simp]:
  "n_aval int_dom_ops_fixpoint = aval_int_dom Refine_Fixpoint"
  "n_special int_dom_ops_fixpoint = int_dom_special_ops Refine_Fixpoint"
  "n_bfilter int_dom_ops_fixpoint = branch_int_dom_fixpoint_st"
  "n_top int_dom_ops_fixpoint = top"
  by (simp_all add: int_dom_ops_fixpoint_def)


definition int_dom_enter_fixpoint_st_for ::
    "(vname => bool) => call_info =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_fixpoint_st_for = generic_enter_st_for int_dom_ops_fixpoint"

lemma int_dom_enter_fixpoint_st_for_eq [simp]:
  "int_dom_enter_fixpoint_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_int_dom Refine_Fixpoint e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_fixpoint_st_for_def generic_enter_st_for_def)

definition int_tf_st_fixpoint_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
  "int_tf_st_fixpoint_for = generic_tf_st_for int_dom_ops_fixpoint"

lemmas int_tf_st_fixpoint_for_simps [simp] =
  generic_tf_st_for.simps [of int_dom_ops_fixpoint, folded int_tf_st_fixpoint_for_def]

lemma int_tf_abs_fixpoint_eq_generic:
  "int_tf_abs Refine_Fixpoint =
     generic_tf_abs int_dom_ops_fixpoint branch_int_dom_fixpoint"
proof (rule ext, rule ext)
  fix a :: edge_action and sigma :: "int_dom abs_state"
  show "int_tf_abs Refine_Fixpoint a sigma =
        generic_tf_abs int_dom_ops_fixpoint branch_int_dom_fixpoint a sigma"
    by (cases a)
       (simp_all add: skip_int_dom_def assign_int_dom_def body_int_dom_def
          event_int_dom_def return_int_dom_def
          split: special_call.splits option.splits)
qed

theorem int_tf_st_fixpoint_for_commute:
  assumes live: "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (int_tf_st_fixpoint_for gs a s) =
     int_tf_abs Refine_Fixpoint a (fun_of_resolved_st_q_for gs s)"
  unfolding int_tf_st_fixpoint_for_def int_tf_abs_fixpoint_eq_generic
  by (rule generic_tf_st_for_commute)
     (simp add: int_dom_backward_fixpoint.branch_st_commute[OF live])

lemma int_dom_enter_fixpoint_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_fixpoint_st_for gs ci s) =
   enter_int_dom_ci_for Refine_Fixpoint gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_int_dom_ci_for_def enter_int_dom_for_def enter_binding_def
                enter_frame_def enter_frame_int_dom_for_def)

end
