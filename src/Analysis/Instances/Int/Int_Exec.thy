theory Int_Exec
  imports "Voblint_Exec.Exec_Refinement" Numeric_Ops
    Int_Transfer
begin

section \<open>Composite integer domain: executable transfer mirror\<close>

text \<open>
  Executable finite-map mirror of the abstract composite transfer bundles
  registered in \<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>, mirroring Sign's own
  \<open>Sign_Exec\<close>'s shape. Every field's soundness proof
  reduces to unfolding both sides' definitions and, for the branch case,
  citing the backward-filter locale's own generic \<open>bfilter_st_commute\<close> --
  already available from \<^theory>\<open>Voblint_Analysis.Int_Backward\<close>'s three
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
  "fun_of_resolved_st_q_for is_global top_int_dom_st x = top"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_int_dom_st:
  "fun_of_resolved_st_q_for is_global top_int_dom_st = (%_. top)"
  by (rule ext) simp

lift_definition cinit_int_dom_st :: "int_dom resolved_st_q" is "(top, int_dom_of_int 0, [])" .

lemma lookup_cinit_int_dom_st_for [simp]:
  "fun_of_resolved_st_q_for gs cinit_int_dom_st x =
   (if gs x then int_dom_of_int 0 else top)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_int_dom_st_for:
  "fun_of_resolved_st_q_for gs cinit_int_dom_st =
   (%x. if gs x then int_dom_of_int 0 else top)"
  by (rule ext) simp

subsection \<open>Refine_Never\<close>

definition int_dom_ops_never :: "int_dom numeric_ops" where
  "int_dom_ops_never = (| n_aval = aval_int_dom Refine_Never,
                          n_bfilter = branch_int_dom_never_st,
                          n_top = top |)"

definition branch_int_dom_never_st_for ::
    "(vname => bool) => exp => bool => int_dom resolved_st_q => int_dom resolved_st_q"
where
  "branch_int_dom_never_st_for = generic_branch_st_for int_dom_ops_never"

lemma branch_int_dom_never_st_for_eq [simp]:
  "branch_int_dom_never_st_for gs b pol s = branch_int_dom_never_st gs b pol s"
  by (simp add: branch_int_dom_never_st_for_def generic_branch_st_for_def int_dom_ops_never_def)

definition int_dom_enter_never_st_for ::
    "(vname => bool) => call_info =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_never_st_for = generic_enter_st_for int_dom_ops_never"

lemma int_dom_enter_never_st_for_eq [simp]:
  "int_dom_enter_never_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (%e. aval_int_dom Refine_Never e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_never_st_for_def generic_enter_st_for_def int_dom_ops_never_def)

fun int_tf_st_never_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
    "int_tf_st_never_for gs EA_Nop s = s"
  | "int_tf_st_never_for gs (EA_Assign x a) s =
       update_resolved_st_q s (location_of gs x)
         (aval_int_dom Refine_Never a (fun_of_resolved_st_q_for gs s))"
  | "int_tf_st_never_for gs (EA_Special sc x) s =
       update_resolved_st_q s (location_of gs x)
         (case sc of
            Nondet_Int => top
          | Min a b => int_dom_min Refine_Never
                         (aval_int_dom Refine_Never a (fun_of_resolved_st_q_for gs s))
                         (aval_int_dom Refine_Never b (fun_of_resolved_st_q_for gs s))
          | Max a b => int_dom_max Refine_Never
                         (aval_int_dom Refine_Never a (fun_of_resolved_st_q_for gs s))
                         (aval_int_dom Refine_Never b (fun_of_resolved_st_q_for gs s)))"
  | "int_tf_st_never_for gs (EA_Assume b) s =
       branch_int_dom_never_st_for gs b True s"
  | "int_tf_st_never_for gs (EA_AssumeNot b) s =
       branch_int_dom_never_st_for gs b False s"
  | "int_tf_st_never_for gs (EA_Body p) s = s"
  | "int_tf_st_never_for gs (EA_Ret None p) s = s"
  | "int_tf_st_never_for gs (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of gs ret_var)
         (aval_int_dom Refine_Never a (fun_of_resolved_st_q_for gs s))"
  | "int_tf_st_never_for gs (EA_Check cnd) s = s"

theorem int_tf_st_never_for_commute:
  assumes "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (int_tf_st_never_for gs a s) =
     int_tf_abs Refine_Never a (fun_of_resolved_st_q_for gs s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by (simp add: skip_int_dom_def)
next
  case (EA_Assign x e)
  then show ?thesis by (simp add: assign_int_dom_def)
next
  case (EA_Special sc x)
  then show ?thesis by (auto split: special_call.splits)
next
  case (EA_Assume b)
  then show ?thesis
    using assms by (simp add: int_dom_backward_never.branch_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis
    using assms by (simp add: int_dom_backward_never.branch_st_commute)
next
  case (EA_Body p)
  then show ?thesis by (simp add: body_int_dom_def)
next
  case (EA_Ret ea p)
  then show ?thesis
  proof (cases ea)
    case None
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_int_dom_def)
  next
    case (Some av)
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_int_dom_def assign_int_dom_def)
  qed
next
  case (EA_Check c)
  then show ?thesis by (simp add: event_int_dom_def)
qed

lemma int_dom_enter_never_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_never_st_for gs ci s) =
   enter_int_dom_ci_for Refine_Never gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_int_dom_ci_for_def enter_int_dom_for_def enter_binding_def
                enter_frame_def enter_frame_int_dom_for_def fun_of_resolved_st_q_for_enter_frame)


subsection \<open>Refine_Once\<close>

definition int_dom_ops_once :: "int_dom numeric_ops" where
  "int_dom_ops_once = (| n_aval = aval_int_dom Refine_Once,
                         n_bfilter = branch_int_dom_once_st,
                         n_top = top |)"

definition branch_int_dom_once_st_for ::
    "(vname => bool) => exp => bool => int_dom resolved_st_q => int_dom resolved_st_q"
where
  "branch_int_dom_once_st_for = generic_branch_st_for int_dom_ops_once"

lemma branch_int_dom_once_st_for_eq [simp]:
  "branch_int_dom_once_st_for gs b pol s = branch_int_dom_once_st gs b pol s"
  by (simp add: branch_int_dom_once_st_for_def generic_branch_st_for_def int_dom_ops_once_def)

definition int_dom_enter_once_st_for ::
    "(vname => bool) => call_info =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_once_st_for = generic_enter_st_for int_dom_ops_once"

lemma int_dom_enter_once_st_for_eq [simp]:
  "int_dom_enter_once_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (%e. aval_int_dom Refine_Once e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_once_st_for_def generic_enter_st_for_def int_dom_ops_once_def)

fun int_tf_st_once_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
    "int_tf_st_once_for gs EA_Nop s = s"
  | "int_tf_st_once_for gs (EA_Assign x a) s =
       update_resolved_st_q s (location_of gs x)
         (aval_int_dom Refine_Once a (fun_of_resolved_st_q_for gs s))"
  | "int_tf_st_once_for gs (EA_Special sc x) s =
       update_resolved_st_q s (location_of gs x)
         (case sc of
            Nondet_Int => top
          | Min a b => int_dom_min Refine_Once
                         (aval_int_dom Refine_Once a (fun_of_resolved_st_q_for gs s))
                         (aval_int_dom Refine_Once b (fun_of_resolved_st_q_for gs s))
          | Max a b => int_dom_max Refine_Once
                         (aval_int_dom Refine_Once a (fun_of_resolved_st_q_for gs s))
                         (aval_int_dom Refine_Once b (fun_of_resolved_st_q_for gs s)))"
  | "int_tf_st_once_for gs (EA_Assume b) s =
       branch_int_dom_once_st_for gs b True s"
  | "int_tf_st_once_for gs (EA_AssumeNot b) s =
       branch_int_dom_once_st_for gs b False s"
  | "int_tf_st_once_for gs (EA_Body p) s = s"
  | "int_tf_st_once_for gs (EA_Ret None p) s = s"
  | "int_tf_st_once_for gs (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of gs ret_var)
         (aval_int_dom Refine_Once a (fun_of_resolved_st_q_for gs s))"
  | "int_tf_st_once_for gs (EA_Check cnd) s = s"

theorem int_tf_st_once_for_commute:
  assumes "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (int_tf_st_once_for gs a s) =
     int_tf_abs Refine_Once a (fun_of_resolved_st_q_for gs s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by (simp add: skip_int_dom_def)
next
  case (EA_Assign x e)
  then show ?thesis by (simp add: assign_int_dom_def)
next
  case (EA_Special sc x)
  then show ?thesis by (auto split: special_call.splits)
next
  case (EA_Assume b)
  then show ?thesis
    using assms by (simp add: int_dom_backward_once.branch_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis
    using assms by (simp add: int_dom_backward_once.branch_st_commute)
next
  case (EA_Body p)
  then show ?thesis by (simp add: body_int_dom_def)
next
  case (EA_Ret ea p)
  then show ?thesis
  proof (cases ea)
    case None
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_int_dom_def)
  next
    case (Some av)
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_int_dom_def assign_int_dom_def)
  qed
next
  case (EA_Check c)
  then show ?thesis by (simp add: event_int_dom_def)
qed

lemma int_dom_enter_once_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_once_st_for gs ci s) =
   enter_int_dom_ci_for Refine_Once gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_int_dom_ci_for_def enter_int_dom_for_def enter_binding_def
                enter_frame_def enter_frame_int_dom_for_def fun_of_resolved_st_q_for_enter_frame)


subsection \<open>Refine_Fixpoint\<close>

definition int_dom_ops_fixpoint :: "int_dom numeric_ops" where
  "int_dom_ops_fixpoint = (| n_aval = aval_int_dom Refine_Fixpoint,
                             n_bfilter = branch_int_dom_fixpoint_st,
                             n_top = top |)"

definition branch_int_dom_fixpoint_st_for ::
    "(vname => bool) => exp => bool => int_dom resolved_st_q => int_dom resolved_st_q"
where
  "branch_int_dom_fixpoint_st_for = generic_branch_st_for int_dom_ops_fixpoint"

lemma branch_int_dom_fixpoint_st_for_eq [simp]:
  "branch_int_dom_fixpoint_st_for gs b pol s = branch_int_dom_fixpoint_st gs b pol s"
  by (simp add: branch_int_dom_fixpoint_st_for_def generic_branch_st_for_def int_dom_ops_fixpoint_def)

definition int_dom_enter_fixpoint_st_for ::
    "(vname => bool) => call_info =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_fixpoint_st_for = generic_enter_st_for int_dom_ops_fixpoint"

lemma int_dom_enter_fixpoint_st_for_eq [simp]:
  "int_dom_enter_fixpoint_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (%e. aval_int_dom Refine_Fixpoint e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_fixpoint_st_for_def generic_enter_st_for_def int_dom_ops_fixpoint_def)

fun int_tf_st_fixpoint_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
    "int_tf_st_fixpoint_for gs EA_Nop s = s"
  | "int_tf_st_fixpoint_for gs (EA_Assign x a) s =
       update_resolved_st_q s (location_of gs x)
         (aval_int_dom Refine_Fixpoint a (fun_of_resolved_st_q_for gs s))"
  | "int_tf_st_fixpoint_for gs (EA_Special sc x) s =
       update_resolved_st_q s (location_of gs x)
         (case sc of
            Nondet_Int => top
          | Min a b => int_dom_min Refine_Fixpoint
                         (aval_int_dom Refine_Fixpoint a (fun_of_resolved_st_q_for gs s))
                         (aval_int_dom Refine_Fixpoint b (fun_of_resolved_st_q_for gs s))
          | Max a b => int_dom_max Refine_Fixpoint
                         (aval_int_dom Refine_Fixpoint a (fun_of_resolved_st_q_for gs s))
                         (aval_int_dom Refine_Fixpoint b (fun_of_resolved_st_q_for gs s)))"
  | "int_tf_st_fixpoint_for gs (EA_Assume b) s =
       branch_int_dom_fixpoint_st_for gs b True s"
  | "int_tf_st_fixpoint_for gs (EA_AssumeNot b) s =
       branch_int_dom_fixpoint_st_for gs b False s"
  | "int_tf_st_fixpoint_for gs (EA_Body p) s = s"
  | "int_tf_st_fixpoint_for gs (EA_Ret None p) s = s"
  | "int_tf_st_fixpoint_for gs (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of gs ret_var)
         (aval_int_dom Refine_Fixpoint a (fun_of_resolved_st_q_for gs s))"
  | "int_tf_st_fixpoint_for gs (EA_Check cnd) s = s"

theorem int_tf_st_fixpoint_for_commute:
  assumes "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (int_tf_st_fixpoint_for gs a s) =
     int_tf_abs Refine_Fixpoint a (fun_of_resolved_st_q_for gs s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by (simp add: skip_int_dom_def)
next
  case (EA_Assign x e)
  then show ?thesis by (simp add: assign_int_dom_def)
next
  case (EA_Special sc x)
  then show ?thesis by (auto split: special_call.splits)
next
  case (EA_Assume b)
  then show ?thesis
    using assms by (simp add: int_dom_backward_fixpoint.branch_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis
    using assms by (simp add: int_dom_backward_fixpoint.branch_st_commute)
next
  case (EA_Body p)
  then show ?thesis by (simp add: body_int_dom_def)
next
  case (EA_Ret ea p)
  then show ?thesis
  proof (cases ea)
    case None
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_int_dom_def)
  next
    case (Some av)
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_int_dom_def assign_int_dom_def)
  qed
next
  case (EA_Check c)
  then show ?thesis by (simp add: event_int_dom_def)
qed

lemma int_dom_enter_fixpoint_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_fixpoint_st_for gs ci s) =
   enter_int_dom_ci_for Refine_Fixpoint gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_int_dom_ci_for_def enter_int_dom_for_def enter_binding_def
                enter_frame_def enter_frame_int_dom_for_def fun_of_resolved_st_q_for_enter_frame)


end
