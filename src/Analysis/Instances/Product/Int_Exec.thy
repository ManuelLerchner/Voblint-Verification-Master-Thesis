theory Int_Exec
  imports Voblint_Core.Exec_Refinement Voblint_Core.Numeric_Ops
    Voblint_Core.DG_LTR_Sound Int_Transfer
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
  "int_dom_ops_never = (| n_aval = aval_int_dom_t Refine_Never,
                          n_bfilter = branch_int_dom_never_st,
                          n_top = top |)"

definition branch_int_dom_never_st_for ::
    "(vname => bool) => texp => bool => int_dom resolved_st_q => int_dom resolved_st_q"
where
  "branch_int_dom_never_st_for = generic_branch_st_for int_dom_ops_never"

lemma branch_int_dom_never_st_for_eq [simp]:
  "branch_int_dom_never_st_for source_global b pol s = branch_int_dom_never_st source_global b pol s"
  by (simp add: branch_int_dom_never_st_for_def generic_branch_st_for_def int_dom_ops_never_def)

definition int_dom_enter_never_st_for ::
    "(vname => bool) => vname list => texp list =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_never_st_for = generic_enter_st_for int_dom_ops_never"

lemma int_dom_enter_never_st_for_eq [simp]:
  "int_dom_enter_never_st_for source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map (%e. aval_int_dom_t Refine_Never e (fun_of_resolved_st_q_for source_global s)) es)
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_never_st_for_def generic_enter_st_for_def int_dom_ops_never_def)

fun int_tf_st_never_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
    "int_tf_st_never_for source_global EA_Nop s = s"
  | "int_tf_st_never_for source_global (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (aval_int_dom_t Refine_Never a (fun_of_resolved_st_q_for source_global s))"
  | "int_tf_st_never_for source_global (EA_Special sc x) s =
       update_resolved_st_q s (location_of source_global x)
         (case sc of
            Nondet_Int k => refine Refine_Never (int_dom_cast k top)
          | Min k a b => int_dom_cast k
              (int_dom_min Refine_Never
                (aval_int_dom_t Refine_Never a (fun_of_resolved_st_q_for source_global s))
                (aval_int_dom_t Refine_Never b (fun_of_resolved_st_q_for source_global s)))
          | Max k a b => int_dom_cast k
              (int_dom_max Refine_Never
                (aval_int_dom_t Refine_Never a (fun_of_resolved_st_q_for source_global s))
                (aval_int_dom_t Refine_Never b (fun_of_resolved_st_q_for source_global s))))"
  | "int_tf_st_never_for source_global (EA_Assume b) s =
       branch_int_dom_never_st_for source_global b True s"
  | "int_tf_st_never_for source_global (EA_AssumeNot b) s =
       branch_int_dom_never_st_for source_global b False s"
  | "int_tf_st_never_for source_global (EA_Ret None p rk) s = s"
  | "int_tf_st_never_for source_global (EA_Ret (Some a) p rk) s =
       update_resolved_st_q s (location_of source_global ret_var)
         (aval_int_dom_t Refine_Never a (fun_of_resolved_st_q_for source_global s))"
  | "int_tf_st_never_for source_global (EA_Check cnd) s = s"

text \<open>
  \<open>int_tf_st_never_for\<close> satisfies \<open>action_reduces\<close>: a void return and a
  check behave exactly like \<open>EA_Nop\<close>, and a value return is literally the
  \<^const>\<open>ret_var\<close> assignment it publishes, since the owning procedure's
  return kind rides inside the returned \<^typ>\<open>texp\<close> rather than beside it.
\<close>

lemma int_tf_st_never_for_action_reduces: "action_reduces (int_tf_st_never_for gs)"
  by unfold_locales (simp_all add: fun_eq_iff)

theorem int_tf_st_never_for_commute:
  "fun_of_resolved_st_q_for gs (int_tf_st_never_for gs a s) =
   apply_tf (int_tf_never_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_wrap_eqI[where H = "%f. f (fun_of_resolved_st_q_for gs s)"])
  show "fun_of_resolved_st_q_for gs (int_tf_st_never_for gs EA_Nop s) =
      apply_tf (int_tf_never_for gs) EA_Nop (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_never_for_def skip_int_dom_def)
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (int_tf_st_never_for gs (EA_Assign x e) s) =
    apply_tf (int_tf_never_for gs) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_never_for_def assign_int_dom_def)
  show "\<And>sc x. fun_of_resolved_st_q_for gs
      (int_tf_st_never_for gs (EA_Special sc x) s) =
    apply_tf (int_tf_never_for gs) (EA_Special sc x) (fun_of_resolved_st_q_for gs s)"
    by (auto simp: int_tf_never_for_def Let_def split: special_call.splits)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (int_tf_st_never_for gs (EA_Assume b) s) =
    apply_tf (int_tf_never_for gs) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_never_for_def int_dom_backward_never.branch_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (int_tf_st_never_for gs (EA_AssumeNot b) s) =
    apply_tf (int_tf_never_for gs) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_never_for_def int_dom_backward_never.branch_st_commute)
  show "\<And>ea p rk. fun_of_resolved_st_q_for gs
      (int_tf_st_never_for gs (EA_Ret ea p rk) s) =
    apply_tf (int_tf_never_for gs) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
  proof -
    fix ea p rk
    show "fun_of_resolved_st_q_for gs (int_tf_st_never_for gs (EA_Ret ea p rk) s) =
      apply_tf (int_tf_never_for gs) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
    proof (cases ea)
      case None
      then show ?thesis by (simp add: int_tf_never_for_def return_int_dom_def)
    next
      case (Some a)
      then show ?thesis by (simp add: int_tf_never_for_def return_int_dom_def)
    qed
  qed
  show "\<And>c. fun_of_resolved_st_q_for gs
      (int_tf_st_never_for gs (EA_Check c) s) =
    apply_tf (int_tf_never_for gs) (EA_Check c) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_never_for_def event_int_dom_def)
qed

lemma int_dom_enter_never_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_never_st_for gs xs es s) =
   tf_enter (int_tf_never_for gs) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: int_tf_never_for_def enter_int_dom_for_def enter_D_def
                enter_frame_int_dom_for_def enter_frame_D_def)

subsection \<open>Refine_Once\<close>

definition int_dom_ops_once :: "int_dom numeric_ops" where
  "int_dom_ops_once = (| n_aval = aval_int_dom_t Refine_Once,
                          n_bfilter = branch_int_dom_once_st,
                          n_top = top |)"

definition branch_int_dom_once_st_for ::
    "(vname => bool) => texp => bool => int_dom resolved_st_q => int_dom resolved_st_q"
where
  "branch_int_dom_once_st_for = generic_branch_st_for int_dom_ops_once"

lemma branch_int_dom_once_st_for_eq [simp]:
  "branch_int_dom_once_st_for source_global b pol s = branch_int_dom_once_st source_global b pol s"
  by (simp add: branch_int_dom_once_st_for_def generic_branch_st_for_def int_dom_ops_once_def)

definition int_dom_enter_once_st_for ::
    "(vname => bool) => vname list => texp list =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_once_st_for = generic_enter_st_for int_dom_ops_once"

lemma int_dom_enter_once_st_for_eq [simp]:
  "int_dom_enter_once_st_for source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map (%e. aval_int_dom_t Refine_Once e (fun_of_resolved_st_q_for source_global s)) es)
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_once_st_for_def generic_enter_st_for_def int_dom_ops_once_def)

fun int_tf_st_once_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
    "int_tf_st_once_for source_global EA_Nop s = s"
  | "int_tf_st_once_for source_global (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (aval_int_dom_t Refine_Once a (fun_of_resolved_st_q_for source_global s))"
  | "int_tf_st_once_for source_global (EA_Special sc x) s =
       update_resolved_st_q s (location_of source_global x)
         (case sc of
            Nondet_Int k => refine Refine_Once (int_dom_cast k top)
          | Min k a b => int_dom_cast k
              (int_dom_min Refine_Once
                (aval_int_dom_t Refine_Once a (fun_of_resolved_st_q_for source_global s))
                (aval_int_dom_t Refine_Once b (fun_of_resolved_st_q_for source_global s)))
          | Max k a b => int_dom_cast k
              (int_dom_max Refine_Once
                (aval_int_dom_t Refine_Once a (fun_of_resolved_st_q_for source_global s))
                (aval_int_dom_t Refine_Once b (fun_of_resolved_st_q_for source_global s))))"
  | "int_tf_st_once_for source_global (EA_Assume b) s =
       branch_int_dom_once_st_for source_global b True s"
  | "int_tf_st_once_for source_global (EA_AssumeNot b) s =
       branch_int_dom_once_st_for source_global b False s"
  | "int_tf_st_once_for source_global (EA_Ret None p rk) s = s"
  | "int_tf_st_once_for source_global (EA_Ret (Some a) p rk) s =
       update_resolved_st_q s (location_of source_global ret_var)
         (aval_int_dom_t Refine_Once a (fun_of_resolved_st_q_for source_global s))"
  | "int_tf_st_once_for source_global (EA_Check cnd) s = s"

text \<open>
  \<open>int_tf_st_once_for\<close> satisfies \<open>action_reduces\<close>, for the same reason
  \<open>int_tf_st_never_for\<close> does.
\<close>

lemma int_tf_st_once_for_action_reduces: "action_reduces (int_tf_st_once_for gs)"
  by unfold_locales (simp_all add: fun_eq_iff)

theorem int_tf_st_once_for_commute:
  "fun_of_resolved_st_q_for gs (int_tf_st_once_for gs a s) =
   apply_tf (int_tf_once_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_wrap_eqI[where H = "%f. f (fun_of_resolved_st_q_for gs s)"])
  show "fun_of_resolved_st_q_for gs (int_tf_st_once_for gs EA_Nop s) =
      apply_tf (int_tf_once_for gs) EA_Nop (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_once_for_def skip_int_dom_def)
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (int_tf_st_once_for gs (EA_Assign x e) s) =
    apply_tf (int_tf_once_for gs) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_once_for_def assign_int_dom_def)
  show "\<And>sc x. fun_of_resolved_st_q_for gs
      (int_tf_st_once_for gs (EA_Special sc x) s) =
    apply_tf (int_tf_once_for gs) (EA_Special sc x) (fun_of_resolved_st_q_for gs s)"
    by (auto simp: int_tf_once_for_def Let_def split: special_call.splits)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (int_tf_st_once_for gs (EA_Assume b) s) =
    apply_tf (int_tf_once_for gs) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_once_for_def int_dom_backward_once.branch_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (int_tf_st_once_for gs (EA_AssumeNot b) s) =
    apply_tf (int_tf_once_for gs) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_once_for_def int_dom_backward_once.branch_st_commute)
  show "\<And>ea p rk. fun_of_resolved_st_q_for gs
      (int_tf_st_once_for gs (EA_Ret ea p rk) s) =
    apply_tf (int_tf_once_for gs) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
  proof -
    fix ea p rk
    show "fun_of_resolved_st_q_for gs (int_tf_st_once_for gs (EA_Ret ea p rk) s) =
      apply_tf (int_tf_once_for gs) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
    proof (cases ea)
      case None
      then show ?thesis by (simp add: int_tf_once_for_def return_int_dom_def)
    next
      case (Some a)
      then show ?thesis by (simp add: int_tf_once_for_def return_int_dom_def)
    qed
  qed
  show "\<And>c. fun_of_resolved_st_q_for gs
      (int_tf_st_once_for gs (EA_Check c) s) =
    apply_tf (int_tf_once_for gs) (EA_Check c) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_once_for_def event_int_dom_def)
qed

lemma int_dom_enter_once_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_once_st_for gs xs es s) =
   tf_enter (int_tf_once_for gs) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: int_tf_once_for_def enter_int_dom_for_def enter_D_def
                enter_frame_int_dom_for_def enter_frame_D_def)

subsection \<open>Refine_Fixpoint\<close>

definition int_dom_ops_fixpoint :: "int_dom numeric_ops" where
  "int_dom_ops_fixpoint = (| n_aval = aval_int_dom_t Refine_Fixpoint,
                          n_bfilter = branch_int_dom_fixpoint_st,
                          n_top = top |)"

definition branch_int_dom_fixpoint_st_for ::
    "(vname => bool) => texp => bool => int_dom resolved_st_q => int_dom resolved_st_q"
where
  "branch_int_dom_fixpoint_st_for = generic_branch_st_for int_dom_ops_fixpoint"

lemma branch_int_dom_fixpoint_st_for_eq [simp]:
  "branch_int_dom_fixpoint_st_for source_global b pol s = branch_int_dom_fixpoint_st source_global b pol s"
  by (simp add: branch_int_dom_fixpoint_st_for_def generic_branch_st_for_def int_dom_ops_fixpoint_def)

definition int_dom_enter_fixpoint_st_for ::
    "(vname => bool) => vname list => texp list =>
      int_dom resolved_st_q => int_dom resolved_st_q"
where
  "int_dom_enter_fixpoint_st_for = generic_enter_st_for int_dom_ops_fixpoint"

lemma int_dom_enter_fixpoint_st_for_eq [simp]:
  "int_dom_enter_fixpoint_st_for source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map (%e. aval_int_dom_t Refine_Fixpoint e (fun_of_resolved_st_q_for source_global s)) es)
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_fixpoint_st_for_def generic_enter_st_for_def int_dom_ops_fixpoint_def)

fun int_tf_st_fixpoint_for ::
  "(vname => bool) => edge_action =>
   int_dom resolved_st_q => int_dom resolved_st_q" where
    "int_tf_st_fixpoint_for source_global EA_Nop s = s"
  | "int_tf_st_fixpoint_for source_global (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (aval_int_dom_t Refine_Fixpoint a (fun_of_resolved_st_q_for source_global s))"
  | "int_tf_st_fixpoint_for source_global (EA_Special sc x) s =
       update_resolved_st_q s (location_of source_global x)
         (case sc of
            Nondet_Int k => refine Refine_Fixpoint (int_dom_cast k top)
          | Min k a b => int_dom_cast k
              (int_dom_min Refine_Fixpoint
                (aval_int_dom_t Refine_Fixpoint a (fun_of_resolved_st_q_for source_global s))
                (aval_int_dom_t Refine_Fixpoint b (fun_of_resolved_st_q_for source_global s)))
          | Max k a b => int_dom_cast k
              (int_dom_max Refine_Fixpoint
                (aval_int_dom_t Refine_Fixpoint a (fun_of_resolved_st_q_for source_global s))
                (aval_int_dom_t Refine_Fixpoint b (fun_of_resolved_st_q_for source_global s))))"
  | "int_tf_st_fixpoint_for source_global (EA_Assume b) s =
       branch_int_dom_fixpoint_st_for source_global b True s"
  | "int_tf_st_fixpoint_for source_global (EA_AssumeNot b) s =
       branch_int_dom_fixpoint_st_for source_global b False s"
  | "int_tf_st_fixpoint_for source_global (EA_Ret None p rk) s = s"
  | "int_tf_st_fixpoint_for source_global (EA_Ret (Some a) p rk) s =
       update_resolved_st_q s (location_of source_global ret_var)
         (aval_int_dom_t Refine_Fixpoint a (fun_of_resolved_st_q_for source_global s))"
  | "int_tf_st_fixpoint_for source_global (EA_Check cnd) s = s"

text \<open>
  \<open>int_tf_st_fixpoint_for\<close> satisfies \<open>action_reduces\<close>, for the same reason
  \<open>int_tf_st_never_for\<close> does.
\<close>

lemma int_tf_st_fixpoint_for_action_reduces: "action_reduces (int_tf_st_fixpoint_for gs)"
  by unfold_locales (simp_all add: fun_eq_iff)

theorem int_tf_st_fixpoint_for_commute:
  "fun_of_resolved_st_q_for gs (int_tf_st_fixpoint_for gs a s) =
   apply_tf (int_tf_fixpoint_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_wrap_eqI[where H = "%f. f (fun_of_resolved_st_q_for gs s)"])
  show "fun_of_resolved_st_q_for gs (int_tf_st_fixpoint_for gs EA_Nop s) =
      apply_tf (int_tf_fixpoint_for gs) EA_Nop (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_fixpoint_for_def skip_int_dom_def)
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (int_tf_st_fixpoint_for gs (EA_Assign x e) s) =
    apply_tf (int_tf_fixpoint_for gs) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_fixpoint_for_def assign_int_dom_def)
  show "\<And>sc x. fun_of_resolved_st_q_for gs
      (int_tf_st_fixpoint_for gs (EA_Special sc x) s) =
    apply_tf (int_tf_fixpoint_for gs) (EA_Special sc x) (fun_of_resolved_st_q_for gs s)"
    by (auto simp: int_tf_fixpoint_for_def Let_def split: special_call.splits)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (int_tf_st_fixpoint_for gs (EA_Assume b) s) =
    apply_tf (int_tf_fixpoint_for gs) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_fixpoint_for_def int_dom_backward_fixpoint.branch_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (int_tf_st_fixpoint_for gs (EA_AssumeNot b) s) =
    apply_tf (int_tf_fixpoint_for gs) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_fixpoint_for_def int_dom_backward_fixpoint.branch_st_commute)
  show "\<And>ea p rk. fun_of_resolved_st_q_for gs
      (int_tf_st_fixpoint_for gs (EA_Ret ea p rk) s) =
    apply_tf (int_tf_fixpoint_for gs) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
  proof -
    fix ea p rk
    show "fun_of_resolved_st_q_for gs (int_tf_st_fixpoint_for gs (EA_Ret ea p rk) s) =
      apply_tf (int_tf_fixpoint_for gs) (EA_Ret ea p rk) (fun_of_resolved_st_q_for gs s)"
    proof (cases ea)
      case None
      then show ?thesis by (simp add: int_tf_fixpoint_for_def return_int_dom_def)
    next
      case (Some a)
      then show ?thesis by (simp add: int_tf_fixpoint_for_def return_int_dom_def)
    qed
  qed
  show "\<And>c. fun_of_resolved_st_q_for gs
      (int_tf_st_fixpoint_for gs (EA_Check c) s) =
    apply_tf (int_tf_fixpoint_for gs) (EA_Check c) (fun_of_resolved_st_q_for gs s)"
    by (simp add: int_tf_fixpoint_for_def event_int_dom_def)
qed

lemma int_dom_enter_fixpoint_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_fixpoint_st_for gs xs es s) =
   tf_enter (int_tf_fixpoint_for gs) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: int_tf_fixpoint_for_def enter_int_dom_for_def enter_D_def
                enter_frame_int_dom_for_def enter_frame_D_def)

end
