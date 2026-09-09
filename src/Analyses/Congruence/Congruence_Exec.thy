theory Congruence_Exec
  imports "Voblint_Exec.Exec_St_Restriction_Refinement" "Voblint_Nonrelational.Numeric_Ops"
    Congruence_Transfer Congruence_Warrowing
begin

section \<open>Running the transfer functions on the state the solver actually stores\<close>

text \<open>
  The solver does not hold a function from variables to residue classes; it
  holds a \<^typ>\<open>congruence resolved_st_q\<close>, a compact record with one slot for
  locals, one for globals, and an override list. This theory gives Congruence's
  eight operations on that carrier and proves each agrees with the abstract
  operation once the carrier is read back through
  \<^const>\<open>fun_of_resolved_st_q_for\<close>. That agreement -- \<open>commutation\<close> -- is what
  every later soundness statement is transported along.

  \<open>cinit_congruence_st\<close> below is the state a run starts in: a declared global
  holds the single integer \<open>0\<close>, every local is unconstrained.
\<close>

text \<open>
  \<^type>\<open>congruence\<close> is a \<^theory_text>\<open>typedef\<close> over the normalized representation, not a
  datatype, so \<^theory_text>\<open>lift_definition\<close> into \<^type>\<open>resolved_st_q\<close> descends through
  both quotients at once and lands on the raw pair type. These two states are
  therefore built the way \<^const>\<open>bot\<close> is at this type: an explicit
  \<^const>\<open>Abs_resolved_st\<close> of a triple, with no override entries.
\<close>

definition top_congruence_st :: "congruence resolved_st_q" where
  "top_congruence_st = Abs_resolved_st (top, top, [])"

lemma lookup_top_congruence_st [simp]:
  "fun_of_resolved_st_q_for is_global top_congruence_st x = top"
  unfolding fun_of_resolved_st_q_for_def top_congruence_st_def
  by (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_congruence_st:
  "fun_of_resolved_st_q_for is_global top_congruence_st = (\<lambda>_. top)"
  by (rule ext) simp

definition cinit_congruence_st :: "congruence resolved_st_q" where
  "cinit_congruence_st = Abs_resolved_st (top, congruence_of_int 0, [])"

lemma lookup_cinit_congruence_st [simp]:
  "fun_of_resolved_st_q_for is_global cinit_congruence_st x =
   (if is_global x then congruence_of_int 0 else top)"
  unfolding fun_of_resolved_st_q_for_def cinit_congruence_st_def
  by (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_congruence_st:
  "fun_of_resolved_st_q_for is_global cinit_congruence_st =
   (\<lambda>x. if is_global x then congruence_of_int 0 else top)"
  by (rule ext) simp

lemma lookup_cinit_congruence_st_for [simp]:
  "fun_of_resolved_st_q_for gs cinit_congruence_st x =
   (if gs x then congruence_of_int 0 else top)"
  unfolding fun_of_resolved_st_q_for_def cinit_congruence_st_def
  by (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_congruence_st_for:
  "fun_of_resolved_st_q_for gs cinit_congruence_st =
   (\<lambda>x. if gs x then congruence_of_int 0 else top)"
  by (rule ext) simp

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>
  \<open>congruence_ops\<close> bundles Congruence's own primitives
  (\<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close>): \<open>congruence_enter_st_for\<close> below is
  \<open>generic_enter_st_for\<close> instantiated at \<open>congruence_ops\<close>, not an independent
  definition, and Sign, Interval and Parity instantiate the same construction at
  their own primitives. \<open>branch_congruence_st_for\<close> reads the backward filter
  straight out of the record, since a branch transfer is that filter and needs no
  construction over it.
\<close>

definition congruence_ops :: "congruence numeric_ops" where
  "congruence_ops =
     \<lparr> n_aval = aval_congruence, n_bfilter = branch_congruence_st, n_top = top \<rparr>"

definition branch_congruence_st_for ::
  "(vname => bool) => exp => bool => congruence resolved_st_q => congruence resolved_st_q" where
  "branch_congruence_st_for = n_bfilter congruence_ops"

lemma branch_congruence_st_for_eq [simp]:
  "branch_congruence_st_for gs b pol s = branch_congruence_st gs b pol s"
  by (simp add: branch_congruence_st_for_def congruence_ops_def)

definition congruence_enter_st_for ::
  "(vname => bool) => call_info =>
   congruence resolved_st_q => congruence resolved_st_q" where
  "congruence_enter_st_for = generic_enter_st_for congruence_ops"

lemma congruence_enter_st_for_eq [simp]:
  "congruence_enter_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_congruence e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: congruence_enter_st_for_def generic_enter_st_for_def congruence_ops_def)

fun congruence_tf_st_for ::
  "(vname => bool) => edge_action =>
   congruence resolved_st_q => congruence resolved_st_q" where
    "congruence_tf_st_for gs EA_Nop s = s"
  | "congruence_tf_st_for gs (EA_Assign x a) s =
       update_resolved_st_q s (location_of gs x)
         (aval_congruence a (fun_of_resolved_st_q_for gs s))"
  | "congruence_tf_st_for gs (EA_Special sc x) s =
       update_resolved_st_q s (location_of gs x)
         (case sc of
            Nondet_Int => top
          | Min a b => congruence_min (aval_congruence a (fun_of_resolved_st_q_for gs s))
                                       (aval_congruence b (fun_of_resolved_st_q_for gs s))
          | Max a b => congruence_max (aval_congruence a (fun_of_resolved_st_q_for gs s))
                                       (aval_congruence b (fun_of_resolved_st_q_for gs s)))"
  | "congruence_tf_st_for gs (EA_Assume b) s =
       branch_congruence_st_for gs b True s"
  | "congruence_tf_st_for gs (EA_AssumeNot b) s =
       branch_congruence_st_for gs b False s"
  | "congruence_tf_st_for gs (EA_Body p) s = s"
  | "congruence_tf_st_for gs (EA_Ret None p) s = s"
  | "congruence_tf_st_for gs (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of gs ret_var)
         (aval_congruence a (fun_of_resolved_st_q_for gs s))"
  | "congruence_tf_st_for gs (EA_Check cnd) s = s"

subsection \<open>Classifier-parametric commutation\<close>

text \<open>
  The guard cases are the only ones that need the liveness premise: the backward
  filter's own commutation is stated on a live state, because a state with no
  live locations reads back as a map the filter can no longer distinguish. Every
  other case commutes unconditionally.
\<close>

theorem congruence_tf_st_for_commute:
  assumes "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (congruence_tf_st_for gs a s) =
     congruence_tf_abs a (fun_of_resolved_st_q_for gs s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by (simp add: skip_congruence_def)
next
  case (EA_Assign x e)
  then show ?thesis by (simp add: assign_congruence_def)
next
  case (EA_Special sc x)
  then show ?thesis by (auto split: special_call.splits)
next
  case (EA_Assume b)
  then show ?thesis
    using assms by (simp add: congruence_backward_domain.branch_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis
    using assms by (simp add: congruence_backward_domain.branch_st_commute)
next
  case (EA_Body p)
  then show ?thesis by (simp add: body_congruence_def)
next
  case (EA_Ret ea p)
  then show ?thesis
  proof (cases ea)
    case None
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_congruence_def)
  next
    case (Some av)
    then show ?thesis using \<open>a = EA_Ret ea p\<close>
      by (simp add: return_congruence_def assign_congruence_def)
  qed
next
  case (EA_Check c)
  then show ?thesis by (simp add: event_congruence_def)
qed

lemma enter_frame_congruence_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q top s) =
   enter_frame_congruence_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_frame_congruence_for_def)

lemma congruence_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (congruence_enter_st_for gs ci s) =
   enter_congruence_ci_for gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_congruence_ci_for_def enter_congruence_for_def enter_binding_def
                enter_frame_def enter_frame_congruence_for_def
                enter_frame_congruence_st_for_commute
                fun_of_resolved_st_q_for_enter_frame)

end
