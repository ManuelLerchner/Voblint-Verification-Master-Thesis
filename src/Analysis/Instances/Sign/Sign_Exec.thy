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

definition assume_sign_st :: "bexp \<Rightarrow> sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "assume_sign_st b s = bfilter_sign_st is_global b True s"

definition assume_not_sign_st :: "bexp \<Rightarrow> sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "assume_not_sign_st b s = bfilter_sign_st is_global b False s"

lemma assume_sign_st_commute:
  "fun_of_resolved_st_q_for is_global (assume_sign_st b s) =
   assume_sign b (fun_of_resolved_st_q_for is_global s)"
  by (simp add: assume_sign_st_def assume_sign_def bfilter_sign_st_commute)

lemma assume_not_sign_st_commute:
  "fun_of_resolved_st_q_for is_global (assume_not_sign_st b s) =
   assume_not_sign b (fun_of_resolved_st_q_for is_global s)"
  by (simp add: assume_not_sign_st_def assume_not_sign_def bfilter_sign_st_commute)

definition enter_sign_st :: "sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "enter_sign_st = enter_frame_D_resolved_q STop"

lemma enter_frame_sign_st_commute:
  "fun_of_resolved_st_q_for is_global (enter_sign_st s) =
   enter_frame_sign (fun_of_resolved_st_q_for is_global s)"
  by (simp add: enter_sign_st_def enter_frame_sign_def)

fun sign_tf_st :: "edge_action \<Rightarrow> sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
    "sign_tf_st EA_Nop s = s"
  | "sign_tf_st (EA_Assign x a) s =
       update_resolved_st_q s (location_of is_global x)
         (aval_sign a (fun_of_resolved_st_q_for is_global s))"
  | "sign_tf_st (EA_Assume b) s = assume_sign_st b s"
  | "sign_tf_st (EA_AssumeNot b) s = assume_not_sign_st b s"
  | "sign_tf_st (EA_Ret e _) s =
       (case e of None \<Rightarrow> s
        | Some a \<Rightarrow> update_resolved_st_q s (location_of is_global ret_var)
            (aval_sign a (fun_of_resolved_st_q_for is_global s)))"

lemma sign_tf_st_ret_none [simp]:
  "sign_tf_st (EA_Ret None p) = sign_tf_st EA_Nop"
  by (rule ext) simp

lemma sign_tf_st_ret_some [simp]:
  "sign_tf_st (EA_Ret (Some a) p) = sign_tf_st (EA_Assign ret_var a)"
  by (rule ext) simp

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

theorem sign_tf_st_commute:
  "fun_of_resolved_st_q_for is_global (sign_tf_st a s) =
   apply_tf sign_tf a (fun_of_resolved_st_q_for is_global s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for is_global s)"])
  show "\<And>p. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Ret None p) s) =
    fun_of_resolved_st_q_for is_global (sign_tf_st EA_Nop s)" by simp
  show "\<And>a p. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Ret (Some a) p) s) =
    fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Assign ret_var a) s)" by simp
  show "fun_of_resolved_st_q_for is_global (sign_tf_st EA_Nop s) =
      apply_tf sign_tf EA_Nop (fun_of_resolved_st_q_for is_global s)" by simp
  show "\<And>x e. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Assign x e) s) =
    apply_tf sign_tf (EA_Assign x e) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: sign_tf_def assign_sign_def)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Assume b) s) =
    apply_tf sign_tf (EA_Assume b) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: sign_tf_def assume_sign_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_AssumeNot b) s) =
    apply_tf sign_tf (EA_AssumeNot b)
      (fun_of_resolved_st_q_for is_global s)"
    by (simp add: sign_tf_def assume_not_sign_st_commute)
qed

definition sign_enter_st :: "vname list \<Rightarrow> aexp list \<Rightarrow>
  sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "sign_enter_st xs es s =
     bind_formals_resolved_q is_global xs
       (map (\<lambda>e. aval_sign e (fun_of_resolved_st_q_for is_global s)) es)
       (enter_sign_st s)"

lemma sign_enter_st_commute:
  "fun_of_resolved_st_q_for is_global (sign_enter_st xs es s) =
   tf_enter sign_tf xs es (fun_of_resolved_st_q_for is_global s)"
  by (simp add: sign_enter_st_def sign_tf_def enter_sign_def enter_D_def
                enter_frame_sign_def enter_frame_sign_st_commute)

definition sign_etf_st :: "(unit, sign resolved_st_q) effectful_st_transfer" where
  "sign_etf_st = unit_etf_st_of_transfer sign_tf_st sign_enter_st"

lemma sign_etf_st_edge_tree:
  "apply_etf_st sign_etf_st a u = unit_edge_tree_st (sign_tf_st a) u"
  unfolding sign_etf_st_def
  by (rule apply_etf_st_unit_of_transfer[OF sign_tf_st_ret_none sign_tf_st_ret_some])

lemma sign_etf_st_combine_tree:
  "etf_combine_st sign_etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  unfolding sign_etf_st_def by (rule etf_combine_st_unit_of_transfer)

lemma sign_etf_st_enter_tree:
  "etf_st_enter sign_etf_st xs es u = unit_edge_tree_st (sign_enter_st xs es) u"
  unfolding sign_etf_st_def by (rule etf_st_enter_unit_of_transfer)

lemma sign_etf_st_enter_exists_unit:
  "\<And>u xs es. \<exists>f. etf_st_enter sign_etf_st xs es u = unit_edge_tree_st f u"
  using sign_etf_st_enter_tree by blast

lemma sign_etf_st_exists_unit:
  "\<And>a u. \<exists>f. apply_etf_st sign_etf_st a u = unit_edge_tree_st f u"
  using sign_etf_st_edge_tree by blast

value "fun_of_resolved_st_q_for is_global top_sign_st ''x''"
value "fun_of_resolved_st_q_for is_global cinit_sign_st ''Gx''"
value "fun_of_resolved_st_q_for is_global cinit_sign_st ''x''"

end

