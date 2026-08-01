theory Parity_Exec
  imports Voblint_Core.Exec_Bridge Parity_Transfer
begin

section \<open>Parity executable seam: transfer mirror and commutation\<close>

instance parity :: bounded_warrowing ..

definition enter_parity_st :: "parity resolved_st_q \<Rightarrow> parity resolved_st_q" where
  "enter_parity_st = enter_frame_D_resolved_q PTop"

lemma enter_frame_parity_st_commute:
  "fun_of_resolved_st_q_for is_global (enter_parity_st s) =
   enter_frame_parity (fun_of_resolved_st_q_for is_global s)"
  by (simp add: enter_parity_st_def enter_frame_parity_def)

fun parity_tf_st :: "edge_action \<Rightarrow> parity resolved_st_q \<Rightarrow> parity resolved_st_q" where
    "parity_tf_st EA_Nop s = s"
  | "parity_tf_st (EA_Assign x a) s =
       update_resolved_st_q s (location_of is_global x)
         (aval_parity a (fun_of_resolved_st_q_for is_global s))"
  | "parity_tf_st (EA_Assume b) s = s"
  | "parity_tf_st (EA_AssumeNot b) s = s"
  | "parity_tf_st (EA_Ret e _) s =
       (case e of None \<Rightarrow> s
        | Some a \<Rightarrow> update_resolved_st_q s (location_of is_global ret_var)
            (aval_parity a (fun_of_resolved_st_q_for is_global s)))"

lemma parity_tf_st_ret_none [simp]:
  "parity_tf_st (EA_Ret None p) = parity_tf_st EA_Nop"
  by (rule ext) simp

lemma parity_tf_st_ret_some [simp]:
  "parity_tf_st (EA_Ret (Some a) p) = parity_tf_st (EA_Assign ret_var a)"
  by (rule ext) simp

theorem parity_tf_st_commute:
  "fun_of_resolved_st_q_for is_global (parity_tf_st a s) =
   apply_tf parity_tf a (fun_of_resolved_st_q_for is_global s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for is_global s)"])
  show "\<And>p. fun_of_resolved_st_q_for is_global
      (parity_tf_st (EA_Ret None p) s) =
    fun_of_resolved_st_q_for is_global (parity_tf_st EA_Nop s)" by simp
  show "\<And>a p. fun_of_resolved_st_q_for is_global
      (parity_tf_st (EA_Ret (Some a) p) s) =
    fun_of_resolved_st_q_for is_global
      (parity_tf_st (EA_Assign ret_var a) s)" by simp
  show "fun_of_resolved_st_q_for is_global (parity_tf_st EA_Nop s) =
      apply_tf parity_tf EA_Nop (fun_of_resolved_st_q_for is_global s)" by simp
  show "\<And>x e. fun_of_resolved_st_q_for is_global
      (parity_tf_st (EA_Assign x e) s) =
    apply_tf parity_tf (EA_Assign x e) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: parity_tf_def assign_parity_def)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (parity_tf_st (EA_Assume b) s) =
    apply_tf parity_tf (EA_Assume b) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: parity_tf_def assume_parity_def)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (parity_tf_st (EA_AssumeNot b) s) =
    apply_tf parity_tf (EA_AssumeNot b)
      (fun_of_resolved_st_q_for is_global s)"
    by (simp add: parity_tf_def assume_not_parity_def)
qed

definition parity_enter_st :: "vname list \<Rightarrow> aexp list \<Rightarrow>
  parity resolved_st_q \<Rightarrow> parity resolved_st_q" where
  "parity_enter_st xs es s =
     bind_formals_resolved_q is_global xs
       (map (\<lambda>e. aval_parity e (fun_of_resolved_st_q_for is_global s)) es)
       (enter_parity_st s)"

lemma parity_enter_st_commute:
  "fun_of_resolved_st_q_for is_global (parity_enter_st xs es s) =
   tf_enter parity_tf xs es (fun_of_resolved_st_q_for is_global s)"
  by (simp add: parity_enter_st_def parity_tf_def enter_parity_def enter_D_def
                enter_frame_parity_def enter_frame_parity_st_commute)

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

end

