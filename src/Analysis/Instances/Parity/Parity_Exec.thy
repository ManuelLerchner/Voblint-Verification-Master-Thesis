theory Parity_Exec
  imports Voblint_Core.Exec_Bridge Parity_Transfer
begin

section \<open>Parity executable seam: transfer mirror and commutation\<close>

instance parity :: bounded_warrowing ..

subsection \<open>Enter mirror (reset locals to Top, keep globals)\<close>

definition enter_parity_st :: "parity st \<Rightarrow> parity st" where
  "enter_parity_st = enter_frame_D_st PTop"

lemma enter_frame_parity_st_commute:
  "fun_of_st (enter_parity_st s) = enter_frame_parity (fun_of_st s)"
  unfolding enter_parity_st_def enter_frame_parity_def
  by (rule fun_of_st_enter_frame_D_st)

subsection \<open>The executable parity transfer function\<close>

fun parity_tf_st :: "edge_action \<Rightarrow> parity st \<Rightarrow> parity st" where
    "parity_tf_st EA_Nop s = s"
  | "parity_tf_st (EA_Assign x a) s = update_st s x (aval_parity a (lookup_st s))"
  | "parity_tf_st (EA_Assume b) s = s"
  | "parity_tf_st (EA_AssumeNot b) s = s"
  | "parity_tf_st (EA_Ret e _) s = (case e of
      None \<Rightarrow> s
    | Some a \<Rightarrow> update_st s ret_var (aval_parity a (lookup_st s)))"

lemma parity_tf_st_ret_none [simp]:
  "parity_tf_st (EA_Ret None p) = parity_tf_st EA_Nop"
  by (rule ext) simp

lemma parity_tf_st_ret_some [simp]:
  "parity_tf_st (EA_Ret (Some a) p) = parity_tf_st (EA_Assign ret_var a)"
  by (rule ext) simp

theorem parity_tf_st_commute:
  "fun_of_st (parity_tf_st a s) = apply_tf parity_tf a (fun_of_st s)"
proof (rule apply_tf_wrap_eqI[where H = "\<lambda>f. f (fun_of_st s)"])
  show "\<And>p. fun_of_st (parity_tf_st (EA_Ret None p) s) = fun_of_st (parity_tf_st EA_Nop s)" by simp
  show "\<And>a p. fun_of_st (parity_tf_st (EA_Ret (Some a) p) s)
                = fun_of_st (parity_tf_st (EA_Assign ret_var a) s)"
    by simp
  show "fun_of_st (parity_tf_st EA_Nop s) = apply_tf parity_tf EA_Nop (fun_of_st s)" by simp
  show "\<And>x e. fun_of_st (parity_tf_st (EA_Assign x e) s) = apply_tf parity_tf (EA_Assign x e) (fun_of_st s)"
    by (simp add: parity_tf_def assign_parity_def)
  show "\<And>b. fun_of_st (parity_tf_st (EA_Assume b) s) = apply_tf parity_tf (EA_Assume b) (fun_of_st s)"
    by (simp add: parity_tf_def assume_parity_def)
  show "\<And>b. fun_of_st (parity_tf_st (EA_AssumeNot b) s) = apply_tf parity_tf (EA_AssumeNot b) (fun_of_st s)"
    by (simp add: parity_tf_def assume_not_parity_def)
qed

subsection \<open>Executable effectful transfer record\<close>

text \<open>The named caller-entry transfer is shared by the effectful transfer record and the D/G
  registration, so executable entry semantics has one implementation.\<close>
definition parity_enter_st :: "vname list \<Rightarrow> aexp list \<Rightarrow> parity st \<Rightarrow> parity st" where
  "parity_enter_st xs es s =
     bind_formals_abs_st xs (map (\<lambda>e. aval_parity e (lookup_st s)) es) (enter_parity_st s)"

lemma parity_enter_st_commute:
  "fun_of_st (parity_enter_st xs es s) = tf_enter parity_tf xs es (fun_of_st s)"
  by (simp add: parity_enter_st_def parity_tf_def enter_parity_def enter_D_def
                enter_frame_parity_def enter_frame_parity_st_commute)

subsection \<open>Analysis seeds\<close>

text \<open>
  \<open>top_parity_st\<close> is unknown everywhere (\<open>gamma_state = UNIV\<close>).  \<open>cinit_parity_st\<close>
  reflects C zero-initialisation: globals \<open>PEven\<close> (0 is even), locals \<open>PTop\<close>.
\<close>

lift_definition top_parity_st :: "parity st" is "(PTop, PTop, [])" .

lemma lookup_top_parity_st [simp]: "lookup_st top_parity_st x = PTop"
  by transfer simp

lemma fun_of_st_top_parity_st: "fun_of_st top_parity_st = (\<lambda>_. PTop)"
  by (rule ext) simp

lift_definition cinit_parity_st :: "parity st" is "(PTop, PEven, [])" .

lemma lookup_cinit_parity_st [simp]:
  "lookup_st cinit_parity_st x = (if is_global x then PEven else PTop)"
  by transfer simp

lemma fun_of_st_cinit_parity_st:
  "fun_of_st cinit_parity_st = (\<lambda>x. if is_global x then PEven else PTop)"
  by (rule ext) simp

end
