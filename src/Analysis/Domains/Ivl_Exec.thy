theory Ivl_Exec
  imports Exec_Bridge Interval_Domain
begin

section \<open>Interval executable transfer mirror\<close>

instance ivl :: bounded_warrowing ..


text \<open>
  Executable mirror of @{const ivl_tf} on @{typ "ivl st"}, following
  the sign-domain pattern in @{file "Sign_Exec.thy"}.  Commutation lemmas hook
  into the generic @{theory Voblint_Analysis.Exec_Bridge} transport; no certified
  end-to-end soundness theory yet (cf.\ @{file "Sign_Exec_Sound.thy"}).
\<close>

lemma fun_of_st_update:
  "fun_of_st (update_st s x v) = (fun_of_st s)(x := v)"
  by (rule ext) (metis fun_upd_apply lookup_update_diff lookup_update_same)

subsection \<open>Backward filter mirror on @{typ "ivl st"}\<close>

fun afilter_ivl_st :: "aexp \<Rightarrow> ivl \<Rightarrow> ivl st \<Rightarrow> ivl st" where
    "afilter_ivl_st (BaseN (AExp.V x)) a s =
       update_st s x (meet_ivl a (lookup_st s x))"
  | "afilter_ivl_st (Plus e1 e2) a s =
       (let (a1, a2) = inv_plus_ivl a (aval_ivl e1 (lookup_st s)) (aval_ivl e2 (lookup_st s))
        in afilter_ivl_st e1 a1 (afilter_ivl_st e2 a2 s))"
  | "afilter_ivl_st (Minus e1 e2) a s =
       (let (a1, a2) = inv_minus_ivl a (aval_ivl e1 (lookup_st s)) (aval_ivl e2 (lookup_st s))
        in afilter_ivl_st e1 a1 (afilter_ivl_st e2 a2 s))"
  | "afilter_ivl_st (Times e1 e2) a s =
       (let (a1, a2) = inv_times_ivl a (aval_ivl e1 (lookup_st s)) (aval_ivl e2 (lookup_st s))
        in afilter_ivl_st e1 a1 (afilter_ivl_st e2 a2 s))"
  | "afilter_ivl_st _ a s = s"

fun bfilter_ivl_st :: "bexp \<Rightarrow> bool \<Rightarrow> ivl st \<Rightarrow> ivl st" where
    "bfilter_ivl_st (Less e1 e2) res s =
       (let (a1, a2) = inv_less_ivl res (aval_ivl e1 (lookup_st s)) (aval_ivl e2 (lookup_st s))
        in afilter_ivl_st e1 a1 (afilter_ivl_st e2 a2 s))"
  | "bfilter_ivl_st (Not b) res s = bfilter_ivl_st b (\<not> res) s"
  | "bfilter_ivl_st (And b1 b2) True s =
       bfilter_ivl_st b1 True (bfilter_ivl_st b2 True s)"
  | "bfilter_ivl_st (And b1 b2) False s =
       bfilter_ivl_st b1 False s \<squnion> bfilter_ivl_st b2 False s"
  | "bfilter_ivl_st (Or b1 b2) True s =
       bfilter_ivl_st b1 True s \<squnion> bfilter_ivl_st b2 True s"
  | "bfilter_ivl_st (Or b1 b2) False s =
       bfilter_ivl_st b1 False (bfilter_ivl_st b2 False s)"
  | "bfilter_ivl_st (Eq e1 e2) True s =
       (let a = meet_ivl (aval_ivl e1 (lookup_st s)) (aval_ivl e2 (lookup_st s))
        in afilter_ivl_st e1 a (afilter_ivl_st e2 a s))"
  | "bfilter_ivl_st _ _ s = s"

lemma afilter_ivl_st_commute:
  "fun_of_st (afilter_ivl_st e a s) = afilter_ivl e a (fun_of_st s)"
proof (induction e arbitrary: a s)
  case (BaseN x)
  show ?case by (cases x; simp add: fun_of_st_update)
next
  case (Plus e1 e2)
  show ?case by (simp add: Plus.IH)
next
  case (Minus e1 e2)
  show ?case by (simp add: Minus.IH)
next
  case (Times e1 e2)
  show ?case by (simp add: Times.IH)
qed

lemma bfilter_ivl_st_commute:
  "fun_of_st (bfilter_ivl_st b res s) = bfilter_ivl b res (fun_of_st s)"
proof (induction b arbitrary: res s)
  case (BaseB x)
  then show ?case by simp
next
  case (Not b)
  then show ?case by simp
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: And.IH)
  next
    case False
    then show ?thesis by (simp add: And.IH)
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: Or.IH)
  next
    case False
    then show ?thesis by (simp add: Or.IH)
  qed
next
  case (Less e1 e2)
  then show ?case by (simp add: afilter_ivl_st_commute split: prod.splits)
next
  case (Eq e1 e2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: afilter_ivl_st_commute Let_def)
  next
    case False
    then show ?thesis by simp
  qed
qed

definition assume_ivl_st :: "bexp \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "assume_ivl_st b s = bfilter_ivl_st b True s"

definition assume_not_ivl_st :: "bexp \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "assume_not_ivl_st b s = bfilter_ivl_st b False s"

lemma assume_ivl_st_commute:
  "fun_of_st (assume_ivl_st b s) = assume_ivl b (fun_of_st s)"
  by (simp add: assume_ivl_st_def assume_ivl_def bfilter_ivl_st_commute)

lemma assume_not_ivl_st_commute:
  "fun_of_st (assume_not_ivl_st b s) = assume_not_ivl b (fun_of_st s)"
  by (simp add: assume_not_ivl_st_def assume_not_ivl_def bfilter_ivl_st_commute)

subsection \<open>Enter mirror\<close>

lemma fun_rep_enter_ivl_rep:
  "fun_rep_st ((\<lambda>(dl, dg, ps). (Ivl MinInf PlusInf, dg, filter (\<lambda>(x, _). is_global x) ps)) r)
   = (\<lambda>x. if is_global x then fun_rep_st r x else Ivl MinInf PlusInf)"
proof -
  obtain dl dg ps where r: "r = (dl, dg, ps)" using prod_cases3 by blast
  show ?thesis unfolding r
    by (rule ext) (auto simp: map_of_filter_key split: option.split)
qed

lift_definition enter_ivl_st :: "ivl st \<Rightarrow> ivl st"
  is "\<lambda>(dl, dg, ps). (Ivl MinInf PlusInf, dg, filter (\<lambda>(x, _). is_global x) ps)"
  by (auto simp: eq_st_def fun_rep_enter_ivl_rep fun_eq_iff)

lemma enter_ivl_st_commute:
  "fun_of_st (enter_ivl_st s) = enter_ivl (fun_of_st s)"
  unfolding enter_ivl_def
  by transfer (simp add: fun_rep_enter_ivl_rep)

subsection \<open>Executable transfer function and seeds\<close>

fun ivl_tf_st :: "edge_action \<Rightarrow> ivl st \<Rightarrow> ivl st" where
    "ivl_tf_st EA_Nop s = s"
  | "ivl_tf_st (EA_Assign x a) s = update_st s x (aval_ivl a (lookup_st s))"
  | "ivl_tf_st (EA_Assume b) s = assume_ivl_st b s"
  | "ivl_tf_st (EA_AssumeNot b) s = assume_not_ivl_st b s"
  | "ivl_tf_st EA_Enter s = enter_ivl_st s"

lift_definition top_ivl_st :: "ivl st" is "(Ivl MinInf PlusInf, Ivl MinInf PlusInf, [])" .

lift_definition cinit_ivl_st :: "ivl st" is "(Ivl MinInf PlusInf, Ivl (Fin 0) (Fin 0), [])" .

lemma lookup_cinit_ivl_st [simp]:
  "lookup_st cinit_ivl_st x = (if is_global x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)"
  by transfer (auto split: if_splits)

lemma fun_of_st_cinit_ivl_st:
  "fun_of_st cinit_ivl_st = (\<lambda>x. if is_global x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)"
  by (rule ext) simp

lemma lookup_top_ivl_st [simp]: "lookup_st top_ivl_st x = Ivl MinInf PlusInf"
  by transfer simp

lemma fun_of_st_top_ivl_st:
  "fun_of_st top_ivl_st = (\<lambda>_. Ivl MinInf PlusInf)"
  by (rule ext) simp

theorem ivl_tf_st_commute:
  "fun_of_st (ivl_tf_st a s) = apply_tf ivl_tf a (fun_of_st s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by simp
next
  case (EA_Assign x e)
  then show ?thesis
    by (simp add: ivl_tf_def assign_ivl_def fun_of_st_update)
next
  case (EA_Assume b)
  then show ?thesis
    by (simp add: ivl_tf_def assume_ivl_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis
    by (simp add: ivl_tf_def assume_not_ivl_st_commute)
next
  case EA_Enter
  then show ?thesis by (simp add: ivl_tf_def enter_ivl_st_commute)
qed

value "lookup_st (ivl_tf_st (EA_Assume (Less (IMP2_Syntax.V ''x'') (IMP2_Syntax.N 20)))
           (update_st top_ivl_st ''x'' (Ivl (Fin 0) (Fin 20)))) ''x''"

end
