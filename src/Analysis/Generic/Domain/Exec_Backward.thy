theory Exec_Backward
  imports Exec_St
begin

section \<open>Generic executable mirror of backward filtering\<close>

text \<open>
  Every interpretation of @{locale backward_domain} gets an executable
  @{typ "'a st"} mirror of its @{text afilter} / @{text bfilter} for free:
  \<open>afilter_st\<close> / \<open>bfilter_st\<close> and their commutation with the abstract
  filters through @{const fun_of_st}, proved once here by the same induction
  every domain previously repeated by hand. A concrete domain names its own
  specialization via the \<open>defines\<close> clause of its existing
  \<open>backward_domain\<close> interpretation (see \<open>Sign_Backward\<close>,
  \<open>Interval_Backward\<close>); no per-domain proof is needed.
\<close>

context backward_domain
begin

fun afilter_st :: "aexp \<Rightarrow> 'a \<Rightarrow> 'a st \<Rightarrow> 'a st" where
    "afilter_st (V x) a s =
       update_st s x (meet a (lookup_st s x))"
  | "afilter_st (Plus e1 e2) a s =
       (let (a1, a2) = inv_plus a (aval_abs e1 (lookup_st s)) (aval_abs e2 (lookup_st s))
        in afilter_st e1 a1 (afilter_st e2 a2 s))"
  | "afilter_st (Minus e1 e2) a s =
       (let (a1, a2) = inv_minus a (aval_abs e1 (lookup_st s)) (aval_abs e2 (lookup_st s))
        in afilter_st e1 a1 (afilter_st e2 a2 s))"
  | "afilter_st (Times e1 e2) a s =
       (let (a1, a2) = inv_times a (aval_abs e1 (lookup_st s)) (aval_abs e2 (lookup_st s))
        in afilter_st e1 a1 (afilter_st e2 a2 s))"
  | "afilter_st _ a s = s"

fun bfilter_st :: "bexp \<Rightarrow> bool \<Rightarrow> 'a st \<Rightarrow> 'a st" where
    "bfilter_st (Less e1 e2) res s =
       (let (a1, a2) = inv_less res (aval_abs e1 (lookup_st s)) (aval_abs e2 (lookup_st s))
        in afilter_st e1 a1 (afilter_st e2 a2 s))"
  | "bfilter_st (Not b) res s = bfilter_st b (\<not> res) s"
  | "bfilter_st (And b1 b2) True s =
       bfilter_st b1 True (bfilter_st b2 True s)"
  | "bfilter_st (And b1 b2) False s =
       bfilter_st b1 False s \<squnion> bfilter_st b2 False s"
  | "bfilter_st (Or b1 b2) True s =
       bfilter_st b1 True s \<squnion> bfilter_st b2 True s"
  | "bfilter_st (Or b1 b2) False s =
       bfilter_st b1 False (bfilter_st b2 False s)"
  | "bfilter_st (Eq e1 e2) True s =
       (let a = meet (aval_abs e1 (lookup_st s)) (aval_abs e2 (lookup_st s))
        in afilter_st e1 a (afilter_st e2 a s))"
  | "bfilter_st _ _ s = s"

lemma afilter_st_commute:
  "fun_of_st (afilter_st e a s) = afilter e a (fun_of_st s)"
proof (induction e arbitrary: a s)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus e1 e2)
  show ?case by (simp add: Plus.IH split: prod.splits)
next
  case (Minus e1 e2)
  show ?case by (simp add: Minus.IH split: prod.splits)
next
  case (Times e1 e2)
  show ?case by (simp add: Times.IH split: prod.splits)
qed

lemma bfilter_st_commute:
  "fun_of_st (bfilter_st b res s) = bfilter b res (fun_of_st s)"
proof (induction b arbitrary: res s)
  case (Bc x)
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
  then show ?case by (simp add: afilter_st_commute split: prod.splits)
next
  case (Eq e1 e2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: afilter_st_commute Let_def)
  next
    case False
    then show ?thesis by simp
  qed
qed

end

end
