theory Compile_Size
  imports IMP2_Proc_to_CFG
begin

section \<open>Static allocation size of a compiled fragment\<close>

text \<open>
  \<^const>\<open>compile\<close> threads a counter and reports the first unused index.  \<open>csize\<close> gives the
  same information from the source syntax alone, and \<open>compile_next_id\<close> identifies the two.
  The counter range of a fragment is then an equation rather than an inequality, so a
  composite clause can name a sibling fragment's entry node before that sibling is compiled
  --- \<open>compile_counter_mono\<close> alone is too weak for that.
\<close>

fun csize :: "com \<Rightarrow> nat" where
  "csize SKIP = 1"
| "csize (Assign x a) = 2"
| "csize (Seq c1 c2) = csize c1 + csize c2"
| "csize (If b c1 c2) = 2 + csize c1 + csize c2"
| "csize (While b c) = 2 + csize c"
| "csize (Call dst q actuals) = 2"
| "csize (Return e) = 2"
| "csize Restore = 1"
| "csize Unwind = 1"

lemma csize_pos: "0 < csize c"
  by (induction c) auto

theorem compile_next_id:
  "compile \<Pi> p c n = (n', en, ex, E, K) \<Longrightarrow> n' = n + csize c"
proof (induction c arbitrary: n n' en ex E K rule: com.induct)
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile \<Pi> p c1 n = (n1, en1, ex1, E1, K1)"
    and c2: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)" and n': "n' = n2"
    by (auto split: prod.splits)
  from Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] n' show ?case by simp
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    and c2: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)" and n': "n' = Suc n2"
    by (auto split: prod.splits)
  from If.IH(1)[OF c1] If.IH(2)[OF c2] n' show ?case by simp
next
  case (While b c)
  then obtain n1 en1 ex1 E1 K1 where
    c1: "compile \<Pi> p c (Suc n) = (n1, en1, ex1, E1, K1)" and n': "n' = Suc n1"
    by (auto split: prod.splits)
  from While.IH[OF c1] n' show ?case by simp
qed (auto split: prod.splits option.splits)

text \<open>\<open>compile_counter_mono\<close> is the inequality consequence, so the equation is a strict
  strengthening of the existing counter fact.\<close>

lemma compile_counter_mono_via_csize:
  assumes "compile \<Pi> p c n = (n', en, ex, E, K)"
  shows "n \<le> n'"
  using compile_next_id[OF assms] by simp

text \<open>The projected form, convenient when only the counter is of interest.\<close>

lemma compile_fst_next_id:
  "fst (compile \<Pi> p c n) = n + csize c"
  using compile_next_id by (cases "compile \<Pi> p c n") simp

end
