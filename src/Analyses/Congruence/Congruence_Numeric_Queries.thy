theory Congruence_Numeric_Queries
  imports Congruence_Arithmetic "Voblint_Domain.Abstract_Numeric_Queries"
begin

section \<open>What a residue class can decide about order and equality\<close>

text \<open>
  Congruence answers the two comparison queries the check layer asks. Knowing
  a value only modulo some integer says nothing about its position on the
  number line. Ordering and equality are decided when both operands pin a
  single integer (modulus \<open>0\<close>); non-singletons yield \<open>None\<close>. Detecting
  disequality between disjoint non-singleton classes remains a precision gap.

  Both operations and their soundness already live in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Arithmetic\<close>, where the reduced
  product \<open>int_dom\<close> reads them. This theory only interprets the
  generic query interface at them, so the check layer can consume Congruence
  the same way it consumes every other domain.
\<close>

global_interpretation congruence_numeric_queries:
  abstract_numeric_queries congruence_lt congruence_eqb
proof unfold_locales
  fix a b :: congruence and r :: bool and i j :: int
  assume "congruence_lt a b = Some r" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  then show "(i < j) = r" using congruence_lt_sound by simp
next
  fix a b :: congruence and r :: bool and i j :: int
  assume "congruence_eqb a b = Some r" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  then show "(i = j) = r" using congruence_eqb_sound by simp
qed

end
