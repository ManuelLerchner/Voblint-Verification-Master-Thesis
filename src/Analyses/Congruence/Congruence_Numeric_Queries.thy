theory Congruence_Numeric_Queries
  imports Congruence_Arithmetic "Voblint_Domain.Numeric_Queries"
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
  product \<open>int_dom\<close> reads them. The expression domain interpreted there also
  registers them as sound numeric queries, so this interpretation only gives
  them the name the check layer consumes and reuses that registered fact.
\<close>

global_interpretation congruence_numeric_queries:
  sound_numeric_queries congruence_lt congruence_eqb
  by (rule congruence_arith.sound_numeric_queries_axioms)

end
