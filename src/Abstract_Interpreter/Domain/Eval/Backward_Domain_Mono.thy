theory Backward_Domain_Mono
  imports Backward_Domain
begin

section \<open>Monotone inverse operators\<close>

text \<open>A domain states its inverse operators' monotonicity with \<open>le_pair\<close>.\<close>

subsection \<open>Pairwise order for reductive/monotone inverse operators\<close>

text \<open>
  A minimal componentwise order on \<open>'a * 'a\<close>, used only to state each inverse
  operator's monotonicity and reductiveness as a single fact about its returned
  pair rather than as two separately-assumed projections. Deliberately not
  \<open>'a * 'a\<close>'s own \<open>\<le>\<close>: some already-transitively-imported theory instantiates
  \<open>('a,'b) prod :: order\<close> here with a non-componentwise (order-with-a-\<open><\<close>-disjunct)
  definition, so relying on the ambient \<open>\<le>\<close> would silently pick up the wrong
  relation. This local, self-contained \<open>\<le>_pair\<close> avoids that entirely.
\<close>

abbreviation le_pair :: "'a::order \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "le_pair p q \<equiv> fst p \<le> fst q \<and> snd p \<le> snd q"

lemma le_pair_fst: "le_pair p q \<Longrightarrow> fst p \<le> fst q"
  by simp

lemma le_pair_snd: "le_pair p q \<Longrightarrow> snd p \<le> snd q"
  by simp

end
