theory Interval_Point_Digest
  imports Interval_Domain
begin

section \<open>Interval point abstraction\<close>

text \<open>
  The point abstraction maps an integer to its singleton interval, and a slot is
  a \<^emph>\<open>point\<close> when it is such a singleton.  The exactness obligation holds because
  \<^term>\<open>gamma_ivl (Ivl (Fin v) (Fin v)) = {v}\<close>.
\<close>

definition ivl_decode :: "Int.int \<Rightarrow> ivl" where
  "ivl_decode v = Ivl (Fin v) (Fin v)"

definition ivl_is_point :: "ivl \<Rightarrow> bool" where
  "ivl_is_point a = (\<exists>v. a = Ivl (Fin v) (Fin v))"

lemma gamma_ivl_point: "gamma_ivl (Ivl (Fin v) (Fin v)) = {v}"
  by (auto intro: antisym)

text \<open>The point abstraction is exact on its own image: a decoded value concretises
  to exactly that value, and re-decodes to itself.\<close>

lemma ivl_decode_gamma: "gamma_ivl (ivl_decode v) = {v}"
  unfolding ivl_decode_def by (rule gamma_ivl_point)

lemma ivl_is_point_decode: "ivl_is_point (ivl_decode v)"
  by (simp add: ivl_is_point_def ivl_decode_def)

end
