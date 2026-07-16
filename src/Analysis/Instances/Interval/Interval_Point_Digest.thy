theory Interval_Point_Digest
  imports
    "Voblint_Analysis.Seed_EnterMono_Lift"
    Interval_Domain
begin

section \<open>Interval as a point-digest domain\<close>

text \<open>
  The interval instance of the \<^locale>\<open>point_digest\<close> capability
  (\<^theory>\<open>Voblint_Analysis.Seed_EnterMono_Lift\<close>): the point abstraction maps an
  integer to its singleton interval, and a slot is a \<^emph>\<open>point\<close> when it is such a
  singleton.  The one precision obligation \<open>point_exact\<close> holds because
  \<^term>\<open>gamma_ivl (Ivl (Fin v) (Fin v)) = {v}\<close>.

  Interpreting the locale exports the domain-generic ENTER_MONO kernel
  (\<open>ivl_point.enter_mono_point\<close>, \<open>ivl_point.point_route_eq\<close>,
  \<open>ivl_point.seed_glob_from_point_route\<close>) at the interval carrier.  These discharge
  the routing / seed obligations of the activation-indexed soundness backbone for
  point (constant-argument) contexts without any interval- or program-specific
  shortcut.  The interpretation names no program variable: the projection variable
  is supplied by the client (\<open>proj_var\<close> in the kernel), not fixed here.
\<close>

definition ivl_decode :: "Int.int \<Rightarrow> ivl" where
  "ivl_decode v = Ivl (Fin v) (Fin v)"

definition ivl_is_point :: "ivl \<Rightarrow> bool" where
  "ivl_is_point a = (\<exists>v. a = Ivl (Fin v) (Fin v))"

lemma gamma_ivl_point: "gamma_ivl (Ivl (Fin v) (Fin v)) = {v}"
  by (auto intro: antisym)

interpretation ivl_point: point_digest ivl_decode ivl_is_point
proof
  fix a :: ivl and v :: int
  assume pt: "ivl_is_point a" and mem: "v \<in> gamma a"
  from pt obtain w where a: "a = Ivl (Fin w) (Fin w)" unfolding ivl_is_point_def by blast
  from mem a have "v = w" by simp
  thus "ivl_decode v = a" using a by (simp add: ivl_decode_def)
qed

text \<open>The point abstraction is exact on its own image: a decoded value concretises
  to exactly that value, and re-decodes to itself.\<close>

lemma ivl_decode_gamma: "gamma_ivl (ivl_decode v) = {v}"
  unfolding ivl_decode_def by (rule gamma_ivl_point)

lemma ivl_is_point_decode: "ivl_is_point (ivl_decode v)"
  by (simp add: ivl_is_point_def ivl_decode_def)

end
