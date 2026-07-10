theory Exec_Ivl_Seed_EnterMono
  imports Exec_Ivl_Cmp_Seed_Clean_Run Seed_EnterMono_Lift
begin

section \<open>Interval ENTER_MONO: the seeded-clean run instantiates point-digest routing\<close>

text \<open>
  The interval sibling of \<open>Exec_Sign_Seed_EnterMono\<close>: the last obligation of the
  seeded-clean kernel \<open>clean_ctx_collect_rread\<close> --- \<open>ENTER_MONO\<close> (Goblint
  \<open>Spec.context\<close>) --- is discharged for the interval run by interpreting the
  domain-generic \<^locale>\<open>point_digest\<close> capability
  (\<^theory>\<open>Voblint_Formalization.Seed_EnterMono_Lift\<close>).

  The interval routing digest is the point abstraction \<open>ivl_of_int n = [n, n]\<close>; the
  context selector reads the caller \<^emph>\<open>local\<close> (\<^const>\<open>ivl_ec\<close>, R_read).  At each call
  site the routing slot on \<open>G\<close> is a \<^emph>\<open>point\<close> interval (\<open>[0,0]\<close> at site 4, \<open>[10,10]\<close>
  at site 7, \<open>iseed_caller_locals_points\<close>), so \<open>ivl_of_int\<close> is constant over its
  concretisation and the ENTER_MONO routing equation holds.
\<close>

subsection \<open>The interval point abstraction and its gamma-exactness\<close>

text \<open>\<open>ivl_of_int n = [n, n]\<close>: the point interval abstracting a single integer.
  Matches the numeral abstraction \<^const>\<open>aval_ivl_hol\<close> uses for \<open>N n\<close>.\<close>

definition ivl_of_int :: "Int.int \<Rightarrow> ivl" where
  "ivl_of_int n = Ivl (Fin n) (Fin n)"

text \<open>A point interval: gamma is a singleton, so \<^const>\<open>ivl_of_int\<close> is constant on it.
  The joins (proper ranges) are not points --- their concretisation spans several
  \<^const>\<open>ivl_of_int\<close> classes (\<open>non_point_ivl_splits\<close>).\<close>

definition point_ivl :: "ivl \<Rightarrow> bool" where
  "point_ivl a = (\<exists>k. a = Ivl (Fin k) (Fin k))"

lemma point_ivl_gamma_exact:
  assumes "point_ivl a" and "v \<in> gamma_ivl a"
  shows "ivl_of_int v = a"
  using assms unfolding point_ivl_def ivl_of_int_def by auto

text \<open>Sharpness: a non-point interval (\<open>[0,10]\<close>) admits two stores of distinct digest,
  so the routing equation cannot hold for both --- ENTER_MONO is false at a non-point
  slot.  This is the interval form of the obstruction the Obs read reintroduces (its
  \<open>local \<squnion> keyed\<close> join widens a shared-context global to a proper range).\<close>

lemma non_point_ivl_splits:
  "0 \<in> gamma_ivl (Ivl (Fin 0) (Fin 10)) \<and> 10 \<in> gamma_ivl (Ivl (Fin 0) (Fin 10))
   \<and> ivl_of_int 0 \<noteq> ivl_of_int 10 \<and> \<not> point_ivl (Ivl (Fin 0) (Fin 10))"
  by (simp add: point_ivl_def ivl_of_int_def)

subsection \<open>Interval interprets the point-digest capability\<close>

text \<open>The interval domain discharges the single \<open>point_exact\<close> assumption via
  \<open>point_ivl_gamma_exact\<close> (\<open>gamma = gamma_ivl\<close> on the interval sound-domain
  instance), inheriting \<open>point_digest.enter_mono_point\<close>.\<close>

interpretation ivl_pd: point_digest ivl_of_int point_ivl
  by unfold_locales (simp add: point_ivl_gamma_exact)

subsection \<open>The run's routing slots are points\<close>

text \<open>The abstract post-solution of the executable interval seeded-clean run, read
  through \<^const>\<open>fun_of_st\<close>.\<close>

definition iseed_sg :: "(pp \<times> ivl st) + ivl st \<Rightarrow> ivl abs_state" where
  "iseed_sg = (\<lambda>k. fun_of_st (snd iseed_clean_solution k))"

lemma iseed_slots_G:
  "iseed_sg (Inl (4, bot)) ''G'' = Ivl (Fin 0) (Fin 0)
   \<and> iseed_sg (Inl (7, bot)) ''G'' = Ivl (Fin 10) (Fin 10)"
  using iseed_caller_locals_points by (simp add: iseed_sg_def)

lemma iseed_slots_point:
  "point_ivl (iseed_sg (Inl (4, bot)) ''G'')"
  "point_ivl (iseed_sg (Inl (7, bot)) ''G'')"
  using iseed_slots_G by (simp_all add: point_ivl_def)

subsection \<open>ENTER_MONO at the run's call sites, as a theorem\<close>

text \<open>
  \<^bold>\<open>ENTER_MONO holds at the run's routing slots.\<close>  Every store admitted by a
  call-site caller slot routes, under \<^const>\<open>ivl_of_int\<close>, to that slot's own point
  interval --- the value-keyed \<open>Spec.context\<close> distinguishes the two calls where a
  monovariant (or Obs) read would merge them.  Discharged by the inherited
  \<open>point_digest.enter_mono_point\<close> plus the eval-checked point slots.
\<close>

theorem iseed_enter_mono_call_sites:
  assumes "s \<in> \<lbrakk>iseed_sg (Inl (4, bot))\<rbrakk>"
  shows "ivl_of_int (s ''G'') = iseed_sg (Inl (4, bot)) ''G''"
  by (rule ivl_pd.enter_mono_point[where sg = iseed_sg and cl = 4 and ctx = bot and proj_var = "''G''",
        OF iseed_slots_point(1) assms])

theorem iseed_enter_mono_call_sites':
  assumes "s \<in> \<lbrakk>iseed_sg (Inl (7, bot))\<rbrakk>"
  shows "ivl_of_int (s ''G'') = iseed_sg (Inl (7, bot)) ''G''"
  by (rule ivl_pd.enter_mono_point[where sg = iseed_sg and cl = 7 and ctx = bot and proj_var = "''G''",
        OF iseed_slots_point(2) assms])

text \<open>
  \<^bold>\<open>Verdict.\<close>  The interval seeded-clean run instantiates the same point-digest
  routing capability as Sign.  ENTER_MONO is not provable unconditionally
  (\<open>non_point_ivl_splits\<close> exhibits the failure at a proper range), but factors into:
  the domain-generic \<^locale>\<open>point_digest\<close> locale (one inherited lemma,
  \<open>point_digest.enter_mono_point\<close>); the interval gamma-exactness
  \<open>point_ivl_gamma_exact\<close> discharging its single assumption; and the run-specific,
  eval-checked \<^emph>\<open>point-routing\<close> premise \<open>iseed_slots_point\<close> --- the seeded-clean
  generator keeps each call-site routing slot a point.  With this, all obligations of
  \<open>ivl_clean_ctx_collect_rread\<close> are met on the interval seeded-clean spine, and
  the eval witnesses of \<^theory>\<open>Voblint_Formalization.Exec_Ivl_Cmp_Seed_Clean_Run\<close>
  (\<open>iseed_contexts_separate\<close> et al.) are complemented by a theorem-level routing
  equation.
\<close>

end
