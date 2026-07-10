theory Exec_Sign_Seed_EnterMono
  imports Exec_Sign_Cmp_Seed_Sound Seed_EnterMono_Lift
begin

section \<open>B3: ENTER_MONO over R_read reduces to slot gamma-exactness\<close>

text \<open>
  The last open obligation of the seeded-clean kernel \<open>clean_ctx_collect_rread\<close>
  (\<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>) is \<open>ENTER_MONO\<close> --- the value-digest
  routing (Goblint \<open>Spec.context\<close>):

    \<open>s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk> \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))\<close>

  For the value-keyed digest \<open>entdg s = decode_conc (s proj_var)\<close>,
  \<open>rt cl ctx L = decode_abs (L proj_var)\<close>, \<open>cmp = (=)\<close>, so at a routing slot
  \<open>L = sg (Inl (cl, ctx))\<close> the obligation is the pointwise equation

    \<open>s \<in> \<lbrakk>L\<rbrakk> \<Longrightarrow> decode_conc (s proj_var) = decode_abs (L proj_var)\<close>.

  \<^bold>\<open>Why the Obs variant is false.\<close>  Over the Obs read \<open>side_env_cmp = local \<squnion> keyed\<close>
  two value-distinct activations sharing a context join in the keyed slot to a
  non-point (here \<^const>\<open>SNonNeg\<close> on \<open>G\<close>); its concretisation
  \<open>gamma_sign SNonNeg = {n. n \<ge> 0}\<close> admits both \<open>0\<close> and \<open>1\<close>, whose
  \<^const>\<open>sign_of_int\<close> digests differ, so no single routed context matches every
  admitted store (\<open>Keyed_Retain_EnterMono.enter_mono_read_not_point\<close>).

  \<^bold>\<open>What makes the R_read instance true.\<close>  Over the local read the seeded-clean
  routing slot's projection is a \<^emph>\<open>point\<close> (\<^const>\<open>SZero\<close> at the first call site,
  \<^const>\<open>SPos\<close> at the second): \<^const>\<open>sign_of_int\<close> is \<^emph>\<open>constant\<close> on the
  concretisation of a point sign and equals it, so the routing equation holds for
  every admitted store.  This is a \<^emph>\<open>precision\<close> (gamma-exactness) fact, not a
  soundness one: soundness gives only over-approximation, never that a slot's
  concretisation collapses to a single digest.

  This theory factors \<open>ENTER_MONO\<close> into a domain-generic \<^emph>\<open>lift\<close> (per-projection
  gamma-exactness \<open>\<Longrightarrow>\<close> the routing equation) and the run-specific gamma-exactness
  premise, which for the sign point signs is a proved domain lemma and for the
  concrete run is eval-checkable.
\<close>

subsection \<open>Domain lemma: the point signs are gamma-exact under \<^const>\<open>sign_of_int\<close>\<close>

text \<open>
  A sign is a \<^emph>\<open>point\<close> when \<^const>\<open>sign_of_int\<close> is constant on its concretisation
  and returns the sign itself --- exactly the atoms \<^const>\<open>SNeg\<close> / \<^const>\<open>SZero\<close> /
  \<^const>\<open>SPos\<close> and \<^const>\<open>SBot\<close> (vacuous).  The joins \<^const>\<open>SNonNeg\<close> /
  \<^const>\<open>SNonPos\<close> / \<^const>\<open>STop\<close> are \<^emph>\<open>not\<close> points: their concretisation spans
  several \<^const>\<open>sign_of_int\<close> classes.
\<close>

definition point_sign :: "sign \<Rightarrow> bool" where
  "point_sign a \<longleftrightarrow> a \<in> {SBot, SNeg, SZero, SPos}"

lemma point_sign_gamma_exact:
  assumes "point_sign a" and "v \<in> gamma_sign a"
  shows "sign_of_int v = a"
  using assms unfolding point_sign_def by (cases a) auto

text \<open>Sharpness: a non-point (\<^const>\<open>SNonNeg\<close>) admits two stores of distinct digest,
  so the routing equation cannot hold for both --- \<open>ENTER_MONO\<close> is false at a
  non-point slot.  This is the exact obstruction the Obs read reintroduces.\<close>

lemma non_point_sign_splits:
  "0 \<in> gamma_sign SNonNeg \<and> 1 \<in> gamma_sign SNonNeg
   \<and> sign_of_int 0 \<noteq> sign_of_int 1 \<and> \<not> point_sign SNonNeg"
  by (simp add: point_sign_def)

subsection \<open>Sign interprets the point-digest capability\<close>

text \<open>
  The domain-generic ENTER_MONO lift is the \<^locale>\<open>point_digest\<close> locale
  (\<^theory>\<open>Voblint_Formalization.Seed_EnterMono_Lift\<close>): it fixes a point abstraction
  \<open>decode\<close> and a point predicate \<open>is_point\<close>, bundles the single gamma-exactness
  assumption \<open>point_exact\<close>, and re-exports \<open>point_digest.enter_mono_point\<close>.
  Sign discharges the assumption via \<open>point_sign_gamma_exact\<close> (\<open>gamma = gamma_sign\<close>
  on the sign sound-domain instance), inheriting the ENTER_MONO point lemma with
  \<open>decode = sign_of_int\<close>.  Interval interprets the same locale in
  \<open>Exec_Ivl_Seed_EnterMono\<close>.
\<close>

interpretation sign_pd: point_digest sign_of_int point_sign
proof (unfold_locales)
  fix a v assume p: "point_sign a" and g: "v \<in> gamma a"
  from g have "v \<in> gamma_sign a" by simp
  from p this show "sign_of_int v = a" by (rule point_sign_gamma_exact)
qed

subsection \<open>Instantiation for the seeded-clean run\<close>

text \<open>
  The abstract post-solution of the executable seeded-clean run, read through
  \<^const>\<open>fun_of_st\<close>.  Its two call-site caller slots carry the \<^emph>\<open>points\<close>
  \<^const>\<open>SZero\<close> (pp 4) and \<^const>\<open>SPos\<close> (pp 7) on \<open>G\<close>
  (\<open>kgen_seed_clean_caller_locals\<close>), so the routing equation holds there.
\<close>

definition seed_sg :: "(pp \<times> sign st) + sign st \<Rightarrow> sign abs_state" where
  "seed_sg = (\<lambda>k. fun_of_st (snd kgen_seed_clean_solution k))"

lemma seed_slots_G:
  "seed_sg (Inl (4, bot)) ''G'' = SZero \<and> seed_sg (Inl (7, bot)) ''G'' = SPos"
  using kgen_seed_clean_caller_locals by (simp add: seed_sg_def)

lemma seed_slots_point:
  "point_sign (seed_sg (Inl (4, bot)) ''G'')"
  "point_sign (seed_sg (Inl (7, bot)) ''G'')"
  using seed_slots_G by (simp_all add: point_sign_def)

text \<open>
  \<^bold>\<open>ENTER_MONO holds at the run's routing slots, as a theorem.\<close>  Every store
  admitted by a call-site caller slot routes to that slot's own point context ---
  the value-keyed \<open>Spec.context\<close> distinguishes the two calls where the Obs read
  merged them.  This is the go/no-go result: the eval-true separation
  (\<open>kgen_seed_clean_precision\<close>) is now a proved routing equation, discharged by the
  domain-generic lift plus the point-sign gamma-exactness lemma.
\<close>

theorem seed_enter_mono_call_sites:
  assumes "s \<in> \<lbrakk>seed_sg (Inl (4, bot))\<rbrakk>"
  shows "sign_of_int (s ''G'') = seed_sg (Inl (4, bot)) ''G''"
  by (rule sign_pd.enter_mono_point[where sg = seed_sg and cl = 4 and ctx = bot and proj_var = "''G''",
        OF seed_slots_point(1) assms])

theorem seed_enter_mono_call_sites':
  assumes "s \<in> \<lbrakk>seed_sg (Inl (7, bot))\<rbrakk>"
  shows "sign_of_int (s ''G'') = seed_sg (Inl (7, bot)) ''G''"
  by (rule sign_pd.enter_mono_point[where sg = seed_sg and cl = 7 and ctx = bot and proj_var = "''G''",
        OF seed_slots_point(2) assms])

text \<open>
  \<^bold>\<open>Verdict (B3).\<close>  The eval-true R_read result lifts to a theorem.  \<open>ENTER_MONO\<close>
  is \<^emph>\<open>not\<close> provable unconditionally --- it requires the routing slot to be
  gamma-exact (a point), which soundness alone never gives (\<open>non_point_sign_splits\<close>
  exhibits the failure at \<^const>\<open>SNonNeg\<close>).  It \<^emph>\<open>is\<close> provable relative to that
  precision premise, which factors cleanly: the domain-generic \<^locale>\<open>point_digest\<close>
  locale (\<open>point_digest.enter_mono_point\<close>, reusable at any \<^class>\<open>sound_domain\<close>
  and any point digest), the sign domain lemma \<open>point_sign_gamma_exact\<close> discharging
  its assumption, and the eval-checkable slot
  premise \<open>seed_slots_point\<close> that the seeded-clean generator makes the call-site
  routing slots points.  The genuinely-required extra invariant is therefore
  \<^emph>\<open>point-routing\<close>: the seeded clean transfer keeps each call-site routing slot
  gamma-exact on the digest projection.  It holds for this run because the
  Goblint-faithful seed delivers the caller's precise per-context global into the
  callee-entry local and the clean transfer never rejoins the coarse published
  slot.
\<close>

end
