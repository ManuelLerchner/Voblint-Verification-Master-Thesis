theory Special_Ops
  imports Constraint_System
begin

section \<open>Generic special-call dispatch\<close>

text \<open>
  Every domain's \<open>Nondet_Int\<close>/\<open>Min\<close>/\<open>Max\<close> dispatch (\<open>special_sign\<close>,
  \<open>special_ivl\<close>, \<open>special_parity\<close>, ...) has the same shape: havoc to \<open>top\<close> for
  \<open>Nondet_Int\<close>, or apply a two-argument primitive to the evaluated operands for
  \<open>Min\<close>/\<open>Max\<close>. This theory proves that shape's soundness and monotonicity once,
  against an abstract pair of primitives (\<open>special_min\<close>/\<open>special_max\<close>) and an
  abstract expression evaluator, so each domain only has to supply its own
  \<open>X_min\<close>/\<open>X_max\<close> and their soundness/monotonicity facts -- the case-split
  dispatch and its proof are not repeated per domain.

  \<open>special_min\<close>/\<open>special_max\<close> are bundled as a record rather than as two bare
  locale parameters so a concrete instance (e.g. \<open>sign_special_ops\<close>) is a
  first-class value, not just a locale interpretation.
\<close>

record 'a special_ops =
  special_min :: "'a => 'a => 'a"
  special_max :: "'a => 'a => 'a"

locale sound_special_ops =
  fixes ops :: "'a::sound_domain special_ops"
    and ev  :: "tyenv => ikind => exp => (vname => 'a) => 'a"
    and cast :: "ikind => 'a => 'a"
  assumes special_min_sound_for[intro]:
    "\<forall>i j p q. i \<in> gamma p \<longrightarrow> j \<in> gamma q \<longrightarrow> min i j \<in> gamma (special_min ops p q)"
  assumes special_max_sound_for[intro]:
    "\<forall>i j p q. i \<in> gamma p \<longrightarrow> j \<in> gamma q \<longrightarrow> max i j \<in> gamma (special_max ops p q)"
  assumes special_min_mono_for[intro]:
    "\<forall>p1 p2 q1 q2. p1 \<le> p2 \<longrightarrow> q1 \<le> q2 \<longrightarrow> special_min ops p1 q1 \<le> special_min ops p2 q2"
  assumes special_max_mono_for[intro]:
    "\<forall>p1 p2 q1 q2. p1 \<le> p2 \<longrightarrow> q1 \<le> q2 \<longrightarrow> special_max ops p1 q1 \<le> special_max ops p2 q2"
  assumes ev_sound_for[intro]:
    "\<forall>G ik (e::exp) s \<sigma>. (\<forall>x. s x \<in> gamma (\<sigma> x)) \<longrightarrow> taval G ik e s \<in> gamma (ev G ik e \<sigma>)"
  assumes ev_mono_for[intro]:
    "\<forall>G ik (e::exp) \<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<longrightarrow> ev G ik e \<sigma>1 \<le> ev G ik e \<sigma>2"
  assumes cast_sound_for[intro]:
    "\<forall>ik v a. v \<in> gamma a \<longrightarrow> ik_norm ik v \<in> gamma (cast ik a)"
  assumes cast_mono_for[intro]:
    "\<forall>ik a1 a2. a1 \<le> a2 \<longrightarrow> cast ik a1 \<le> cast ik a2"
  assumes gamma_top:
    "gamma (top :: 'a) = UNIV"
begin

lemma special_min_soundD:
  "i \<in> gamma p \<Longrightarrow> j \<in> gamma q \<Longrightarrow> min i j \<in> gamma (special_min ops p q)"
  using special_min_sound_for by blast

lemma special_max_soundD:
  "i \<in> gamma p \<Longrightarrow> j \<in> gamma q \<Longrightarrow> max i j \<in> gamma (special_max ops p q)"
  using special_max_sound_for by blast

lemma special_min_monoD:
  "p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> special_min ops p1 q1 \<le> special_min ops p2 q2"
  using special_min_mono_for by blast

lemma special_max_monoD:
  "p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> special_max ops p1 q1 \<le> special_max ops p2 q2"
  using special_max_mono_for by blast

lemma ev_soundD:
  "(\<forall>x. s x \<in> gamma (\<sigma> x)) \<Longrightarrow> taval G ik e s \<in> gamma (ev G ik e \<sigma>)"
  using ev_sound_for by blast

lemma ev_monoD:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> ev G ik e \<sigma>1 \<le> ev G ik e \<sigma>2"
  using ev_mono_for by blast

text \<open>
  \<open>special_transfer\<close> evaluates \<open>Min\<close>/\<open>Max\<close>'s two operands at the same
  synthesized kind \<^const>\<open>special_result\<close> itself evaluates them at
  (\<open>opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))\<close>), then casts the \<open>min\<close>/\<open>max\<close> result
  to the destination \<open>x\<close>'s own declared kind -- the same double-cast shape
  \<open>EA_Assign\<close> uses, since \<open>special_result\<close>'s own value is not yet in
  \<open>\<Gamma> x\<close>'s range in general.
\<close>
definition special_transfer ::
    "tyenv => special_call => vname => (vname => 'a) => (vname => 'a)"
where
  "special_transfer \<Gamma> sc x \<sigma> =
     \<sigma>(x := (case sc of
                Nondet_Int => top
              | Min a b => (let k = opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))
                             in cast (\<Gamma> x) (special_min ops (ev \<Gamma> k a \<sigma>) (ev \<Gamma> k b \<sigma>)))
              | Max a b => (let k = opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))
                             in cast (\<Gamma> x) (special_max ops (ev \<Gamma> k a \<sigma>) (ev \<Gamma> k b \<sigma>)))))"

lemma special_transfer_Nondet_Int [simp]:
  "special_transfer \<Gamma> Nondet_Int x \<sigma> = \<sigma>(x := top)"
  unfolding special_transfer_def by simp

lemma special_transfer_Min [simp]:
  "special_transfer \<Gamma> (Min a b) x \<sigma> =
     \<sigma>(x := cast (\<Gamma> x) (special_min ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a \<sigma>)
                                        (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b \<sigma>)))"
  unfolding special_transfer_def by (simp add: Let_def)

lemma special_transfer_Max [simp]:
  "special_transfer \<Gamma> (Max a b) x \<sigma> =
     \<sigma>(x := cast (\<Gamma> x) (special_max ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a \<sigma>)
                                        (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b \<sigma>)))"
  unfolding special_transfer_def by (simp add: Let_def)

lemma cast_soundD:
  "v \<in> gamma a \<Longrightarrow> ik_norm ik v \<in> gamma (cast ik a)"
  using cast_sound_for by blast

lemma cast_monoD:
  "a1 \<le> a2 \<Longrightarrow> cast ik a1 \<le> cast ik a2"
  using cast_mono_for by blast

lemma special_transfer_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and sr: "special_result \<Gamma> sc s v"
  shows "s(x := ik_norm (\<Gamma> x) v) \<in> \<lbrakk>special_transfer \<Gamma> sc x \<sigma>\<rbrakk>"
  unfolding gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "(s(x := ik_norm (\<Gamma> x) v)) y \<in> gamma ((special_transfer \<Gamma> sc x \<sigma>) y)"
  proof (cases "y = x")
    case True
    from sr show ?thesis
    proof (cases sc)
      case Nondet_Int
      with True show ?thesis by (simp add: gamma_top)
    next
      case (Min a b)
      let ?k = "opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))"
      from sr Min have "v = min (taval \<Gamma> ?k a s) (taval \<Gamma> ?k b s)" by (simp add: Let_def)
      moreover from V have "taval \<Gamma> ?k a s \<in> gamma (ev \<Gamma> ?k a \<sigma>)"
        and "taval \<Gamma> ?k b s \<in> gamma (ev \<Gamma> ?k b \<sigma>)"
        using ev_soundD by blast+
      ultimately have "v \<in> gamma (special_min ops (ev \<Gamma> ?k a \<sigma>) (ev \<Gamma> ?k b \<sigma>))"
        by (simp add: special_min_soundD)
      then show ?thesis using Min True by (simp add: cast_soundD)
    next
      case (Max a b)
      let ?k = "opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))"
      from sr Max have "v = max (taval \<Gamma> ?k a s) (taval \<Gamma> ?k b s)" by (simp add: Let_def)
      moreover from V have "taval \<Gamma> ?k a s \<in> gamma (ev \<Gamma> ?k a \<sigma>)"
        and "taval \<Gamma> ?k b s \<in> gamma (ev \<Gamma> ?k b \<sigma>)"
        using ev_soundD by blast+
      ultimately have "v \<in> gamma (special_max ops (ev \<Gamma> ?k a \<sigma>) (ev \<Gamma> ?k b \<sigma>))"
        by (simp add: special_max_soundD)
      then show ?thesis using Max True by (simp add: cast_soundD)
    qed
  next
    case False
    with V show ?thesis by (cases sc) simp_all
  qed
qed

lemma special_transfer_mono:
  assumes le: "sigma1 \<le> sigma2"
  shows "special_transfer \<Gamma> sc x sigma1 \<le> special_transfer \<Gamma> sc x sigma2"
proof (cases sc)
  case Nondet_Int
  with le show ?thesis by (simp add: le_funD le_funI)
next
  case (Min a b)
  have "special_min ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma1)
                         (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma1)
          \<le> special_min ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma2)
                             (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma2)"
    using le by (intro special_min_monoD ev_monoD)
  then have "cast (\<Gamma> x) (special_min ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma1)
                                          (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma1))
          \<le> cast (\<Gamma> x) (special_min ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma2)
                                          (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma2))"
    by (rule cast_monoD)
  with le Min show ?thesis unfolding le_fun_def by auto
next
  case (Max a b)
  have "special_max ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma1)
                         (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma1)
          \<le> special_max ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma2)
                             (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma2)"
    using le by (intro special_max_monoD ev_monoD)
  then have "cast (\<Gamma> x) (special_max ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma1)
                                          (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma1))
          \<le> cast (\<Gamma> x) (special_max ops (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) a sigma2)
                                          (ev \<Gamma> (opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))) b sigma2))"
    by (rule cast_monoD)
  with le Max show ?thesis unfolding le_fun_def by auto
qed

end

end
