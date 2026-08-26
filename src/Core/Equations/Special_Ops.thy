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
    and ev  :: "texp => (vname => 'a) => 'a"
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
    "\<forall>(e::texp) s \<sigma>. (\<forall>x. s x \<in> gamma (\<sigma> x)) \<longrightarrow> teval e s \<in> gamma (ev e \<sigma>)"
  assumes ev_mono_for[intro]:
    "\<forall>(e::texp) \<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<longrightarrow> ev e \<sigma>1 \<le> ev e \<sigma>2"
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
  "(\<forall>x. s x \<in> gamma (\<sigma> x)) \<Longrightarrow> teval e s \<in> gamma (ev e \<sigma>)"
  using ev_sound_for by blast

lemma ev_monoD:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> ev e \<sigma>1 \<le> ev e \<sigma>2"
  using ev_mono_for by blast

text \<open>
  \<open>special_transfer\<close> evaluates \<open>Min\<close>/\<open>Max\<close>'s two operands -- already elaborated
  at the one kind the comparison relates them at -- and casts the \<open>min\<close>/\<open>max\<close>
  result to the destination kind the classified call carries, exactly where
  \<^const>\<open>special_result\<close> applies its own \<^const>\<open>ik_norm\<close>.
\<close>
definition special_transfer ::
    "special_call => vname => (vname => 'a) => (vname => 'a)"
where
  "special_transfer sc x \<sigma> =
     \<sigma>(x := (case sc of
                Nondet_Int k => cast k top
              | Min k a b => cast k (special_min ops (ev a \<sigma>) (ev b \<sigma>))
              | Max k a b => cast k (special_max ops (ev a \<sigma>) (ev b \<sigma>))))"

lemma special_transfer_Nondet_Int [simp]:
  "special_transfer (Nondet_Int k) x \<sigma> = \<sigma>(x := cast k top)"
  unfolding special_transfer_def by simp

lemma special_transfer_Min [simp]:
  "special_transfer (Min k a b) x \<sigma> =
     \<sigma>(x := cast k (special_min ops (ev a \<sigma>) (ev b \<sigma>)))"
  unfolding special_transfer_def by simp

lemma special_transfer_Max [simp]:
  "special_transfer (Max k a b) x \<sigma> =
     \<sigma>(x := cast k (special_max ops (ev a \<sigma>) (ev b \<sigma>)))"
  unfolding special_transfer_def by simp

lemma cast_soundD:
  "v \<in> gamma a \<Longrightarrow> ik_norm ik v \<in> gamma (cast ik a)"
  using cast_sound_for by blast

lemma cast_monoD:
  "a1 \<le> a2 \<Longrightarrow> cast ik a1 \<le> cast ik a2"
  using cast_mono_for by blast

lemma special_transfer_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and sr: "special_result sc s v"
  shows "s(x := v) \<in> \<lbrakk>special_transfer sc x \<sigma>\<rbrakk>"
  unfolding gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "(s(x := v)) y \<in> gamma ((special_transfer sc x \<sigma>) y)"
  proof (cases "y = x")
    case True
    from sr show ?thesis
    proof (cases sc)
      case (Nondet_Int k)
      then have "v \<in> ik_range k" using sr by simp
      then have "ik_norm k v = v" by (rule ik_norm_id)
      moreover have "ik_norm k v \<in> gamma (cast k (top :: 'a))"
        using cast_sound_for gamma_top by blast
      ultimately show ?thesis using Nondet_Int True by simp
    next
      case (Min k a b)
      from sr Min have veq: "v = ik_norm k (min (teval a s) (teval b s))" by simp
      from V have "teval a s \<in> gamma (ev a \<sigma>)" and "teval b s \<in> gamma (ev b \<sigma>)"
        using ev_soundD by blast+
      then have "min (teval a s) (teval b s) \<in> gamma (special_min ops (ev a \<sigma>) (ev b \<sigma>))"
        by (simp add: special_min_soundD)
      then have "ik_norm k (min (teval a s) (teval b s))
                   \<in> gamma (cast k (special_min ops (ev a \<sigma>) (ev b \<sigma>)))"
        by (rule cast_soundD)
      then show ?thesis using Min True veq by simp
    next
      case (Max k a b)
      from sr Max have veq: "v = ik_norm k (max (teval a s) (teval b s))" by simp
      from V have "teval a s \<in> gamma (ev a \<sigma>)" and "teval b s \<in> gamma (ev b \<sigma>)"
        using ev_soundD by blast+
      then have "max (teval a s) (teval b s) \<in> gamma (special_max ops (ev a \<sigma>) (ev b \<sigma>))"
        by (simp add: special_max_soundD)
      then have "ik_norm k (max (teval a s) (teval b s))
                   \<in> gamma (cast k (special_max ops (ev a \<sigma>) (ev b \<sigma>)))"
        by (rule cast_soundD)
      then show ?thesis using Max True veq by simp
    qed
  next
    case False
    with V show ?thesis by (cases sc) simp_all
  qed
qed

lemma special_transfer_mono:
  assumes le: "sigma1 \<le> sigma2"
  shows "special_transfer sc x sigma1 \<le> special_transfer sc x sigma2"
proof (cases sc)
  case (Nondet_Int k)
  with le show ?thesis by (simp add: le_funD le_funI)
next
  case (Min k a b)
  have "special_min ops (ev a sigma1) (ev b sigma1)
          \<le> special_min ops (ev a sigma2) (ev b sigma2)"
    using le by (intro special_min_monoD ev_monoD)
  then have "cast k (special_min ops (ev a sigma1) (ev b sigma1))
          \<le> cast k (special_min ops (ev a sigma2) (ev b sigma2))"
    by (rule cast_monoD)
  with le Min show ?thesis unfolding le_fun_def by auto
next
  case (Max k a b)
  have "special_max ops (ev a sigma1) (ev b sigma1)
          \<le> special_max ops (ev a sigma2) (ev b sigma2)"
    using le by (intro special_max_monoD ev_monoD)
  then have "cast k (special_max ops (ev a sigma1) (ev b sigma1))
          \<le> cast k (special_max ops (ev a sigma2) (ev b sigma2))"
    by (rule cast_monoD)
  with le Max show ?thesis unfolding le_fun_def by auto
qed

end

end
