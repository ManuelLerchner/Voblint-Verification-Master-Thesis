theory Special_Ops
  imports "Voblint_Core.Transfer_Interface"
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
    and ev  :: "exp => (vname => 'a) => 'a"
  assumes special_min_sound_for[intro]:
    "\<forall>i j p q. i \<in> gamma p \<longrightarrow> j \<in> gamma q \<longrightarrow> min i j \<in> gamma (special_min ops p q)"
  assumes special_max_sound_for[intro]:
    "\<forall>i j p q. i \<in> gamma p \<longrightarrow> j \<in> gamma q \<longrightarrow> max i j \<in> gamma (special_max ops p q)"
  assumes special_min_mono_for[intro]:
    "\<forall>p1 p2 q1 q2. p1 \<le> p2 \<longrightarrow> q1 \<le> q2 \<longrightarrow> special_min ops p1 q1 \<le> special_min ops p2 q2"
  assumes special_max_mono_for[intro]:
    "\<forall>p1 p2 q1 q2. p1 \<le> p2 \<longrightarrow> q1 \<le> q2 \<longrightarrow> special_max ops p1 q1 \<le> special_max ops p2 q2"
  assumes ev_sound_for[intro]:
    "\<forall>(e::exp) s \<sigma>. (\<forall>x. s x \<in> gamma (\<sigma> x)) \<longrightarrow> aval e s \<in> gamma (ev e \<sigma>)"
  assumes ev_mono_for[intro]:
    "\<forall>(e::exp) \<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<longrightarrow> ev e \<sigma>1 \<le> ev e \<sigma>2"
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
  "(\<forall>x. s x \<in> gamma (\<sigma> x)) \<Longrightarrow> aval e s \<in> gamma (ev e \<sigma>)"
  using ev_sound_for by blast

lemma ev_monoD:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> ev e \<sigma>1 \<le> ev e \<sigma>2"
  using ev_mono_for by blast

definition special_transfer ::
    "special_call => vname => (vname => 'a) => (vname => 'a)"
where
  "special_transfer sc x \<sigma> =
     \<sigma>(x := (case sc of
                Nondet_Int => top
              | Min a b => special_min ops (ev a \<sigma>) (ev b \<sigma>)
              | Max a b => special_max ops (ev a \<sigma>) (ev b \<sigma>)))"

lemma special_transfer_Nondet_Int [simp]:
  "special_transfer Nondet_Int x \<sigma> = \<sigma>(x := top)"
  unfolding special_transfer_def by simp

lemma special_transfer_Min [simp]:
  "special_transfer (Min a b) x \<sigma> = \<sigma>(x := special_min ops (ev a \<sigma>) (ev b \<sigma>))"
  unfolding special_transfer_def by simp

lemma special_transfer_Max [simp]:
  "special_transfer (Max a b) x \<sigma> = \<sigma>(x := special_max ops (ev a \<sigma>) (ev b \<sigma>))"
  unfolding special_transfer_def by simp

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
      case Nondet_Int
      with True show ?thesis by (simp add: gamma_top)
    next
      case (Min a b)
      with sr True have "v = min (aval a s) (aval b s)" by simp
      moreover from V have "aval a s \<in> gamma (ev a \<sigma>)" and "aval b s \<in> gamma (ev b \<sigma>)"
        using ev_soundD by blast+
      ultimately show ?thesis using Min True by (simp add: special_min_soundD)
    next
      case (Max a b)
      with sr True have "v = max (aval a s) (aval b s)" by simp
      moreover from V have "aval a s \<in> gamma (ev a \<sigma>)" and "aval b s \<in> gamma (ev b \<sigma>)"
        using ev_soundD by blast+
      ultimately show ?thesis using Max True by (simp add: special_max_soundD)
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
  case Nondet_Int
  with le show ?thesis by (simp add: le_funD le_funI)
next
  case (Min a b)
  have "special_min ops (ev a sigma1) (ev b sigma1)
          \<le> special_min ops (ev a sigma2) (ev b sigma2)"
    using le by (intro special_min_monoD ev_monoD)
  with le Min show ?thesis unfolding le_fun_def by auto
next
  case (Max a b)
  have "special_max ops (ev a sigma1) (ev b sigma1)
          \<le> special_max ops (ev a sigma2) (ev b sigma2)"
    using le by (intro special_max_monoD ev_monoD)
  with le Max show ?thesis unfolding le_fun_def by auto
qed

end

end
