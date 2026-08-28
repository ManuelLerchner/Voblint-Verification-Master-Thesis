theory Abstract_Arithmetic
  imports Abstract_Domain "Voblint_VIMP.VIMP_Typing"
begin

section \<open>Generic typed expression soundness\<close>

text \<open>
  \<open>expression_domain_sound\<close> below takes \<open>cast\<close> as an explicit per-domain
  locale parameter: every domain implements its own precise, Goblint-faithful
  cast against its own concrete representation -- \<open>Interval\<close> wraps each bound
  via modular reduction with a width check, \<open>Congruence\<close> wraps its class
  through the wraparound modulus's \<open>gcd\<close>, \<open>Parity\<close> is the identity (its
  modulus, \<open>2\<close>, divides every wraparound modulus this project defines), and
  \<open>Sign\<close> is exact at \<open>SZero\<close> and sound at \<open>SNonNeg\<close> for an unsigned target
  (\<open>ik_norm\<close> for an unsigned kind always lands in \<open>[0, ik_max ik]\<close>) -- source-
  checked 2026-08-25 against \<open>intervalDomain.ml\<close>'s \<open>norm ~cast:true\<close> and
  \<open>congruenceDomain.ml\<close>'s \<open>cast_to\<close> for the two domains with a genuine
  concrete representation.
\<close>

text \<open>
  Sign, Interval, and Parity each prove an \<open>aval_<dom>_sound\<close> lemma with the
  identical shape and proof script: structural induction on \<open>texp\<close>,
  discharged by the same per-operator soundness facts. Arithmetic
  (\<open>plus_sound\<close>/\<open>minus_sound\<close>/\<open>times_sound\<close>) and comparison/truthiness
  (\<open>lt\<close>/\<open>eqb\<close>/\<open>tobool\<close>) are genuinely domain-specific -- each domain's own
  case-split proof over its own representation -- so this locale does not try
  to share those. What it shares is the one induction that combines them,
  mirroring Goblint's \<open>base.ml\<close> expression evaluator: \<open>Base\<close> only ever calls
  \<open>ID.add\<close>/\<open>ID.lt\<close>/\<open>ID.to_bool\<close> and never recomputes a comparison's
  precision itself, so \<open>ev\<close> here only ever calls \<open>lt\<close>/\<open>eqb\<close>/\<open>tobool\<close> and
  never recomputes what a domain already knows about its own relation.

  \<open>ev\<close> mirrors \<^const>\<open>teval\<close>'s own recursion exactly: it reads each
  node's kind off the node itself and norms every arithmetic node once
  through the domain's own \<open>cast\<close> (never at \<open>TLess\<close>/\<open>TEq\<close>/\<open>TNot\<close>/\<open>TAnd\<close>/
  \<open>TOr\<close>'s own 0/1 result, which \<^const>\<open>teval\<close> never norms either -- 0 and 1
  already fit every kind), and \<open>TCast\<close> is exactly one more \<open>cast\<close> at the
  target kind. \<open>lit\<close>,
  \<open>lt\<close>, \<open>eqb\<close>, \<open>tobool\<close>, and now \<open>cast\<close> stay locale parameters, not derived:
  interpreting this locale at a domain's own literal-embedding function,
  comparison/truthiness queries, and (Goblint-faithful where the domain has
  a concrete representation to wrap) cast keeps every existing call site
  untouched.
\<close>

text \<open>
  A comparison or logical result is always the concrete C truthiness value
  \<open>0\<close>/\<open>1\<close>. Abstractly that becomes \<open>Some True \<Rightarrow> lit 1\<close> (definitely true),
  \<open>Some False \<Rightarrow> lit 0\<close> (definitely false), \<open>None \<Rightarrow> lit 0 \<squnion> lit 1\<close> (unknown,
  soundly covering both) -- exactly Goblint's \<open>id_binary_pred\<close>/\<open>id_unary_log\<close>/
  \<open>id_binary_log\<close> pattern. \<open>TAnd\<close>/\<open>TOr\<close> additionally exploit the annihilator
  case (a definitely-false conjunct settles the whole conjunction, a
  definitely-true disjunct settles the whole disjunction) before falling
  back to the fully unknown join, mirroring \<open>id_binary_log\<close>'s own
  short-circuit.

  Each operand is queried through \<open>lt\<close>/\<open>eqb\<close>/\<open>tobool\<close> only when it is not
  itself \<open>is_bot\<close>: an \<open>is_bot\<close> operand denotes an unreachable value (its
  concretization is empty), so the whole comparison collapses to \<open>bot\<close>
  rather than querying a value with no witness to reason about. This guard
  is not optional bookkeeping -- \<open>bot\<close> is every domain's own least element,
  so a comparison against it can widen to conflicting query answers as the
  \<^emph>\<open>other\<close> operand widens; routing it through \<open>bot\<close> directly, before
  \<open>lt\<close>/\<open>eqb\<close>/\<open>tobool\<close> ever see it, is what keeps \<open>aval_dom_mono\<close> provable
  without demanding an impossible monotonicity obligation from those queries
  at their own domain's bottom.
\<close>

locale expression_domain_sound =
  fixes ev :: "texp \<Rightarrow> (vname \<Rightarrow> 'a::{sound_domain,plus,minus,times}) \<Rightarrow> 'a"
    and cast :: "ikind \<Rightarrow> 'a \<Rightarrow> 'a"
    and lit :: "int \<Rightarrow> 'a"
    and lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and eqb :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and tobool :: "'a \<Rightarrow> bool option"
  assumes ev_N[simp]: "ev (TN ik n) sigma = lit (ik_norm ik n)"
    and ev_V[simp]: "ev (TVar ik x) sigma = sigma x"
    and ev_Plus[simp]: "ev (TPlus ik e1 e2) sigma =
         cast ik (ev e1 sigma + ev e2 sigma)"
    and ev_Minus[simp]: "ev (TMinus ik e1 e2) sigma =
         cast ik (ev e1 sigma - ev e2 sigma)"
    and ev_Times[simp]: "ev (TTimes ik e1 e2) sigma =
         cast ik (ev e1 sigma * ev e2 sigma)"
    and ev_Cast[simp]: "ev (TCast ik e) sigma = cast ik (ev e sigma)"
    and ev_Less[simp]: "ev (TLess e1 e2) sigma =
         (if is_bot (ev e1 sigma) \<or> is_bot (ev e2 sigma) then bot
          else if lt (ev e1 sigma) (ev e2 sigma) = Some True then lit 1
          else if lt (ev e1 sigma) (ev e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Eq[simp]: "ev (TEq e1 e2) sigma =
         (if is_bot (ev e1 sigma) \<or> is_bot (ev e2 sigma) then bot
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some True then lit 1
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Not[simp]: "ev (TNot e) sigma =
         (if is_bot (ev e sigma) then bot
          else if tobool (ev e sigma) = Some True then lit 0
          else if tobool (ev e sigma) = Some False then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_And[simp]: "ev (TAnd e1 e2) sigma =
         (if is_bot (ev e1 sigma) \<or> is_bot (ev e2 sigma) then bot
          else if tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False
          then lit 0
          else if tobool (ev e1 sigma) = Some True \<and> tobool (ev e2 sigma) = Some True
          then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_Or[simp]: "ev (TOr e1 e2) sigma =
         (if is_bot (ev e1 sigma) \<or> is_bot (ev e2 sigma) then bot
          else if tobool (ev e1 sigma) = Some True \<or> tobool (ev e2 sigma) = Some True
          then lit 1
          else if tobool (ev e1 sigma) = Some False \<and> tobool (ev e2 sigma) = Some False
          then lit 0
          else lit 0 \<squnion> lit 1)"
    and lit_sound[simp]: "n \<in> gamma (lit n)"
    and plus_sound[intro]: "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i + j \<in> gamma (p + q)"
    and minus_sound[intro]: "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i - j \<in> gamma (p - q)"
    and times_sound[intro]: "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i * j \<in> gamma (p * q)"
    and plus_mono[intro]: "p1 \<le> (p2::'a) \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> p1 + q1 \<le> p2 + q2"
    and minus_mono[intro]: "p1 \<le> (p2::'a) \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> p1 - q1 \<le> p2 - q2"
    and times_mono[intro]: "p1 \<le> (p2::'a) \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> p1 * q1 \<le> p2 * q2"
    and lt_sound: "lt p q = Some b \<Longrightarrow> i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> (i < j) = b"
    and eqb_sound: "eqb p q = Some b \<Longrightarrow> i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> (i = j) = b"
    and tobool_sound: "tobool p = Some b \<Longrightarrow> i \<in> gamma (p::'a) \<Longrightarrow> truthy i = b"
    and lt_mono:
      "\<not> is_bot (p1::'a) \<Longrightarrow> \<not> is_bot q1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow>
       lt p2 q2 = Some b \<Longrightarrow> lt p1 q1 = Some b"
    and eqb_mono:
      "\<not> is_bot (p1::'a) \<Longrightarrow> \<not> is_bot q1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow>
       eqb p2 q2 = Some b \<Longrightarrow> eqb p1 q1 = Some b"
    and tobool_mono:
      "\<not> is_bot (p1::'a) \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some b \<Longrightarrow> tobool p1 = Some b"
    and gamma_top: "gamma (top :: 'a) = UNIV"
    and cast_sound: "(v::int) \<in> gamma (a::'a) \<Longrightarrow> ik_norm ik v \<in> gamma (cast ik a)"
    and cast_mono: "a1 \<le> (a2::'a) \<Longrightarrow> cast ik a1 \<le> cast ik a2"
begin

lemma aval_dom_sound:
  "(\<forall>x. s x \<in> gamma (sigma x)) \<Longrightarrow> teval a s \<in> gamma (ev a sigma)"
proof (induction a arbitrary: s sigma)
  case (TN ik n) then show ?case by simp
next
  case (TVar ik x) then show ?case by (simp add: cast_sound)
next
  case (TPlus ik e1 e2)
  have h1: "teval e1 s \<in> gamma (ev e1 sigma)" using TPlus.IH(1) TPlus.prems by simp
  have h2: "teval e2 s \<in> gamma (ev e2 sigma)" using TPlus.IH(2) TPlus.prems by simp
  show ?case using cast_sound[OF plus_sound[OF h1 h2]] by simp
next
  case (TMinus ik e1 e2)
  have h1: "teval e1 s \<in> gamma (ev e1 sigma)" using TMinus.IH(1) TMinus.prems by simp
  have h2: "teval e2 s \<in> gamma (ev e2 sigma)" using TMinus.IH(2) TMinus.prems by simp
  show ?case using cast_sound[OF minus_sound[OF h1 h2]] by simp
next
  case (TTimes ik e1 e2)
  have h1: "teval e1 s \<in> gamma (ev e1 sigma)" using TTimes.IH(1) TTimes.prems by simp
  have h2: "teval e2 s \<in> gamma (ev e2 sigma)" using TTimes.IH(2) TTimes.prems by simp
  show ?case using cast_sound[OF times_sound[OF h1 h2]] by simp
next
  case (TCast ik e)
  have h: "teval e s \<in> gamma (ev e sigma)" using TCast.IH TCast.prems by simp
  show ?case using cast_sound[OF h] by simp
next
  case (TLess e1 e2)
  have h1: "teval e1 s \<in> gamma (ev e1 sigma)" using TLess.IH(1) TLess.prems by simp
  have h2: "teval e2 s \<in> gamma (ev e2 sigma)" using TLess.IH(2) TLess.prems by simp
  have nb1: "\<not> is_bot (ev e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "lt (ev e1 sigma) (ev e2 sigma) = Some True")
    case True
    with lt_sound[OF True h1 h2] nb1 nb2 show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "lt (ev e1 sigma) (ev e2 sigma) = Some False")
      case True
      with lt_sound[OF True h1 h2] nb1 nb2 False show ?thesis by simp
    next
      case False
      with \<open>\<not> (lt (ev e1 sigma) (ev e2 sigma) = Some True)\<close> nb1 nb2
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (TEq e1 e2)
  have h1: "teval e1 s \<in> gamma (ev e1 sigma)" using TEq.IH(1) TEq.prems by simp
  have h2: "teval e2 s \<in> gamma (ev e2 sigma)" using TEq.IH(2) TEq.prems by simp
  have nb1: "\<not> is_bot (ev e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "eqb (ev e1 sigma) (ev e2 sigma) = Some True")
    case True
    with eqb_sound[OF True h1 h2] nb1 nb2 show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "eqb (ev e1 sigma) (ev e2 sigma) = Some False")
      case True
      with eqb_sound[OF True h1 h2] nb1 nb2 False show ?thesis by simp
    next
      case False
      with \<open>\<not> (eqb (ev e1 sigma) (ev e2 sigma) = Some True)\<close> nb1 nb2
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (TNot e)
  have h: "teval e s \<in> gamma (ev e sigma)" using TNot.IH TNot.prems by simp
  have nb: "\<not> is_bot (ev e sigma)" using h is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev e sigma) = Some True")
    case True
    with tobool_sound[OF True h] nb show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "tobool (ev e sigma) = Some False")
      case True
      with tobool_sound[OF True h] nb False show ?thesis by simp
    next
      case False
      with \<open>\<not> (tobool (ev e sigma) = Some True)\<close> nb
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (TAnd e1 e2)
  have h1: "teval e1 s \<in> gamma (ev e1 sigma)" using TAnd.IH(1) TAnd.prems by simp
  have h2: "teval e2 s \<in> gamma (ev e2 sigma)" using TAnd.IH(2) TAnd.prems by simp
  have nb1: "\<not> is_bot (ev e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False")
    case True
    then have "\<not> truthy (teval e1 s) \<or> \<not> truthy (teval e2 s)"
      using tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by auto
  next
    case False
    show ?thesis
    proof (cases "tobool (ev e1 sigma) = Some True \<and> tobool (ev e2 sigma) = Some True")
      case True
      then have "truthy (teval e1 s) \<and> truthy (teval e2 s)"
        using tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by simp
    next
      case False
      with \<open>\<not> (tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False)\<close>
        nb1 nb2
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (TOr e1 e2)
  have h1: "teval e1 s \<in> gamma (ev e1 sigma)" using TOr.IH(1) TOr.prems by simp
  have h2: "teval e2 s \<in> gamma (ev e2 sigma)" using TOr.IH(2) TOr.prems by simp
  have nb1: "\<not> is_bot (ev e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev e1 sigma) = Some True \<or> tobool (ev e2 sigma) = Some True")
    case True
    then have "truthy (teval e1 s) \<or> truthy (teval e2 s)"
      using tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by auto
  next
    case False
    show ?thesis
    proof (cases "tobool (ev e1 sigma) = Some False \<and> tobool (ev e2 sigma) = Some False")
      case True
      then have "\<not> truthy (teval e1 s) \<and> \<not> truthy (teval e2 s)"
        using tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by simp
    next
      case False
      with \<open>\<not> (tobool (ev e1 sigma) = Some True \<or> tobool (ev e2 sigma) = Some True)\<close>
        nb1 nb2
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
qed

lemma aval_dom_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> ev a sigma1 \<le> ev a sigma2"
proof (induction a arbitrary: sigma1 sigma2)
  case (TN ik n) then show ?case by simp
next
  case (TVar ik x) then show ?case by (simp add: cast_mono le_funD)
next
  case (TPlus ik e1 e2)
  have "ev e1 sigma1 \<le> ev e1 sigma2" using TPlus.IH(1) TPlus.prems by simp
  moreover have "ev e2 sigma1 \<le> ev e2 sigma2" using TPlus.IH(2) TPlus.prems by simp
  ultimately show ?case using plus_mono by (simp add: cast_mono)
next
  case (TMinus ik e1 e2)
  have "ev e1 sigma1 \<le> ev e1 sigma2" using TMinus.IH(1) TMinus.prems by simp
  moreover have "ev e2 sigma1 \<le> ev e2 sigma2" using TMinus.IH(2) TMinus.prems by simp
  ultimately show ?case using minus_mono by (simp add: cast_mono)
next
  case (TTimes ik e1 e2)
  have "ev e1 sigma1 \<le> ev e1 sigma2" using TTimes.IH(1) TTimes.prems by simp
  moreover have "ev e2 sigma1 \<le> ev e2 sigma2" using TTimes.IH(2) TTimes.prems by simp
  ultimately show ?case using times_mono by (simp add: cast_mono)
next
  case (TCast ik e)
  have "ev e sigma1 \<le> ev e sigma2" using TCast.IH TCast.prems by simp
  then show ?case by (simp add: cast_mono)
next
  case (TLess e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using TLess.IH(1) TLess.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using TLess.IH(2) TLess.prems by simp
  show ?case
  proof (cases "is_bot (ev e1 sigma1) \<or> is_bot (ev e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_bot (ev e1 sigma1)" and nb2: "\<not> is_bot (ev e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "lt (ev e1 sigma2) (ev e2 sigma2)")
      case (Some b)
      then have "lt (ev e1 sigma1) (ev e2 sigma1) = Some b"
        using lt_mono[OF nb1 nb2 p_mono q_mono] by simp
      then show ?thesis using Some nb1 nb2 nb1' nb2' by (cases b) simp_all
    next
      case None
      then show ?thesis using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        by (cases "lt (ev e1 sigma1) (ev e2 sigma1) = Some True";
            cases "lt (ev e1 sigma1) (ev e2 sigma1) = Some False") auto
    qed
  qed
next
  case (TEq e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using TEq.IH(1) TEq.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using TEq.IH(2) TEq.prems by simp
  show ?case
  proof (cases "is_bot (ev e1 sigma1) \<or> is_bot (ev e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_bot (ev e1 sigma1)" and nb2: "\<not> is_bot (ev e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "eqb (ev e1 sigma2) (ev e2 sigma2)")
      case (Some b)
      then have "eqb (ev e1 sigma1) (ev e2 sigma1) = Some b"
        using eqb_mono[OF nb1 nb2 p_mono q_mono] by simp
      then show ?thesis using Some nb1 nb2 nb1' nb2' by (cases b) simp_all
    next
      case None
      then show ?thesis using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        by (cases "eqb (ev e1 sigma1) (ev e2 sigma1) = Some True";
            cases "eqb (ev e1 sigma1) (ev e2 sigma1) = Some False") auto
    qed
  qed
next
  case (TNot e)
  have p_mono: "ev e sigma1 \<le> ev e sigma2" using TNot.IH TNot.prems by simp
  show ?case
  proof (cases "is_bot (ev e sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb: "\<not> is_bot (ev e sigma1)" by auto
    have nb': "\<not> is_bot (ev e sigma2)" using nb p_mono is_bot_mono by blast
    show ?thesis
    proof (cases "tobool (ev e sigma2)")
      case (Some b)
      then have "tobool (ev e sigma1) = Some b" using tobool_mono[OF nb p_mono] by simp
      then show ?thesis using Some nb nb' by (cases b) simp_all
    next
      case None
      then show ?thesis using nb nb' sup_ge1 sup_ge2
        by (cases "tobool (ev e sigma1) = Some True";
            cases "tobool (ev e sigma1) = Some False") auto
    qed
  qed
next
  case (TAnd e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using TAnd.IH(1) TAnd.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using TAnd.IH(2) TAnd.prems by simp
  show ?case
  proof (cases "is_bot (ev e1 sigma1) \<or> is_bot (ev e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_bot (ev e1 sigma1)" and nb2: "\<not> is_bot (ev e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "tobool (ev e1 sigma2) = Some False \<or> tobool (ev e2 sigma2) = Some False")
      case True
      then have "tobool (ev e1 sigma1) = Some False \<or> tobool (ev e2 sigma1) = Some False"
        using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
      with True nb1 nb2 nb1' nb2' show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "tobool (ev e1 sigma2) = Some True \<and> tobool (ev e2 sigma2) = Some True")
        case True
        then have "tobool (ev e1 sigma1) = Some True" and "tobool (ev e2 sigma1) = Some True"
          using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by simp
      next
        case False
        with \<open>\<not> (tobool (ev e1 sigma2) = Some False \<or> tobool (ev e2 sigma2) = Some False)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "tobool (ev e1 sigma1) = Some False \<or> tobool (ev e2 sigma1) = Some False";
              cases "tobool (ev e1 sigma1) = Some True \<and> tobool (ev e2 sigma1) = Some True")
             auto
      qed
    qed
  qed
next
  case (TOr e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using TOr.IH(1) TOr.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using TOr.IH(2) TOr.prems by simp
  show ?case
  proof (cases "is_bot (ev e1 sigma1) \<or> is_bot (ev e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_bot (ev e1 sigma1)" and nb2: "\<not> is_bot (ev e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "tobool (ev e1 sigma2) = Some True \<or> tobool (ev e2 sigma2) = Some True")
      case True
      then have "tobool (ev e1 sigma1) = Some True \<or> tobool (ev e2 sigma1) = Some True"
        using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
      with True nb1 nb2 nb1' nb2' show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "tobool (ev e1 sigma2) = Some False \<and> tobool (ev e2 sigma2) = Some False")
        case True
        then have "tobool (ev e1 sigma1) = Some False" and "tobool (ev e2 sigma1) = Some False"
          using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by simp
      next
        case False
        with \<open>\<not> (tobool (ev e1 sigma2) = Some True \<or> tobool (ev e2 sigma2) = Some True)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "tobool (ev e1 sigma1) = Some True \<or> tobool (ev e2 sigma1) = Some True";
              cases "tobool (ev e1 sigma1) = Some False \<and> tobool (ev e2 sigma1) = Some False")
             auto
      qed
    qed
  qed
qed

end

end
