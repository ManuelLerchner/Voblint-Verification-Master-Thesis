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
  identical shape and proof script: structural induction on \<open>exp\<close>, discharged
  by the same per-operator soundness facts. Arithmetic
  (\<open>plus_sound\<close>/\<open>minus_sound\<close>/\<open>times_sound\<close>) and comparison/truthiness
  (\<open>lt\<close>/\<open>eqb\<close>/\<open>tobool\<close>) are genuinely domain-specific -- each domain's own
  case-split proof over its own representation -- so this locale does not try
  to share those. What it shares is the one induction that combines them,
  mirroring Goblint's \<open>base.ml\<close> expression evaluator: \<open>Base\<close> only ever calls
  \<open>ID.add\<close>/\<open>ID.lt\<close>/\<open>ID.to_bool\<close> and never recomputes a comparison's
  precision itself, so \<open>ev\<close> here only ever calls \<open>lt\<close>/\<open>eqb\<close>/\<open>tobool\<close> and
  never recomputes what a domain already knows about its own relation.

  \<open>ev\<close> now mirrors \<^const>\<open>taval\<close>'s own typed recursion exactly: it takes
  the same \<open>tyenv\<close>/\<open>ikind\<close> pair, norms every arithmetic node once through
  the domain's own \<open>cast\<close> (never at \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>'s own 0/1
  result, which \<^const>\<open>taval\<close> never norms either -- 0 and 1 already fit
  every kind), and evaluates a comparison's or logical operator's operand(s)
  at their own synthesized kind, exactly as \<^const>\<open>taval_syn\<close> does. \<open>lit\<close>,
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
  \<open>id_binary_log\<close> pattern. \<open>And\<close>/\<open>Or\<close> additionally exploit the annihilator
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
  fixes ev :: "tyenv \<Rightarrow> ikind \<Rightarrow> exp \<Rightarrow> (vname \<Rightarrow> 'a::{sound_domain,plus,minus,times}) \<Rightarrow> 'a"
    and cast :: "ikind \<Rightarrow> 'a \<Rightarrow> 'a"
    and lit :: "int \<Rightarrow> 'a"
    and lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and eqb :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and tobool :: "'a \<Rightarrow> bool option"
  assumes ev_N[simp]: "ev \<Gamma> ik (N n) sigma = cast ik (lit n)"
    and ev_V[simp]: "ev \<Gamma> ik (V x) sigma = cast ik (sigma x)"
    and ev_Plus[simp]: "ev \<Gamma> ik (Plus e1 e2) sigma =
         cast ik (ev \<Gamma> ik e1 sigma + ev \<Gamma> ik e2 sigma)"
    and ev_Minus[simp]: "ev \<Gamma> ik (Minus e1 e2) sigma =
         cast ik (ev \<Gamma> ik e1 sigma - ev \<Gamma> ik e2 sigma)"
    and ev_Times[simp]: "ev \<Gamma> ik (Times e1 e2) sigma =
         cast ik (ev \<Gamma> ik e1 sigma * ev \<Gamma> ik e2 sigma)"
    and ev_Less[simp]: "ev \<Gamma> ik (Less e1 e2) sigma =
         (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2)) in
          if is_bot (ev \<Gamma> k e1 sigma) \<or> is_bot (ev \<Gamma> k e2 sigma) then bot
          else if lt (ev \<Gamma> k e1 sigma) (ev \<Gamma> k e2 sigma) = Some True then lit 1
          else if lt (ev \<Gamma> k e1 sigma) (ev \<Gamma> k e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Eq[simp]: "ev \<Gamma> ik (exp.Eq e1 e2) sigma =
         (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2)) in
          if is_bot (ev \<Gamma> k e1 sigma) \<or> is_bot (ev \<Gamma> k e2 sigma) then bot
          else if eqb (ev \<Gamma> k e1 sigma) (ev \<Gamma> k e2 sigma) = Some True then lit 1
          else if eqb (ev \<Gamma> k e1 sigma) (ev \<Gamma> k e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Not[simp]: "ev \<Gamma> ik (exp.Not e) sigma =
         (let k = opk (esyn \<Gamma> e) in
          if is_bot (ev \<Gamma> k e sigma) then bot
          else if tobool (ev \<Gamma> k e sigma) = Some True then lit 0
          else if tobool (ev \<Gamma> k e sigma) = Some False then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_And[simp]: "ev \<Gamma> ik (And e1 e2) sigma =
         (let k1 = opk (esyn \<Gamma> e1); k2 = opk (esyn \<Gamma> e2) in
          if is_bot (ev \<Gamma> k1 e1 sigma) \<or> is_bot (ev \<Gamma> k2 e2 sigma) then bot
          else if tobool (ev \<Gamma> k1 e1 sigma) = Some False \<or> tobool (ev \<Gamma> k2 e2 sigma) = Some False
          then lit 0
          else if tobool (ev \<Gamma> k1 e1 sigma) = Some True \<and> tobool (ev \<Gamma> k2 e2 sigma) = Some True
          then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_Or[simp]: "ev \<Gamma> ik (Or e1 e2) sigma =
         (let k1 = opk (esyn \<Gamma> e1); k2 = opk (esyn \<Gamma> e2) in
          if is_bot (ev \<Gamma> k1 e1 sigma) \<or> is_bot (ev \<Gamma> k2 e2 sigma) then bot
          else if tobool (ev \<Gamma> k1 e1 sigma) = Some True \<or> tobool (ev \<Gamma> k2 e2 sigma) = Some True
          then lit 1
          else if tobool (ev \<Gamma> k1 e1 sigma) = Some False \<and> tobool (ev \<Gamma> k2 e2 sigma) = Some False
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
  "(\<forall>x. s x \<in> gamma (sigma x)) \<Longrightarrow> taval \<Gamma> ik a s \<in> gamma (ev \<Gamma> ik a sigma)"
proof (induction a arbitrary: s sigma ik)
  case (N n) then show ?case by (simp add: cast_sound)
next
  case (V x) then show ?case by (simp add: cast_sound)
next
  case (Plus e1 e2)
  have h1: "taval \<Gamma> ik e1 s \<in> gamma (ev \<Gamma> ik e1 sigma)" using Plus.IH(1) Plus.prems by simp
  have h2: "taval \<Gamma> ik e2 s \<in> gamma (ev \<Gamma> ik e2 sigma)" using Plus.IH(2) Plus.prems by simp
  show ?case using cast_sound[OF plus_sound[OF h1 h2]] by simp
next
  case (Minus e1 e2)
  have h1: "taval \<Gamma> ik e1 s \<in> gamma (ev \<Gamma> ik e1 sigma)" using Minus.IH(1) Minus.prems by simp
  have h2: "taval \<Gamma> ik e2 s \<in> gamma (ev \<Gamma> ik e2 sigma)" using Minus.IH(2) Minus.prems by simp
  show ?case using cast_sound[OF minus_sound[OF h1 h2]] by simp
next
  case (Times e1 e2)
  have h1: "taval \<Gamma> ik e1 s \<in> gamma (ev \<Gamma> ik e1 sigma)" using Times.IH(1) Times.prems by simp
  have h2: "taval \<Gamma> ik e2 s \<in> gamma (ev \<Gamma> ik e2 sigma)" using Times.IH(2) Times.prems by simp
  show ?case using cast_sound[OF times_sound[OF h1 h2]] by simp
next
  case (Less e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have h1: "taval \<Gamma> ?k e1 s \<in> gamma (ev \<Gamma> ?k e1 sigma)" using Less.IH(1) Less.prems by simp
  have h2: "taval \<Gamma> ?k e2 s \<in> gamma (ev \<Gamma> ?k e2 sigma)" using Less.IH(2) Less.prems by simp
  have nb1: "\<not> is_bot (ev \<Gamma> ?k e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev \<Gamma> ?k e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "lt (ev \<Gamma> ?k e1 sigma) (ev \<Gamma> ?k e2 sigma) = Some True")
    case True
    with lt_sound[OF True h1 h2] nb1 nb2 show ?thesis by (simp add: Let_def)
  next
    case False
    show ?thesis
    proof (cases "lt (ev \<Gamma> ?k e1 sigma) (ev \<Gamma> ?k e2 sigma) = Some False")
      case True
      with lt_sound[OF True h1 h2] nb1 nb2 False show ?thesis by (simp add: Let_def)
    next
      case False
      with \<open>\<not> (lt (ev \<Gamma> ?k e1 sigma) (ev \<Gamma> ?k e2 sigma) = Some True)\<close> nb1 nb2
      show ?thesis by (auto simp: Let_def intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (Eq e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have h1: "taval \<Gamma> ?k e1 s \<in> gamma (ev \<Gamma> ?k e1 sigma)" using Eq.IH(1) Eq.prems by simp
  have h2: "taval \<Gamma> ?k e2 s \<in> gamma (ev \<Gamma> ?k e2 sigma)" using Eq.IH(2) Eq.prems by simp
  have nb1: "\<not> is_bot (ev \<Gamma> ?k e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev \<Gamma> ?k e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "eqb (ev \<Gamma> ?k e1 sigma) (ev \<Gamma> ?k e2 sigma) = Some True")
    case True
    with eqb_sound[OF True h1 h2] nb1 nb2 show ?thesis by (simp add: Let_def)
  next
    case False
    show ?thesis
    proof (cases "eqb (ev \<Gamma> ?k e1 sigma) (ev \<Gamma> ?k e2 sigma) = Some False")
      case True
      with eqb_sound[OF True h1 h2] nb1 nb2 False show ?thesis by (simp add: Let_def)
    next
      case False
      with \<open>\<not> (eqb (ev \<Gamma> ?k e1 sigma) (ev \<Gamma> ?k e2 sigma) = Some True)\<close> nb1 nb2
      show ?thesis by (auto simp: Let_def intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (Not e)
  let ?k = "opk (esyn \<Gamma> e)"
  have h: "taval \<Gamma> ?k e s \<in> gamma (ev \<Gamma> ?k e sigma)" using Not.IH Not.prems by simp
  have nb: "\<not> is_bot (ev \<Gamma> ?k e sigma)" using h is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev \<Gamma> ?k e sigma) = Some True")
    case True
    with tobool_sound[OF True h] nb show ?thesis by (simp add: Let_def)
  next
    case False
    show ?thesis
    proof (cases "tobool (ev \<Gamma> ?k e sigma) = Some False")
      case True
      with tobool_sound[OF True h] nb False show ?thesis by (simp add: Let_def)
    next
      case False
      with \<open>\<not> (tobool (ev \<Gamma> ?k e sigma) = Some True)\<close> nb
      show ?thesis by (auto simp: Let_def intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (And e1 e2)
  let ?k1 = "opk (esyn \<Gamma> e1)" and ?k2 = "opk (esyn \<Gamma> e2)"
  have h1: "taval \<Gamma> ?k1 e1 s \<in> gamma (ev \<Gamma> ?k1 e1 sigma)" using And.IH(1) And.prems by simp
  have h2: "taval \<Gamma> ?k2 e2 s \<in> gamma (ev \<Gamma> ?k2 e2 sigma)" using And.IH(2) And.prems by simp
  have nb1: "\<not> is_bot (ev \<Gamma> ?k1 e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev \<Gamma> ?k2 e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma) = Some False \<or> tobool (ev \<Gamma> ?k2 e2 sigma) = Some False")
    case True
    then have "\<not> truthy (taval \<Gamma> ?k1 e1 s) \<or> \<not> truthy (taval \<Gamma> ?k2 e2 s)"
      using tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by (auto simp: Let_def)
  next
    case False
    show ?thesis
    proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma) = Some True \<and> tobool (ev \<Gamma> ?k2 e2 sigma) = Some True")
      case True
      then have "truthy (taval \<Gamma> ?k1 e1 s) \<and> truthy (taval \<Gamma> ?k2 e2 s)"
        using tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by (simp add: Let_def)
    next
      case False
      with \<open>\<not> (tobool (ev \<Gamma> ?k1 e1 sigma) = Some False \<or> tobool (ev \<Gamma> ?k2 e2 sigma) = Some False)\<close>
        nb1 nb2
      show ?thesis by (auto simp: Let_def intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (Or e1 e2)
  let ?k1 = "opk (esyn \<Gamma> e1)" and ?k2 = "opk (esyn \<Gamma> e2)"
  have h1: "taval \<Gamma> ?k1 e1 s \<in> gamma (ev \<Gamma> ?k1 e1 sigma)" using Or.IH(1) Or.prems by simp
  have h2: "taval \<Gamma> ?k2 e2 s \<in> gamma (ev \<Gamma> ?k2 e2 sigma)" using Or.IH(2) Or.prems by simp
  have nb1: "\<not> is_bot (ev \<Gamma> ?k1 e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev \<Gamma> ?k2 e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma) = Some True \<or> tobool (ev \<Gamma> ?k2 e2 sigma) = Some True")
    case True
    then have "truthy (taval \<Gamma> ?k1 e1 s) \<or> truthy (taval \<Gamma> ?k2 e2 s)"
      using tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by (auto simp: Let_def)
  next
    case False
    show ?thesis
    proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma) = Some False \<and> tobool (ev \<Gamma> ?k2 e2 sigma) = Some False")
      case True
      then have "\<not> truthy (taval \<Gamma> ?k1 e1 s) \<and> \<not> truthy (taval \<Gamma> ?k2 e2 s)"
        using tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by (simp add: Let_def)
    next
      case False
      with \<open>\<not> (tobool (ev \<Gamma> ?k1 e1 sigma) = Some True \<or> tobool (ev \<Gamma> ?k2 e2 sigma) = Some True)\<close>
        nb1 nb2
      show ?thesis by (auto simp: Let_def intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
qed

lemma aval_dom_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> ev \<Gamma> ik a sigma1 \<le> ev \<Gamma> ik a sigma2"
proof (induction a arbitrary: sigma1 sigma2 ik)
  case (N n) then show ?case by (simp add: cast_mono)
next
  case (V x) then show ?case by (simp add: cast_mono le_funD)
next
  case (Plus e1 e2)
  have "ev \<Gamma> ik e1 sigma1 \<le> ev \<Gamma> ik e1 sigma2" using Plus.IH(1) Plus.prems by simp
  moreover have "ev \<Gamma> ik e2 sigma1 \<le> ev \<Gamma> ik e2 sigma2" using Plus.IH(2) Plus.prems by simp
  ultimately show ?case using plus_mono by (simp add: cast_mono)
next
  case (Minus e1 e2)
  have "ev \<Gamma> ik e1 sigma1 \<le> ev \<Gamma> ik e1 sigma2" using Minus.IH(1) Minus.prems by simp
  moreover have "ev \<Gamma> ik e2 sigma1 \<le> ev \<Gamma> ik e2 sigma2" using Minus.IH(2) Minus.prems by simp
  ultimately show ?case using minus_mono by (simp add: cast_mono)
next
  case (Times e1 e2)
  have "ev \<Gamma> ik e1 sigma1 \<le> ev \<Gamma> ik e1 sigma2" using Times.IH(1) Times.prems by simp
  moreover have "ev \<Gamma> ik e2 sigma1 \<le> ev \<Gamma> ik e2 sigma2" using Times.IH(2) Times.prems by simp
  ultimately show ?case using times_mono by (simp add: cast_mono)
next
  case (Less e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have p_mono: "ev \<Gamma> ?k e1 sigma1 \<le> ev \<Gamma> ?k e1 sigma2" using Less.IH(1) Less.prems by simp
  have q_mono: "ev \<Gamma> ?k e2 sigma1 \<le> ev \<Gamma> ?k e2 sigma2" using Less.IH(2) Less.prems by simp
  show ?case
  proof (cases "is_bot (ev \<Gamma> ?k e1 sigma1) \<or> is_bot (ev \<Gamma> ?k e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least Let_def)
  next
    case False
    then have nb1: "\<not> is_bot (ev \<Gamma> ?k e1 sigma1)" and nb2: "\<not> is_bot (ev \<Gamma> ?k e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev \<Gamma> ?k e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev \<Gamma> ?k e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "lt (ev \<Gamma> ?k e1 sigma2) (ev \<Gamma> ?k e2 sigma2)")
      case (Some b)
      then have "lt (ev \<Gamma> ?k e1 sigma1) (ev \<Gamma> ?k e2 sigma1) = Some b"
        using lt_mono[OF nb1 nb2 p_mono q_mono] by simp
      then show ?thesis using Some nb1 nb2 nb1' nb2' by (cases b) (simp_all add: Let_def)
    next
      case None
      then show ?thesis using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        by (cases "lt (ev \<Gamma> ?k e1 sigma1) (ev \<Gamma> ?k e2 sigma1) = Some True";
            cases "lt (ev \<Gamma> ?k e1 sigma1) (ev \<Gamma> ?k e2 sigma1) = Some False") (auto simp: Let_def)
    qed
  qed
next
  case (Eq e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have p_mono: "ev \<Gamma> ?k e1 sigma1 \<le> ev \<Gamma> ?k e1 sigma2" using Eq.IH(1) Eq.prems by simp
  have q_mono: "ev \<Gamma> ?k e2 sigma1 \<le> ev \<Gamma> ?k e2 sigma2" using Eq.IH(2) Eq.prems by simp
  show ?case
  proof (cases "is_bot (ev \<Gamma> ?k e1 sigma1) \<or> is_bot (ev \<Gamma> ?k e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least Let_def)
  next
    case False
    then have nb1: "\<not> is_bot (ev \<Gamma> ?k e1 sigma1)" and nb2: "\<not> is_bot (ev \<Gamma> ?k e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev \<Gamma> ?k e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev \<Gamma> ?k e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "eqb (ev \<Gamma> ?k e1 sigma2) (ev \<Gamma> ?k e2 sigma2)")
      case (Some b)
      then have "eqb (ev \<Gamma> ?k e1 sigma1) (ev \<Gamma> ?k e2 sigma1) = Some b"
        using eqb_mono[OF nb1 nb2 p_mono q_mono] by simp
      then show ?thesis using Some nb1 nb2 nb1' nb2' by (cases b) (simp_all add: Let_def)
    next
      case None
      then show ?thesis using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        by (cases "eqb (ev \<Gamma> ?k e1 sigma1) (ev \<Gamma> ?k e2 sigma1) = Some True";
            cases "eqb (ev \<Gamma> ?k e1 sigma1) (ev \<Gamma> ?k e2 sigma1) = Some False") (auto simp: Let_def)
    qed
  qed
next
  case (Not e)
  let ?k = "opk (esyn \<Gamma> e)"
  have p_mono: "ev \<Gamma> ?k e sigma1 \<le> ev \<Gamma> ?k e sigma2" using Not.IH Not.prems by simp
  show ?case
  proof (cases "is_bot (ev \<Gamma> ?k e sigma1)")
    case True
    then show ?thesis by (simp add: bot_least Let_def)
  next
    case False
    then have nb: "\<not> is_bot (ev \<Gamma> ?k e sigma1)" by auto
    have nb': "\<not> is_bot (ev \<Gamma> ?k e sigma2)" using nb p_mono is_bot_mono by blast
    show ?thesis
    proof (cases "tobool (ev \<Gamma> ?k e sigma2)")
      case (Some b)
      then have "tobool (ev \<Gamma> ?k e sigma1) = Some b" using tobool_mono[OF nb p_mono] by simp
      then show ?thesis using Some nb nb' by (cases b) (simp_all add: Let_def)
    next
      case None
      then show ?thesis using nb nb' sup_ge1 sup_ge2
        by (cases "tobool (ev \<Gamma> ?k e sigma1) = Some True";
            cases "tobool (ev \<Gamma> ?k e sigma1) = Some False") (auto simp: Let_def)
    qed
  qed
next
  case (And e1 e2)
  let ?k1 = "opk (esyn \<Gamma> e1)" and ?k2 = "opk (esyn \<Gamma> e2)"
  have p_mono: "ev \<Gamma> ?k1 e1 sigma1 \<le> ev \<Gamma> ?k1 e1 sigma2" using And.IH(1) And.prems by simp
  have q_mono: "ev \<Gamma> ?k2 e2 sigma1 \<le> ev \<Gamma> ?k2 e2 sigma2" using And.IH(2) And.prems by simp
  show ?case
  proof (cases "is_bot (ev \<Gamma> ?k1 e1 sigma1) \<or> is_bot (ev \<Gamma> ?k2 e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least Let_def)
  next
    case False
    then have nb1: "\<not> is_bot (ev \<Gamma> ?k1 e1 sigma1)" and nb2: "\<not> is_bot (ev \<Gamma> ?k2 e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev \<Gamma> ?k1 e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev \<Gamma> ?k2 e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma2) = Some False \<or> tobool (ev \<Gamma> ?k2 e2 sigma2) = Some False")
      case True
      then have "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some False \<or> tobool (ev \<Gamma> ?k2 e2 sigma1) = Some False"
        using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
      with True nb1 nb2 nb1' nb2' show ?thesis by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma2) = Some True \<and> tobool (ev \<Gamma> ?k2 e2 sigma2) = Some True")
        case True
        then have "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some True" and "tobool (ev \<Gamma> ?k2 e2 sigma1) = Some True"
          using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by (simp add: Let_def)
      next
        case False
        with \<open>\<not> (tobool (ev \<Gamma> ?k1 e1 sigma2) = Some False \<or> tobool (ev \<Gamma> ?k2 e2 sigma2) = Some False)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some False \<or> tobool (ev \<Gamma> ?k2 e2 sigma1) = Some False";
              cases "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some True \<and> tobool (ev \<Gamma> ?k2 e2 sigma1) = Some True")
             (auto simp: Let_def)
      qed
    qed
  qed
next
  case (Or e1 e2)
  let ?k1 = "opk (esyn \<Gamma> e1)" and ?k2 = "opk (esyn \<Gamma> e2)"
  have p_mono: "ev \<Gamma> ?k1 e1 sigma1 \<le> ev \<Gamma> ?k1 e1 sigma2" using Or.IH(1) Or.prems by simp
  have q_mono: "ev \<Gamma> ?k2 e2 sigma1 \<le> ev \<Gamma> ?k2 e2 sigma2" using Or.IH(2) Or.prems by simp
  show ?case
  proof (cases "is_bot (ev \<Gamma> ?k1 e1 sigma1) \<or> is_bot (ev \<Gamma> ?k2 e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least Let_def)
  next
    case False
    then have nb1: "\<not> is_bot (ev \<Gamma> ?k1 e1 sigma1)" and nb2: "\<not> is_bot (ev \<Gamma> ?k2 e2 sigma1)" by auto
    have nb1': "\<not> is_bot (ev \<Gamma> ?k1 e1 sigma2)" using nb1 p_mono is_bot_mono by blast
    have nb2': "\<not> is_bot (ev \<Gamma> ?k2 e2 sigma2)" using nb2 q_mono is_bot_mono by blast
    show ?thesis
    proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma2) = Some True \<or> tobool (ev \<Gamma> ?k2 e2 sigma2) = Some True")
      case True
      then have "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some True \<or> tobool (ev \<Gamma> ?k2 e2 sigma1) = Some True"
        using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
      with True nb1 nb2 nb1' nb2' show ?thesis by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "tobool (ev \<Gamma> ?k1 e1 sigma2) = Some False \<and> tobool (ev \<Gamma> ?k2 e2 sigma2) = Some False")
        case True
        then have "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some False" and "tobool (ev \<Gamma> ?k2 e2 sigma1) = Some False"
          using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by (simp add: Let_def)
      next
        case False
        with \<open>\<not> (tobool (ev \<Gamma> ?k1 e1 sigma2) = Some True \<or> tobool (ev \<Gamma> ?k2 e2 sigma2) = Some True)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some True \<or> tobool (ev \<Gamma> ?k2 e2 sigma1) = Some True";
              cases "tobool (ev \<Gamma> ?k1 e1 sigma1) = Some False \<and> tobool (ev \<Gamma> ?k2 e2 sigma1) = Some False")
             (auto simp: Let_def)
      qed
    qed
  qed
qed

end

text \<open>
  \<open>expression_domain_sound_untyped\<close> is the ikind-free counterpart of
  \<open>expression_domain_sound\<close> above, for a domain whose arithmetic genuinely
  needs no per-variable kind (e.g. Congruence, whose class representation is
  exact regardless of width and only meets \<open>ikind\<close> at its own \<open>cast\<close>
  boundary). \<open>ev\<close> here mirrors the untyped \<open>aval\<close>, not \<open>taval\<close>.
\<close>

locale expression_domain_sound_untyped =
  fixes ev :: "exp \<Rightarrow> (vname \<Rightarrow> 'a::{sound_domain,plus,minus,times}) \<Rightarrow> 'a"
    and lit :: "int \<Rightarrow> 'a"
    and lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and eqb :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and tobool :: "'a \<Rightarrow> bool option"
  assumes ev_N[simp]: "ev (N n) sigma = lit n"
    and ev_V[simp]: "ev (V x) sigma = sigma x"
    and ev_Plus[simp]: "ev (Plus e1 e2) sigma = ev e1 sigma + ev e2 sigma"
    and ev_Minus[simp]: "ev (Minus e1 e2) sigma = ev e1 sigma - ev e2 sigma"
    and ev_Times[simp]: "ev (Times e1 e2) sigma = ev e1 sigma * ev e2 sigma"
    and ev_Less[simp]: "ev (Less e1 e2) sigma =
         (if is_bot (ev e1 sigma) \<or> is_bot (ev e2 sigma) then bot
          else if lt (ev e1 sigma) (ev e2 sigma) = Some True then lit 1
          else if lt (ev e1 sigma) (ev e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Eq[simp]: "ev (exp.Eq e1 e2) sigma =
         (if is_bot (ev e1 sigma) \<or> is_bot (ev e2 sigma) then bot
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some True then lit 1
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Not[simp]: "ev (exp.Not e) sigma =
         (if is_bot (ev e sigma) then bot
          else if tobool (ev e sigma) = Some True then lit 0
          else if tobool (ev e sigma) = Some False then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_And[simp]: "ev (And e1 e2) sigma =
         (if is_bot (ev e1 sigma) \<or> is_bot (ev e2 sigma) then bot
          else if tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False
          then lit 0
          else if tobool (ev e1 sigma) = Some True \<and> tobool (ev e2 sigma) = Some True
          then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_Or[simp]: "ev (Or e1 e2) sigma =
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
begin

lemma aval_dom_sound:
  "(\<forall>x. s x \<in> gamma (sigma x)) \<Longrightarrow> aval a s \<in> gamma (ev a sigma)"
proof (induction a arbitrary: s sigma)
  case (N n) then show ?case by auto
next
  case (V x) then show ?case by auto
next
  case (Plus e1 e2) then show ?case by auto
next
  case (Minus e1 e2) then show ?case by auto
next
  case (Times e1 e2) then show ?case by auto
next
  case (Less e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" using Less.IH(1) Less.prems by simp
  have h2: "aval e2 s \<in> gamma (ev e2 sigma)" using Less.IH(2) Less.prems by simp
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
  case (Eq e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" using Eq.IH(1) Eq.prems by simp
  have h2: "aval e2 s \<in> gamma (ev e2 sigma)" using Eq.IH(2) Eq.prems by simp
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
  case (Not e)
  have h: "aval e s \<in> gamma (ev e sigma)" using Not.IH Not.prems by simp
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
  case (And e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" using And.IH(1) And.prems by simp
  have h2: "aval e2 s \<in> gamma (ev e2 sigma)" using And.IH(2) And.prems by simp
  have nb1: "\<not> is_bot (ev e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False")
    case True
    then have "\<not> truthy (aval e1 s) \<or> \<not> truthy (aval e2 s)"
      using tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by auto
  next
    case False
    show ?thesis
    proof (cases "tobool (ev e1 sigma) = Some True \<and> tobool (ev e2 sigma) = Some True")
      case True
      then have "truthy (aval e1 s) \<and> truthy (aval e2 s)"
        using tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by simp
    next
      case False
      with \<open>\<not> (tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False)\<close> nb1 nb2
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (Or e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" using Or.IH(1) Or.prems by simp
  have h2: "aval e2 s \<in> gamma (ev e2 sigma)" using Or.IH(2) Or.prems by simp
  have nb1: "\<not> is_bot (ev e1 sigma)" using h1 is_bot_correct by auto
  have nb2: "\<not> is_bot (ev e2 sigma)" using h2 is_bot_correct by auto
  show ?case
  proof (cases "tobool (ev e1 sigma) = Some True \<or> tobool (ev e2 sigma) = Some True")
    case True
    then have "truthy (aval e1 s) \<or> truthy (aval e2 s)"
      using tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by auto
  next
    case False
    show ?thesis
    proof (cases "tobool (ev e1 sigma) = Some False \<and> tobool (ev e2 sigma) = Some False")
      case True
      then have "\<not> truthy (aval e1 s) \<and> \<not> truthy (aval e2 s)"
        using tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by simp
    next
      case False
      with \<open>\<not> (tobool (ev e1 sigma) = Some True \<or> tobool (ev e2 sigma) = Some True)\<close> nb1 nb2
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
qed

lemma aval_dom_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> ev a sigma1 \<le> ev a sigma2"
proof (induction a arbitrary: sigma1 sigma2)
  case (N n) then show ?case by simp
next
  case (V x) then show ?case by (simp add: le_funD)
next
  case (Plus e1 e2)
  have "ev e1 sigma1 \<le> ev e1 sigma2" using Plus.IH(1) Plus.prems by simp
  moreover have "ev e2 sigma1 \<le> ev e2 sigma2" using Plus.IH(2) Plus.prems by simp
  ultimately show ?case using plus_mono by simp
next
  case (Minus e1 e2)
  have "ev e1 sigma1 \<le> ev e1 sigma2" using Minus.IH(1) Minus.prems by simp
  moreover have "ev e2 sigma1 \<le> ev e2 sigma2" using Minus.IH(2) Minus.prems by simp
  ultimately show ?case using minus_mono by simp
next
  case (Times e1 e2)
  have "ev e1 sigma1 \<le> ev e1 sigma2" using Times.IH(1) Times.prems by simp
  moreover have "ev e2 sigma1 \<le> ev e2 sigma2" using Times.IH(2) Times.prems by simp
  ultimately show ?case using times_mono by simp
next
  case (Less e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using Less.IH(1) Less.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using Less.IH(2) Less.prems by simp
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
  case (Eq e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using Eq.IH(1) Eq.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using Eq.IH(2) Eq.prems by simp
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
  case (Not e)
  have p_mono: "ev e sigma1 \<le> ev e sigma2" using Not.IH Not.prems by simp
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
      then have "tobool (ev e sigma1) = Some b"
        using tobool_mono[OF nb p_mono] by simp
      then show ?thesis using Some nb nb' by (cases b) simp_all
    next
      case None
      then show ?thesis using nb nb' sup_ge1 sup_ge2
        by (cases "tobool (ev e sigma1) = Some True";
            cases "tobool (ev e sigma1) = Some False") auto
    qed
  qed
next
  case (And e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using And.IH(1) And.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using And.IH(2) And.prems by simp
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
        then show ?thesis
          using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
          by (cases "tobool (ev e1 sigma1) = Some True \<and> tobool (ev e2 sigma1) = Some True";
              cases "tobool (ev e1 sigma1) = Some False \<or> tobool (ev e2 sigma1) = Some False")
             (auto simp: tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono])
      next
        case False
        then show ?thesis
          using \<open>\<not> (tobool (ev e1 sigma2) = Some False \<or> tobool (ev e2 sigma2) = Some False)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        by (cases "tobool (ev e1 sigma1) = Some True \<and> tobool (ev e2 sigma1) = Some True";
            cases "tobool (ev e1 sigma1) = Some False \<or> tobool (ev e2 sigma1) = Some False")
           (auto simp: Let_def)
      qed
    qed
  qed
next
  case (Or e1 e2)
  have p_mono: "ev e1 sigma1 \<le> ev e1 sigma2" using Or.IH(1) Or.prems by simp
  have q_mono: "ev e2 sigma1 \<le> ev e2 sigma2" using Or.IH(2) Or.prems by simp
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
        then show ?thesis
          using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
          by (cases "tobool (ev e1 sigma1) = Some False \<and> tobool (ev e2 sigma1) = Some False";
              cases "tobool (ev e1 sigma1) = Some True \<or> tobool (ev e2 sigma1) = Some True")
             (auto simp: tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono])
      next
        case False
        then show ?thesis
          using \<open>\<not> (tobool (ev e1 sigma2) = Some True \<or> tobool (ev e2 sigma2) = Some True)\<close>
            nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
          by (cases "tobool (ev e1 sigma1) = Some False \<and> tobool (ev e2 sigma1) = Some False";
              cases "tobool (ev e1 sigma1) = Some True \<or> tobool (ev e2 sigma1) = Some True")
             (auto simp: Let_def)
      qed
    qed
  qed
qed

end

end
