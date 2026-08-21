  theory Abstract_Arithmetic
  imports Abstract_Domain
begin

section \<open>Generic expression soundness\<close>

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

  \<open>ev\<close>, \<open>lit\<close>, \<open>lt\<close>, \<open>eqb\<close>, and \<open>tobool\<close> are locale parameters, not derived:
  interpreting this locale at a domain's own \<open>aval_<dom>\<close>, literal-embedding
  function, and comparison/truthiness queries keeps every existing call site
  of \<open>aval_<dom>\<close> untouched -- the shared \<open>aval_dom_sound\<close> lemma below is
  stated over the same externally-fixed functions, not a locale-internal
  reconstruction of them.
\<close>

text \<open>
  A comparison or logical result is always the concrete C truthiness value
  \<open>0\<close>/\<open>1\<close>. Abstractly that becomes \<open>Some True \<Rightarrow> lit 1\<close> (definitely true),
  \<open>Some False \<Rightarrow> lit 0\<close> (definitely false), \<open>None \<Rightarrow> lit 0 \<squnion> lit 1\<close> (unknown,
  soundly covering both) -- exactly Goblint's \<open>id_binary_pred\<close>/\<open>id_unary_log\<close>/
  \<open>id_binary_log\<close> pattern. \<open>And\<close>/\<open>Or\<close> additionally exploit the annihilator
  case (a definitely-false conjunct settles the whole conjunction, a
  definitely-true disjunct settles the whole disjunction) before falling back
  to the fully unknown join, mirroring \<open>id_binary_log\<close>'s own short-circuit.

  Each operand is queried through \<open>lt\<close>/\<open>eqb\<close>/\<open>tobool\<close> only when it is not
  itself \<open>is_bot\<close>: an \<open>is_bot\<close> operand denotes an unreachable value (its
  concretization is empty), so the whole comparison collapses to \<open>bot\<close> rather
  than querying a value with no witness to reason about. This guard is not
  optional bookkeeping -- \<open>bot\<close> is every domain's own least element, so a
  comparison against it can widen to conflicting query answers as the
  \<^emph>\<open>other\<close> operand widens; routing it through \<open>bot\<close> directly, before \<open>lt\<close>/
  \<open>eqb\<close>/\<open>tobool\<close> ever see it, is what keeps \<open>aval_dom_mono\<close> provable without
  demanding an impossible monotonicity obligation from those queries at their
  own domain's bottom.
\<close>

locale expression_domain_sound =
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
      with \<open>\<not> (tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False)\<close>
        nb1 nb2
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
      with \<open>\<not> (tobool (ev e1 sigma) = Some True \<or> tobool (ev e2 sigma) = Some True)\<close>
        nb1 nb2
      show ?thesis by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])
    qed
  qed
qed


lemma aval_dom_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> ev a sigma1 \<le> ev a sigma2"
proof (induction a arbitrary: sigma1 sigma2)
  case (N n) then show ?case by auto
next
  case (V x) then show ?case by (auto simp add: le_funD)
next
  case (Plus e1 e2) then show ?case by auto
next
  case (Minus e1 e2) then show ?case by auto
next
  case (Times e1 e2) then show ?case by auto
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
        then have "tobool (ev e1 sigma1) = Some True" and "tobool (ev e2 sigma1) = Some True"
          using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by simp
      next
        case False
        with \<open>\<not> (tobool (ev e1 sigma2) = Some False \<or> tobool (ev e2 sigma2) = Some False)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "tobool (ev e1 sigma1) = Some False \<or> tobool (ev e2 sigma1) = Some False";
              cases "tobool (ev e1 sigma1) = Some True \<and> tobool (ev e2 sigma1) = Some True") auto
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
        then have "tobool (ev e1 sigma1) = Some False" and "tobool (ev e2 sigma1) = Some False"
          using tobool_mono[OF nb1 p_mono] tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by simp
      next
        case False
        with \<open>\<not> (tobool (ev e1 sigma2) = Some True \<or> tobool (ev e2 sigma2) = Some True)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "tobool (ev e1 sigma1) = Some True \<or> tobool (ev e2 sigma1) = Some True";
              cases "tobool (ev e1 sigma1) = Some False \<and> tobool (ev e2 sigma1) = Some False") auto
      qed
    qed
  qed
qed

end

end

