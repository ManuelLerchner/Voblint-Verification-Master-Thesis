theory Abstract_Arithmetic
  imports "Voblint_Domain.Abstract_Domain" "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Generic expression soundness\<close>

text \<open>
  Sign, Interval, Parity, and Congruence each prove an \<open>aval_<dom>_sound\<close> lemma with the
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
  itself \<open>is_empty\<close>: an \<open>is_empty\<close> operand denotes an unreachable value (its
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
  fixes ev :: "exp \<Rightarrow> (vname \<Rightarrow> 'a::sound_domain) \<Rightarrow> 'a"
    and lit :: "int \<Rightarrow> 'a"
    and pls :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and mns :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and tms :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and dvs :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and rem :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and eqb :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and tobool :: "'a \<Rightarrow> bool option"
  assumes ev_N[simp]: "ev (N n) sigma = lit n"
    and ev_V[simp]: "ev (V x) sigma = sigma x"
    and ev_Plus[simp]: "ev (Plus e1 e2) sigma = pls (ev e1 sigma) (ev e2 sigma)"
    and ev_Minus[simp]: "ev (Minus e1 e2) sigma = mns (ev e1 sigma) (ev e2 sigma)"
    and ev_Times[simp]: "ev (Times e1 e2) sigma = tms (ev e1 sigma) (ev e2 sigma)"
    and ev_Div[simp]: "ev (Div e1 e2) sigma = dvs (ev e1 sigma) (ev e2 sigma)"
    and ev_Mod[simp]: "ev (Mod e1 e2) sigma = rem (ev e1 sigma) (ev e2 sigma)"
    and ev_Less[simp]: "ev (Less e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else if lt (ev e1 sigma) (ev e2 sigma) = Some True then lit 1
          else if lt (ev e1 sigma) (ev e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_LessEq[simp]: "ev (LessEq e1 e2) sigma =
         (if is_empty (ev e2 sigma) \<or> is_empty (ev e1 sigma) then bot
          else if lt (ev e2 sigma) (ev e1 sigma) = Some False then lit 1
          else if lt (ev e2 sigma) (ev e1 sigma) = Some True then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Greater[simp]: "ev (Greater e1 e2) sigma =
         (if is_empty (ev e2 sigma) \<or> is_empty (ev e1 sigma) then bot
          else if lt (ev e2 sigma) (ev e1 sigma) = Some True then lit 1
          else if lt (ev e2 sigma) (ev e1 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_GreaterEq[simp]: "ev (GreaterEq e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else if lt (ev e1 sigma) (ev e2 sigma) = Some False then lit 1
          else if lt (ev e1 sigma) (ev e2 sigma) = Some True then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_NotEq[simp]: "ev (NotEq e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some False then lit 1
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some True then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Eq[simp]: "ev (exp.Eq e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some True then lit 1
          else if eqb (ev e1 sigma) (ev e2 sigma) = Some False then lit 0
          else lit 0 \<squnion> lit 1)"
    and ev_Not[simp]: "ev (exp.Not e) sigma =
         (if is_empty (ev e sigma) then bot
          else if tobool (ev e sigma) = Some True then lit 0
          else if tobool (ev e sigma) = Some False then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_And[simp]: "ev (And e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else if tobool (ev e1 sigma) = Some False \<or> tobool (ev e2 sigma) = Some False
          then lit 0
          else if tobool (ev e1 sigma) = Some True \<and> tobool (ev e2 sigma) = Some True
          then lit 1
          else lit 0 \<squnion> lit 1)"
    and ev_Or[simp]: "ev (Or e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else if tobool (ev e1 sigma) = Some True \<or> tobool (ev e2 sigma) = Some True
          then lit 1
          else if tobool (ev e1 sigma) = Some False \<and> tobool (ev e2 sigma) = Some False
          then lit 0
          else lit 0 \<squnion> lit 1)"
    and lit_sound[simp]: "n \<in> gamma (lit n)"
    and plus_sound[intro]:
      "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i + j \<in> gamma (pls p q)"
    and minus_sound[intro]:
      "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i - j \<in> gamma (mns p q)"
    and times_sound[intro]:
      "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i * j \<in> gamma (tms p q)"
    and div_sound[intro]:
      "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> c_div i j \<in> gamma (dvs p q)"
    and mod_sound[intro]:
      "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> c_mod i j \<in> gamma (rem p q)"
    and lt_sound: "lt p q = Some b \<Longrightarrow> i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> (i < j) = b"
    and eqb_sound: "eqb p q = Some b \<Longrightarrow> i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> (i = j) = b"
    and tobool_sound: "tobool p = Some b \<Longrightarrow> i \<in> gamma (p::'a) \<Longrightarrow> truthy i = b"
begin

text \<open>
  Every comparison and connective evaluates to the same guarded choice between
  the literals \<open>0\<close>/\<open>1\<close> and their join. \<open>bool_lit_sound\<close> and
  \<open>bool_lit_mono\<close> discharge that shape once, so each induction case supplies
  only its own query facts.
\<close>

lemma bool_lit_sound:
  assumes "\<not> E" and "C1 \<Longrightarrow> v = t1" and "C2 \<Longrightarrow> v = t2" and "v \<in> {0, 1}"
  shows "v \<in> gamma
    (if E then bot else if C1 then lit t1 else if C2 then lit t2 else lit 0 \<squnion> lit 1)"
  using assms by (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])

lemma aval_dom_sound:
  "(\<forall>x. s x \<in> gamma (sigma x)) \<Longrightarrow> aval a s \<in> gamma (ev a sigma)"
proof (induction a arbitrary: s sigma)
  case (Less e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using Less by simp_all
  show ?case unfolding ev_Less aval.simps
    by (rule bool_lit_sound) (use h1 h2 is_empty_correct lt_sound[OF _ h1 h2] in auto)
next

  case (LessEq e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using LessEq by simp_all
  show ?case unfolding ev_LessEq aval.simps
    by (rule bool_lit_sound) (use h1 h2 is_empty_correct lt_sound[where b=True, OF _ h2 h1]
        lt_sound[where b=False, OF _ h2 h1] in auto)
next
  case (Greater e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using Greater by simp_all
  show ?case unfolding ev_Greater aval.simps
    by (rule bool_lit_sound) (use h1 h2 is_empty_correct lt_sound[OF _ h2 h1] in auto)
next
  case (GreaterEq e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using GreaterEq by simp_all
  show ?case unfolding ev_GreaterEq aval.simps
    by (rule bool_lit_sound) (use h1 h2 is_empty_correct lt_sound[where b=True, OF _ h1 h2]
        lt_sound[where b=False, OF _ h1 h2] in auto)
next
  case (NotEq e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using NotEq by simp_all
  show ?case unfolding ev_NotEq aval.simps
    by (rule bool_lit_sound) (use h1 h2 is_empty_correct eqb_sound[OF _ h1 h2] in auto)
next  case (Eq e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using Eq by simp_all
  show ?case unfolding ev_Eq aval.simps
    by (rule bool_lit_sound) (use h1 h2 is_empty_correct eqb_sound[OF _ h1 h2] in auto)
next
  case (Not e)
  have h: "aval e s \<in> gamma (ev e sigma)" using Not by simp
  show ?case unfolding ev_Not aval.simps
    by (rule bool_lit_sound) (use h is_empty_correct tobool_sound[OF _ h] in auto)
next
  case (And e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using And by simp_all
  show ?case unfolding ev_And aval.simps
    by (rule bool_lit_sound)
       (use h1 h2 is_empty_correct tobool_sound[OF _ h1] tobool_sound[OF _ h2] in auto)
next
  case (Or e1 e2)
  have h1: "aval e1 s \<in> gamma (ev e1 sigma)" and h2: "aval e2 s \<in> gamma (ev e2 sigma)"
    using Or by simp_all
  show ?case unfolding ev_Or aval.simps
    by (rule bool_lit_sound)
       (use h1 h2 is_empty_correct tobool_sound[OF _ h1] tobool_sound[OF _ h2] in auto)
qed auto

end

text \<open>
  Monotonicity needs strictly more than soundness does, and one domain can
  supply the first without the second: the composite integer domain's
  arithmetic is monotone only away from \<open>Refine_Fixpoint\<close>, while its soundness
  holds at every refinement mode. Splitting the two apart is what lets that
  domain interpret the shared induction twice --- unconditionally for
  \<open>aval_dom_sound\<close>, under its mode side condition for \<open>aval_dom_mono\<close> --- rather
  than repeat both proofs by hand.
\<close>

locale expression_domain_mono = expression_domain_sound +
  assumes plus_mono[intro]:
      "p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> pls p1 q1 \<le> pls p2 q2"
    and minus_mono[intro]:
      "p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> mns p1 q1 \<le> mns p2 q2"
    and times_mono[intro]:
      "p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> tms p1 q1 \<le> tms p2 q2"
    and div_mono[intro]:
      "p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> dvs p1 q1 \<le> dvs p2 q2"
    and mod_mono[intro]:
      "p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> rem p1 q1 \<le> rem p2 q2"
    and lt_mono:
      "\<not> is_empty p1 \<Longrightarrow> \<not> is_empty q1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow>
       lt p2 q2 = Some b \<Longrightarrow> lt p1 q1 = Some b"
    and eqb_mono:
      "\<not> is_empty p1 \<Longrightarrow> \<not> is_empty q1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> q1 \<le> q2 \<Longrightarrow>
       eqb p2 q2 = Some b \<Longrightarrow> eqb p1 q1 = Some b"
    and tobool_mono:
      "\<not> is_empty p1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some b \<Longrightarrow> tobool p1 = Some b"
begin

lemma bool_lit_mono:
  assumes "E2 \<Longrightarrow> E1" and "\<not> E1 \<Longrightarrow> D1 \<Longrightarrow> C1" and "\<not> E1 \<Longrightarrow> D2 \<Longrightarrow> C2"
    and "C1 \<Longrightarrow> \<not> C2" and "t1 \<in> {0, 1}" and "t2 \<in> {0, 1}"
  shows "(if E1 then bot else if C1 then lit t1 else if C2 then lit t2 else lit 0 \<squnion> lit 1)
    \<le> (if E2 then bot else if D1 then lit t1 else if D2 then lit t2 else lit 0 \<squnion> lit 1)"
  using assms by auto

lemma aval_dom_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> ev a sigma1 \<le> ev a sigma2"
proof (induction a arbitrary: sigma1 sigma2)
  case (Less e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Less by simp_all
  show ?case unfolding ev_Less
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ p q] in auto)
next

  case (LessEq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using LessEq by simp_all
  show ?case unfolding ev_LessEq
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ q p] in auto)
next
  case (Greater e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Greater by simp_all
  show ?case unfolding ev_Greater
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ q p] in auto)
next
  case (GreaterEq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using GreaterEq by simp_all
  show ?case unfolding ev_GreaterEq
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ p q] in auto)
next
  case (NotEq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using NotEq by simp_all
  show ?case unfolding ev_NotEq
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] eqb_mono[OF _ _ p q] in auto)
next  case (Eq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Eq by simp_all
  show ?case unfolding ev_Eq
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] eqb_mono[OF _ _ p q] in auto)
next
  case (Not e)
  have p: "ev e sigma1 \<le> ev e sigma2" using Not by simp
  show ?case unfolding ev_Not
    by (rule bool_lit_mono) (use is_empty_antimono[OF p] tobool_mono[OF _ p] in auto)
next
  case (And e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using And by simp_all
  show ?case unfolding ev_And
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q]
          tobool_mono[OF _ p] tobool_mono[OF _ q] in auto)
next
  case (Or e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Or by simp_all
  show ?case unfolding ev_Or
    by (rule bool_lit_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q]
          tobool_mono[OF _ p] tobool_mono[OF _ q] in auto)
qed (auto simp add: le_funD)

end

end
