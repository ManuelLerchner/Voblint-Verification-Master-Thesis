theory Abstract_Arithmetic
  imports "Voblint_Domain.Abstract_Domain" "Voblint_VIMP.VIMP_Expr"
    "Voblint_Framework.Abstract_Checks"
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
  \<open>0\<close>/\<open>1\<close>. Goblint's integer domains move between the two readings with
  \<open>of_bool\<close> and \<open>to_bool\<close>; here the three-valued answer of a query is read back
  as a value by \<open>of_bool_option\<close>: \<open>Some True\<close> is \<open>lit 1\<close>, \<open>Some False\<close>
  is \<open>lit 0\<close>, and an unknown answer joins both --- exactly Goblint's
  \<open>id_binary_pred\<close>/\<open>id_unary_log\<close>/\<open>id_binary_log\<close> pattern. A negated relation
  negates the query answer, and \<open>And\<close>/\<open>Or\<close> combine their operands' truthiness
  with \<^const>\<open>and_opt\<close>/\<^const>\<open>or_opt\<close>, which settle on one definite annihilating
  operand, mirroring \<open>id_binary_log\<close>'s own short-circuit.

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

fun of_bool_option :: "(int \<Rightarrow> 'a::sup) \<Rightarrow> bool option \<Rightarrow> 'a" where
  "of_bool_option lit (Some b) = lit (if b then 1 else 0)"
| "of_bool_option lit None = lit 0 \<squnion> lit 1"

text \<open>
  A definite answer survives widening the operands, so the combinators keep every
  definite answer of their wider inputs.
\<close>

lemma and_opt_mono:
  assumes "\<And>b. x2 = Some b \<Longrightarrow> x1 = Some b" and "\<And>b. y2 = Some b \<Longrightarrow> y1 = Some b"
  shows "and_opt x2 y2 = Some b \<Longrightarrow> and_opt x1 y1 = Some b"
  using assms(1)[of True] assms(1)[of False] assms(2)[of True] assms(2)[of False]
  unfolding and_opt_def by (cases b) (auto split: if_splits)

lemma or_opt_mono:
  assumes "\<And>b. x2 = Some b \<Longrightarrow> x1 = Some b" and "\<And>b. y2 = Some b \<Longrightarrow> y1 = Some b"
  shows "or_opt x2 y2 = Some b \<Longrightarrow> or_opt x1 y1 = Some b"
  using assms(1)[of True] assms(1)[of False] assms(2)[of True] assms(2)[of False]
  unfolding or_opt_def by (cases b) (auto split: if_splits)

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
          else of_bool_option lit (lt (ev e1 sigma) (ev e2 sigma)))"
    and ev_LessEq[simp]: "ev (LessEq e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else of_bool_option lit (map_option HOL.Not (lt (ev e2 sigma) (ev e1 sigma))))"
    and ev_Greater[simp]: "ev (Greater e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else of_bool_option lit (lt (ev e2 sigma) (ev e1 sigma)))"
    and ev_GreaterEq[simp]: "ev (GreaterEq e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else of_bool_option lit (map_option HOL.Not (lt (ev e1 sigma) (ev e2 sigma))))"
    and ev_NotEq[simp]: "ev (NotEq e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else of_bool_option lit (map_option HOL.Not (eqb (ev e1 sigma) (ev e2 sigma))))"
    and ev_Eq[simp]: "ev (exp.Eq e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else of_bool_option lit (eqb (ev e1 sigma) (ev e2 sigma)))"
    and ev_Not[simp]: "ev (exp.Not e) sigma =
         (if is_empty (ev e sigma) then bot
          else of_bool_option lit (map_option HOL.Not (tobool (ev e sigma))))"
    and ev_And[simp]: "ev (And e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else of_bool_option lit (and_opt (tobool (ev e1 sigma)) (tobool (ev e2 sigma))))"
    and ev_Or[simp]: "ev (Or e1 e2) sigma =
         (if is_empty (ev e1 sigma) \<or> is_empty (ev e2 sigma) then bot
          else of_bool_option lit (or_opt (tobool (ev e1 sigma)) (tobool (ev e2 sigma))))"
    and lit_sound[simp]: "n \<in> \<gamma> (lit n)"
    and plus_sound[intro]:
      "i \<in> \<gamma> (p::'a) \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> i + j \<in> \<gamma> (pls p q)"
    and minus_sound[intro]:
      "i \<in> \<gamma> (p::'a) \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> i - j \<in> \<gamma> (mns p q)"
    and times_sound[intro]:
      "i \<in> \<gamma> (p::'a) \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> i * j \<in> \<gamma> (tms p q)"
    and div_sound[intro]:
      "i \<in> \<gamma> (p::'a) \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> c_div i j \<in> \<gamma> (dvs p q)"
    and mod_sound[intro]:
      "i \<in> \<gamma> (p::'a) \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> c_mod i j \<in> \<gamma> (rem p q)"
    and lt_sound: "lt p q = Some b \<Longrightarrow> i \<in> \<gamma> (p::'a) \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> (i < j) = b"
    and eqb_sound: "eqb p q = Some b \<Longrightarrow> i \<in> \<gamma> (p::'a) \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> (i = j) = b"
    and tobool_sound: "tobool p = Some b \<Longrightarrow> i \<in> \<gamma> (p::'a) \<Longrightarrow> truthy i = b"
begin

text \<open>
  Every comparison and connective reads its query answer back through
  \<^const>\<open>of_bool_option\<close> behind the same emptiness guard. \<open>of_bool_option_sound\<close>
  and \<open>of_bool_option_mono\<close> discharge that shape once, so each induction case
  supplies only its own query facts.
\<close>

lemma of_bool_option_sound:
  assumes "\<not> E" and "\<And>b. r = Some b \<Longrightarrow> v = (if b then 1 else 0)" and "v \<in> {0, 1}"
  shows "v \<in> \<gamma> (if E then bot else of_bool_option lit r)"
  using assms
  by (cases r) (auto intro: gamma_sup_ub1[THEN subsetD] gamma_sup_ub2[THEN subsetD])

lemma aval_dom_sound:
  "(\<forall>x. s x \<in> \<gamma> (sigma x)) \<Longrightarrow> \<lbrakk>a\<rbrakk>\<^sub>e s \<in> \<gamma> (ev a sigma)"
proof (induction a arbitrary: s sigma)
  case (Less e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using Less by simp_all
  show ?case unfolding ev_Less aval.simps
    by (rule of_bool_option_sound) (use h1 h2 is_empty_correct lt_sound[OF _ h1 h2] in auto)
next
  case (LessEq e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using LessEq by simp_all
  show ?case unfolding ev_LessEq aval.simps
    by (rule of_bool_option_sound) (use h1 h2 is_empty_correct lt_sound[OF _ h2 h1] in auto)
next
  case (Greater e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using Greater by simp_all
  show ?case unfolding ev_Greater aval.simps
    by (rule of_bool_option_sound) (use h1 h2 is_empty_correct lt_sound[OF _ h2 h1] in auto)
next
  case (GreaterEq e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using GreaterEq by simp_all
  show ?case unfolding ev_GreaterEq aval.simps
    by (rule of_bool_option_sound) (use h1 h2 is_empty_correct lt_sound[OF _ h1 h2] in auto)
next
  case (NotEq e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using NotEq by simp_all
  show ?case unfolding ev_NotEq aval.simps
    by (rule of_bool_option_sound) (use h1 h2 is_empty_correct eqb_sound[OF _ h1 h2] in auto)
next
  case (Eq e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using Eq by simp_all
  show ?case unfolding ev_Eq aval.simps
    by (rule of_bool_option_sound) (use h1 h2 is_empty_correct eqb_sound[OF _ h1 h2] in auto)
next
  case (Not e)
  have h: "\<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e sigma)" using Not by simp
  show ?case unfolding ev_Not aval.simps
    by (rule of_bool_option_sound) (use h is_empty_correct tobool_sound[OF _ h] in auto)
next
  case (And e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using And by simp_all
  show ?case unfolding ev_And aval.simps
    by (rule of_bool_option_sound)
       (use h1 h2 is_empty_correct
          and_opt_sound[OF _ tobool_sound[OF _ h1] tobool_sound[OF _ h2]] in auto)
next
  case (Or e1 e2)
  have h1: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e1 sigma)" and h2: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (ev e2 sigma)"
    using Or by simp_all
  show ?case unfolding ev_Or aval.simps
    by (rule of_bool_option_sound)
       (use h1 h2 is_empty_correct
          or_opt_sound[OF _ tobool_sound[OF _ h1] tobool_sound[OF _ h2]] in auto)
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

lemma of_bool_option_mono:
  assumes "E2 \<Longrightarrow> E1" and "\<And>b. \<not> E1 \<Longrightarrow> r2 = Some b \<Longrightarrow> r1 = Some b"
  shows "(if E1 then bot else of_bool_option lit r1) \<le> (if E2 then bot else of_bool_option lit r2)"
  using assms by (cases r1; cases r2) auto

lemma aval_dom_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> ev a sigma1 \<le> ev a sigma2"
proof (induction a arbitrary: sigma1 sigma2)
  case (Less e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Less by simp_all
  show ?case unfolding ev_Less
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ p q] in auto)
next
  case (LessEq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using LessEq by simp_all
  show ?case unfolding ev_LessEq
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ q p] in auto)
next
  case (Greater e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Greater by simp_all
  show ?case unfolding ev_Greater
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ q p] in auto)
next
  case (GreaterEq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using GreaterEq by simp_all
  show ?case unfolding ev_GreaterEq
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] lt_mono[OF _ _ p q] in auto)
next
  case (NotEq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using NotEq by simp_all
  show ?case unfolding ev_NotEq
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] eqb_mono[OF _ _ p q] in auto)
next
  case (Eq e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Eq by simp_all
  show ?case unfolding ev_Eq
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q] eqb_mono[OF _ _ p q] in auto)
next
  case (Not e)
  have p: "ev e sigma1 \<le> ev e sigma2" using Not by simp
  show ?case unfolding ev_Not
    by (rule of_bool_option_mono) (use is_empty_antimono[OF p] tobool_mono[OF _ p] in auto)
next
  case (And e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using And by simp_all
  show ?case unfolding ev_And
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q]
          and_opt_mono[OF tobool_mono[OF _ p] tobool_mono[OF _ q]] in auto)
next
  case (Or e1 e2)
  have p: "ev e1 sigma1 \<le> ev e1 sigma2" and q: "ev e2 sigma1 \<le> ev e2 sigma2"
    using Or by simp_all
  show ?case unfolding ev_Or
    by (rule of_bool_option_mono)
       (use is_empty_antimono[OF p] is_empty_antimono[OF q]
          or_opt_mono[OF tobool_mono[OF _ p] tobool_mono[OF _ q]] in auto)
qed (auto simp add: le_funD)

end

end
