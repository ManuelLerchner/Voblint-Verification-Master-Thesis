theory Abstract_Arithmetic
  imports Abstract_Domain
begin

section \<open>Generic arithmetic-expression soundness\<close>

text \<open>
  Sign, Interval, and Parity each prove an \<open>aval_<dom>_sound\<close> lemma with the
  identical shape and proof script: structural induction on \<open>aexp\<close>,
  discharged by \<open>simp\<close> with exactly three per-operator soundness facts
  (\<open>plus_sound\<close>/\<open>minus_sound\<close>/\<open>times_sound\<close>) plus one literal-soundness fact.
  The per-operator facts themselves are genuinely domain-specific -- each
  domain's own case-split proof over its own representation -- so this
  locale does not try to share those. What it shares is the one induction
  that combines them, mirroring Goblint's \<open>ArithIkind\<close> numeric subset
  (\<open>plus\<close>/\<open>minus\<close>/\<open>times\<close>) as a locale rather than a type class: the
  arithmetic operators are already ordinary \<open>plus\<close>/\<open>minus\<close>/\<open>times\<close>
  instances per domain, so this locale only adds the soundness \<^emph>\<open>contract\<close>
  those instances must satisfy, not new operations.

  \<open>ev\<close> and \<open>lit\<close> are locale parameters, not derived: interpreting this
  locale at a domain's own \<open>aval_<dom>\<close> and literal-embedding function
  (\<open>sign_of_int\<close>, \<open>parity_of_int\<close>, or an inline \<open>\<lambda>n. Ivl (Fin n) (Fin n)\<close>
  for Interval, which has no separately named one) keeps every existing
  call site of \<open>aval_<dom>\<close> untouched -- the shared \<open>aval_dom_sound\<close> lemma
  below is stated over the same externally-fixed function, not a
  locale-internal reconstruction of it.
\<close>

locale arith_domain_sound =
  fixes ev :: "aexp \<Rightarrow> (vname \<Rightarrow> 'a::{sound_domain,plus,minus,times}) \<Rightarrow> 'a"
    and lit :: "int \<Rightarrow> 'a"
  assumes ev_N[simp]: "ev (N n) sigma = lit n"
    and ev_V[simp]: "ev (V x) sigma = sigma x"
    and ev_Plus[simp]: "ev (Plus e1 e2) sigma = ev e1 sigma + ev e2 sigma"
    and ev_Minus[simp]: "ev (Minus e1 e2) sigma = ev e1 sigma - ev e2 sigma"
    and ev_Times[simp]: "ev (Times e1 e2) sigma = ev e1 sigma * ev e2 sigma"
    and lit_sound[simp]: "n \<in> gamma (lit n)"
    and plus_sound[intro]: "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i + j \<in> gamma (p + q)"
    and minus_sound[intro]: "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i - j \<in> gamma (p - q)"
    and times_sound[intro]: "i \<in> gamma (p::'a) \<Longrightarrow> j \<in> gamma q \<Longrightarrow> i * j \<in> gamma (p * q)"
    and plus_mono[intro]: "p1 \<le> (p2::'a) \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> p1 + q1 \<le> p2 + q2"
    and minus_mono[intro]: "p1 \<le> (p2::'a) \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> p1 - q1 \<le> p2 - q2"
    and times_mono[intro]: "p1 \<le> (p2::'a) \<Longrightarrow> q1 \<le> q2 \<Longrightarrow> p1 * q1 \<le> p2 * q2"
begin

lemma aval_dom_sound:
  "(\<forall>x. s x \<in> gamma (sigma x)) \<Longrightarrow> aval a s \<in> gamma (ev a sigma)"
  apply (induction a arbitrary: s sigma)
  by(auto)

lemma aval_dom_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> ev a sigma1 \<le> ev a sigma2"
  apply (induction a arbitrary: sigma1 sigma2)
  by (auto simp add:le_funD)
     
end

end
