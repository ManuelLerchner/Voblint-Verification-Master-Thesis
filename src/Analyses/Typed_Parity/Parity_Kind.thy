theory Parity_Kind
  imports "Voblint_Analysis_Parity.Parity_Domain" "Voblint_Typed_Nonrel.Typed_Nonrel_Analysis"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Parity at a kind\<close>

text \<open>
  Normalizing to a kind changes a value by a multiple of \<open>2 ^ w\<close>, which is even, so
  every operation keeps its parity across a wraparound (\<open>parity_cast_sound\<close>). The
  typed operations are therefore the mathematical ones. Every kind's range holds an
  even and an odd value, so a parity meets the range exactly when it is not bottom, and
  no parity other than bottom bounds a value to a kind. Parity has no Goblint
  counterpart.
\<close>

instantiation parity :: ik_domain
begin

definition widen_ik_parity :: "ikind \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity" where
  "widen_ik_parity k a b = a \<squnion> b"

definition narrow_ik_parity :: "ikind \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity" where
  "narrow_ik_parity k a b = a \<sqinter> b"

definition empty_ik_parity :: "ikind \<Rightarrow> parity \<Rightarrow> bool" where
  "empty_ik_parity k a \<longleftrightarrow> a = PBot"

instance proof
  fix k :: ikind and a b :: parity
  show "a \<le> widen_ik k a b" "b \<le> widen_ik k a b" by (simp_all add: widen_ik_parity_def)
  show "b \<le> a \<Longrightarrow> b \<le> narrow_ik k a b" "b \<le> a \<Longrightarrow> narrow_ik k a b \<le> a"
    by (simp_all add: narrow_ik_parity_def inf_absorb2)
  show "empty_ik k a \<longleftrightarrow> numeric_domain_class.gamma a \<inter> ik_range k = {}"
  proof (cases a)
    case PEven then show ?thesis
      by (simp add: empty_ik_parity_def disjoint_iff) (rule exI[of _ 0], simp)
  next
    case POdd then show ?thesis
      using one_in_ik_range[of k]
      by (simp add: empty_ik_parity_def disjoint_iff del: one_in_ik_range) (rule exI[of _ 1], simp)
  next
    case PTop then show ?thesis
      by (simp add: empty_ik_parity_def) (metis zero_in_ik_range empty_iff)
  qed (simp add: empty_ik_parity_def)
qed

end

fun parity_aop :: "aop \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity" where
  "parity_aop AAdd a b = a + b"
| "parity_aop ASub a b = a - b"
| "parity_aop AMul a b = a * b"
| "parity_aop ADiv a b = parity_div a b"
| "parity_aop AMod a b = parity_mod a b"

lemma parity_aop_sound:
  "m \<in> gamma_parity a \<Longrightarrow> n \<in> gamma_parity b \<Longrightarrow> aop_eval op m n \<in> gamma_parity (parity_aop op a b)"
  by (cases op) (simp_all add: parity_plus_sound parity_minus_sound parity_times_sound
      parity_div_sound parity_mod_sound)


instantiation parity :: kind_int_domain
begin

definition top_ik_parity :: "ikind \<Rightarrow> parity" where "top_ik_parity k = PTop"

definition of_int_ik_parity :: "ikind \<Rightarrow> int \<Rightarrow> parity" where
  "of_int_ik_parity k n = parity_of_int (ik_norm k n)"

definition cast_ik_parity :: "signed_overflow_policy \<Rightarrow> ikind option \<Rightarrow> ikind \<Rightarrow> parity \<Rightarrow> parity" where
  "cast_ik_parity ovp sk k a = a"

definition arith_ik_parity :: "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> bool \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity" where
  "arith_ik_parity ovp k op fits = parity_aop op"

definition cmp_ik_parity :: "cop \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> bool option" where
  "cmp_ik_parity = cop_of parity_lt parity_eqb"

definition meet_ik_parity :: "parity \<Rightarrow> parity \<Rightarrow> parity" where
  "meet_ik_parity a b = a \<sqinter> b"

definition refine_ik_parity :: "cop \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity \<times> parity" where
  "refine_ik_parity c a b = (if c = CEq then (a \<sqinter> b, a \<sqinter> b) else (a, b))"

definition raw_aop_ik_parity :: "aop \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity" where
  "raw_aop_ik_parity = parity_aop"

definition fits_ik_parity :: "ikind \<Rightarrow> parity \<Rightarrow> bool" where
  "fits_ik_parity k a \<longleftrightarrow> a = PBot"

definition answer_ik_parity :: "parity \<Rightarrow> answer" where
  "answer_ik_parity a = answer_with (int_parity_update (\<lambda>_. a))"

definition of_answer_ik_parity :: "ikind option \<Rightarrow> answer \<Rightarrow> parity" where
  "of_answer_ik_parity sk q = (case q of QBot \<Rightarrow> \<bottom> | QTop \<Rightarrow> \<top> | QLifted d \<Rightarrow> int_parity d)"

instance proof
  fix n m :: int and k :: ikind and a b :: parity and op :: aop and c :: cop and r :: bool
  show "n \<in> ik_range k \<Longrightarrow> n \<in> numeric_domain_class.gamma (top_ik k :: parity)"
    by (simp add: top_ik_parity_def)
  show "ik_norm k n \<in> numeric_domain_class.gamma (of_int_ik k n :: parity)"
    by (simp add: of_int_ik_parity_def parity_of_int_gamma)
  show "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> numeric_domain_class.gamma a
      \<Longrightarrow> ik_norm k n \<in> numeric_domain_class.gamma (cast_ik ovp sk k a)" for ovp sk
    by (simp add: cast_ik_parity_def parity_cast_sound)
  show "(fits \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k) \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> numeric_domain_class.gamma (arith_ik ovp k op fits a b)" for ovp fits
    by (simp add: arith_ik_parity_def parity_cast_sound parity_aop_sound)
  show "cmp_ik c a b = Some r \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> cop_eval c m n = r"
    unfolding cmp_ik_parity_def by simp (rule cop_of_sound[OF parity_lt_sound parity_eqb_sound])
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> m \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (meet_ik a b)"
    by (simp add: meet_ik_parity_def)
  show "cop_eval c m n \<Longrightarrow> m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (fst (refine_ik c a b))
        \<and> n \<in> numeric_domain_class.gamma (snd (refine_ik c a b))"
    by (cases c) (simp_all add: refine_ik_parity_def)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> aop_eval op m n \<in> numeric_domain_class.gamma (raw_aop_ik op a b)"
    by (simp add: raw_aop_ik_parity_def parity_aop_sound)
  show "fits_ik k a \<Longrightarrow> n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> ik_range k"
    by (simp add: fits_ik_parity_def)
  show "n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    by (simp add: answer_ik_parity_def gamma_int_dom_def top_int_dom_ext_def gamma_sign_top
        gamma_parity_top top_ivl_def gamma_ivl_top)
  show "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
      \<Longrightarrow> n \<in> numeric_domain_class.gamma (of_answer_ik sk q :: parity)" for sk q
    by (cases q)
      (simp_all add: of_answer_ik_parity_def gamma_int_dom_def gamma_sign_top gamma_parity_top)
qed

end

declare [[code abort: gamma_parity]]

subsection \<open>Executed\<close>

text \<open>A step of \<open>2\<close> from \<open>0\<close> keeps \<open>x\<close> even at \<^const>\<open>U8\<close>, across every wraparound.\<close>

definition parity_prog :: imp_prog where
  "parity_prog = program {
     fun f() { x = 0; while (x != 7) { x = x + 2; } }
     fun main() { f(); } }"

lemma parity_value:
  "typed_nonrel.state_at default_sem_conf [(ScopedId (STR ''f'') (STR ''x''), U8)] 0 Globals_Join tglobal parity_prog []
     (Statement 1) (ScopedId (STR ''f'') (STR ''x''))
     = KD U8 PEven"
  by eval

end
