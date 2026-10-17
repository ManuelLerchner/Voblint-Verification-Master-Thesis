theory Backward_Domain
  imports Nonrelational_Reachability Forward_Domain
begin

section \<open>Inverse operators for refining against a guard\<close>

text \<open>
  A forward transfer over-approximates what an assignment does; a backward one narrows
  values against a condition that is known to hold, which is what a branch on \<open>b\<close>
  learns about the stores that pass it. The interface a domain supplies for that is
  a set of inverse operators for arithmetic and comparison (\<open>inv_less\<close>,
  \<open>inv_plus\<close>, ...), each sound in the sense that every concrete pair the operator
  admits before the operation is still admitted after narrowing.
  This abstracts the backward-refinement operations Goblint's \<open>BaseInvariant\<close> implements
  concretely for its Base analysis; Goblint has no generic module signature this locale
  is a formalization of.
\<close>

subsection \<open>Backward-analysis locale\<close>

text \<open>
  A semantic intersection preserves every concrete value shared by both
  operands and lies below both. It need not be the lattice infimum: a domain
  may normalize an empty result while its representation order still
  distinguishes several empty elements. The lower bounds make every refinement
  step reductive. Every domain's intersection has both, so they form one
  contract; \<open>mono_intersection\<close> adds monotonicity as a separate
  strengthening.
\<close>

locale sound_intersection =
  fixes intersect :: "'a::numeric_domain => 'a => 'a"
  assumes intersect_sound[intro]:
    "n \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> n \<in> \<gamma> (intersect a b)"
    and intersect_reductive1[intro]: "intersect a b \<le> a"
    and intersect_reductive2[intro]: "intersect a b \<le> b"

text \<open>
  Monotone intersection is a separate layer for the same reason as in the forward
  interfaces: soundness needs only \<open>sound_intersection\<close>, while the solver's
  least-solution theorem asks \<open>intersect\<close> to preserve the order in both arguments.
\<close>

locale mono_intersection = sound_intersection +
  assumes intersect_mono[intro]:
    "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> intersect a1 b1 \<le> intersect a2 b2"

text \<open>
  The inverse operators work on abstract values alone: given the result an
  operation must have produced, each narrows its operands to values that still
  admit every concrete pair producing it. \<open>sound_inverse_ops\<close> states them and their
  soundness with no state in sight, which is all the derived numeric queries
  (\<open>Backward_Numeric_Queries\<close>) read.
\<close>

locale sound_inverse_ops = sound_intersection intersect
  for intersect :: "'a::numeric_domain => 'a => 'a" +
  fixes
    inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_eq    :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
  assumes
      inv_less_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> (n1 < n2) = res
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_less res a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_less res a1 a2))"
    and inv_eq_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> (n1 = n2) = res
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_eq res a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_eq res a1 a2))"
    and inv_plus_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 + n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_plus r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_plus r a1 a2))"
    and inv_minus_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 - n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_minus r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_minus r a1 a2))"
    and inv_times_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 * n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_times r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_times r a1 a2))"
begin

text \<open>
  Projections of the five \<open>inv_*_sound\<close> assumptions above, one membership
  fact per operand instead of the pair conjunction the raw assumption gives.
  These, not the raw assumptions, are the \<open>[intro]\<close> rules: their conclusion
  has a distinctive \<open>fst (inv_* ...)\<close>/\<open>snd (inv_* ...)\<close> head, so a goal of
  exactly that shape picks the matching rule directly, whereas the raw
  conjunction-valued assumption would leave automation to split a conjunction
  goal it did not ask for.
\<close>

lemmas inv_less_sound_fst [intro] = inv_less_sound[THEN conjunct1]
lemmas inv_less_sound_snd [intro] = inv_less_sound[THEN conjunct2]

lemmas inv_eq_sound_fst [intro] = inv_eq_sound[THEN conjunct1]
lemmas inv_eq_sound_snd [intro] = inv_eq_sound[THEN conjunct2]

lemmas inv_plus_sound_fst [intro] = inv_plus_sound[THEN conjunct1]
lemmas inv_plus_sound_snd [intro] = inv_plus_sound[THEN conjunct2]

lemmas inv_minus_sound_fst [intro] = inv_minus_sound[THEN conjunct1]
lemmas inv_minus_sound_snd [intro] = inv_minus_sound[THEN conjunct2]

lemmas inv_times_sound_fst [intro] = inv_times_sound[THEN conjunct1]
lemmas inv_times_sound_snd [intro] = inv_times_sound[THEN conjunct2]

end

subsection \<open>Conservative inverse operator\<close>

text \<open>
  A domain too coarse to invert an operator (e.g. sign, which cannot narrow
  either operand of a plus/minus/times from its result) instantiates that
  inverse with this shared no-op: both operands pass through unchanged. The
  first argument is the known result or truth value, so the same no-op serves
  the arithmetic inverses and the comparison inverses. Its soundness
  obligation unfolds to the operands' own membership, so each instance
  discharges it with \<open>inv_conservative_def\<close>.
\<close>

definition inv_conservative :: "'r => 'a => 'a => 'a * 'a" where
  "inv_conservative r a1 a2 = (a1, a2)"

end
