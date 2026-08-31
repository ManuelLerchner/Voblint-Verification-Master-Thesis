theory Abstract_Domain
  imports "TD.Update_rules"
begin

hide_const (open) Update_rules.N

unbundle lattice_syntax

section \<open>Abstract value domains\<close>

text \<open>
  An executable domain supplies the required lattice operations, an exact
  emptiness test, and an exact fullness test. Sound domains
  add a concretization into integers, while
  widening domains add the update operation required for infinite ascending
  chains. Abstract states and control-flow reachability are separate modules.
\<close>

subsection \<open>Executable and sound domains\<close>

class executable_domain = bounded_semilattice_sup_bot + order_top +
  fixes is_empty :: "'a \<Rightarrow> bool"
  fixes is_full :: "'a \<Rightarrow> bool"
  fixes to_string :: "'a \<Rightarrow> string"

class sound_domain = executable_domain +
  fixes gamma :: "'a \<Rightarrow> int set"
  assumes gamma_bot[simp]: "gamma bot = {}"
  assumes gamma_top[simp]: "gamma top = UNIV"
  assumes gamma_mono: "a \<le> b \<Longrightarrow> gamma a \<subseteq> gamma b"
  assumes is_empty_correct: "is_empty a \<longleftrightarrow> gamma a = {}"
  assumes is_full_correct: "is_full a \<longleftrightarrow> gamma a = UNIV"

text \<open>
  \<open>executable_domain\<close> carries exactly the executable per-element operations a
  concrete domain's runtime representation needs: the lattice structure plus
  \<open>is_empty\<close>/\<open>is_full\<close>, both finite decision procedures on every real instance
  (Interval's bound comparison, Sign's constructor match, ...). \<open>sound_domain\<close>
  extends it with \<open>gamma\<close>, which is not executable in general (an infinite
  \<^typ>\<open>int set\<close>) and exists purely to state and prove soundness. Splitting the
  class this way keeps \<open>gamma\<close> out of the type-class dictionary that code
  generation must materialize for any constant that only needs \<open>is_empty\<close>/
  \<open>is_full\<close> (the finite witness-bottom tests over a resolved state, in
  particular): requesting \<open>'a::executable_domain\<close> there never drags \<^const>\<open>gamma\<close>'s
  code equation into the dependency closure, even though every
  \<^class>\<open>sound_domain\<close> instance is automatically a \<^class>\<open>executable_domain\<close>
  instance too.
\<close>

text \<open>
  \<open>is_empty\<close>/\<open>is_full\<close> are semantic classifiers, not structural equality
  tests against \<open>bot\<close>/\<open>top\<close>: \<open>is_empty\<close> mirrors Goblint's own \<open>Lattice.Bot\<close>
  signature (@{url "https://github.com/goblint/analyzer/blob/master/src/domain/lattice.ml"}):
  \<open>val is_bot: t -> bool\<close> is a per-domain operation there too, not a
  derived equality test against one canonical bottom value. The reason is
  the same in both codebases: many domains have representations with more
  than one empty- or full-denoting value (Interval's inverted bound pairs, e.g.
  \<^term>\<open>Ivl (Fin 5) (Fin (-1))\<close>, none of them favored over \<open>bot\<close> itself),
  so \<open>a = bot\<close> would silently miss some of them, and symmetrically for
  \<open>a = top\<close> and full concretizations. Fixing \<open>is_empty\<close>/\<open>is_full\<close> as their
  own class operations, correct against \<^const>\<open>gamma\<close> rather than against
  \<^const>\<open>bot\<close>/\<^const>\<open>top\<close>, makes every \<^class>\<open>sound_domain\<close> instance responsible
  for its own exact emptiness and fullness tests, the same obligation every
  domain already carries for \<^const>\<open>gamma\<close> itself. The lattice constants
  \<open>bot\<close>/\<open>top\<close> stay the canonical representatives; \<open>is_empty\<close>/\<open>is_full\<close> answer
  a different question (what a value denotes), and a proof that genuinely
  needs the canonical element still writes \<open>a = bot\<close>/\<open>a = top\<close> directly.
\<close>

subsection \<open>Concretization bounds\<close>

lemma gamma_sup_ub1[intro]: "gamma a \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  by (rule gamma_mono[OF sup_ge1])

lemma gamma_sup_ub2[intro]: "gamma b \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  by (rule gamma_mono[OF sup_ge2])

lemma gamma_sup_sound: "gamma a \<union> gamma b \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  using gamma_sup_ub1 gamma_sup_ub2 by blast

text \<open>
  Emptiness is downward closed under the abstract order, and fullness is
  upward closed: both follow from \<open>gamma_mono\<close> alone, with no per-domain fact
  needed. This is what lets the generic transfer dispatcher's short-circuit
  stay monotone: a smaller input can only be witness-empty \<^emph>\<open>more\<close> often than
  a larger one, never less; symmetrically, a larger input can only be
  witness-full \<^emph>\<open>more\<close> often than a smaller one.
\<close>
lemma is_empty_antimono:
  "a \<le> b \<Longrightarrow> is_empty b \<Longrightarrow> is_empty a" for a b :: "'a::sound_domain"
  by (metis bot.extremum_uniqueI gamma_mono is_empty_correct)

lemma is_full_mono:
  "a \<le> b \<Longrightarrow> is_full a \<Longrightarrow> is_full b" for a b :: "'a::sound_domain"
  by (metis gamma_mono is_full_correct subset_UNIV subset_antisym)

subsection \<open>Domains with widening\<close>

text \<open>
  Widening belongs to the value domain because it approximates joins in that
  domain. Finite domains instantiate it with join; infinite domains may use a
  coarser extrapolation. \<open>executable_widening_domain\<close> keeps widening on the
  executable side, so generated code that only needs \<open>\<nabla>\<close> is never forced to
  request \<open>gamma\<close> through \<open>widening_domain\<close>.
\<close>

class executable_widening_domain = executable_domain + widening

class widening_domain = sound_domain + executable_widening_domain

lemma widen_ub1[intro]: "gamma a \<subseteq> gamma (a \<nabla> b)" for a b :: "'a::widening_domain"
  by (rule gamma_mono[OF widen_ge1])

lemma widen_ub2[intro]: "gamma b \<subseteq> gamma (a \<nabla> b)" for a b :: "'a::widening_domain"
  by (rule gamma_mono[OF widen_ge2])

text \<open>The vendored solver states its combined update rule over a bounded
  semilattice carrying both widening and narrowing.\<close>

class bounded_warrowing = bounded_semilattice_sup_bot + warrowing

text \<open>
  \<open>warrow\<close> is deliberately not join-like: it takes the narrowing branch
  whenever \<open>b \<le> a\<close>, and narrowing moves the result down toward \<open>b\<close>, not up
  past \<open>a\<close>, so no \<open>a \<le> a \<nabla>\<Delta> b\<close> counterpart to \<open>warrowing_properties\<close> holds
  in general. What does hold unconditionally in that regime is the matching
  upper bound on the \<open>a\<close> side, \<open>warrow_le_when_le\<close>, together with
  \<open>warrowing_properties\<close>' \<open>b \<le> a \<nabla>\<Delta> b\<close> that gives the full sandwich
  \<open>b \<le> a \<nabla>\<Delta> b \<le> a\<close>. \<open>warrow_idem\<close> is the fixpoint case of that sandwich.
\<close>

lemma warrow_idem: "a \<nabla>\<Delta> a = a" for a :: "'a::warrowing"
  unfolding warrow_def using narrow_ge[of a a] narrow_le[of a a] by (auto intro: order.antisym)

lemma warrow_le_when_le: "b \<le> a \<Longrightarrow> a \<nabla>\<Delta> b \<le> a" for a b :: "'a::warrowing"
  unfolding warrow_def using narrow_le by simp

end

