theory Abstract_Domain
  imports "TD.Update_rules"
begin

hide_const (open) Update_rules.N

unbundle lattice_syntax

section \<open>Abstract value domains\<close>

text \<open>
  An executable domain supplies the required lattice operations and an exact
  emptiness test. Sound domains add a concretization into integers. The
  widening and narrowing the solver applies come from the vendored
  \<open>warrowing\<close> class, required as \<open>bounded_warrowing\<close> below. Abstract states and
  control-flow reachability are separate modules.
\<close>

subsection \<open>Executable and sound domains\<close>

class executable_domain = bounded_semilattice_sup_bot + order_top +
  fixes is_empty :: "'a \<Rightarrow> bool"
  fixes to_string :: "'a \<Rightarrow> String.literal"

class numeric_domain = executable_domain +
  fixes gamma :: "'a \<Rightarrow> int set" ("\<gamma>")
  assumes gamma_bot[simp]: "\<gamma> \<bottom> = {}"
  assumes gamma_top[simp]: "\<gamma> \<top> = UNIV"
  assumes gamma_mono: "a \<le> b \<Longrightarrow> \<gamma> a \<subseteq> \<gamma> b"
  assumes is_empty_correct: "is_empty a \<longleftrightarrow> \<gamma> a = {}"

text \<open>
  \<open>executable_domain\<close> carries exactly the executable per-element operations a
  concrete domain's runtime representation needs: the lattice structure,
  \<open>is_empty\<close> (a finite decision procedure on every real instance
  -- Interval's bound comparison, Sign's constructor match, ...), and
  \<open>to_string\<close> for reporting a solved value back to a caller. \<open>numeric_domain\<close>
  extends it with \<open>gamma\<close>, which is not executable in general (an infinite
  \<^typ>\<open>int set\<close>) and exists purely to state and prove soundness. Splitting the
  class this way keeps \<open>gamma\<close> out of the type-class dictionary that code
  generation must materialize for any constant that only needs \<open>is_empty\<close>
  (the finite witness-bottom tests over a resolved state, in
  particular): requesting \<open>'a::executable_domain\<close> there never drags \<^const>\<open>gamma\<close>'s
  code equation into the dependency closure, even though every
  \<^class>\<open>numeric_domain\<close> instance is automatically a \<^class>\<open>executable_domain\<close>
  instance too.
\<close>

text \<open>
  \<open>is_empty\<close> is a semantic classifier, not a structural equality
  test against \<open>bot\<close>: it mirrors Goblint's own \<open>Lattice.Bot\<close>
  signature (@{url "https://github.com/goblint/analyzer/blob/master/src/domain/lattice.ml"}):
  \<open>val is_bot: t -> bool\<close> is a per-domain operation there too, not a
  generic derived test. Goblint's own default implementation (\<open>IntDomain0.Std\<close>
  in
  @{url "https://github.com/goblint/analyzer/blob/master/src/cdomain/value/cdomains/intDomain0.ml"})
  in fact defines it as structural equality against one canonical \<open>bot_of\<close>
  value, since most of its domains keep a single bottom representation
  (Interval's \<open>bot () = None\<close>, normalized on every operation). Voblint
  cannot take that shortcut: some Voblint domains admit representations with
  more than one empty-denoting value that are never normalized away
  (Interval's inverted bound pairs, e.g. \<^term>\<open>Ivl (Fin 5) (Fin (-1))\<close>, none
  of them favored over \<open>bot\<close> itself), so \<open>a = bot\<close> would silently miss some
  of them. Fixing \<open>is_empty\<close> as its own class operation, correct against
  \<^const>\<open>gamma\<close> rather than against \<^const>\<open>bot\<close>, makes every
  \<^class>\<open>numeric_domain\<close> instance responsible for its own exact emptiness
  test, the same obligation every domain already carries for
  \<^const>\<open>gamma\<close> itself. The lattice constant \<open>bot\<close> stays the canonical
  representative; \<open>is_empty\<close> answers a different question (what a
  value denotes), and a proof that genuinely needs the canonical element
  still writes \<open>a = bot\<close> directly.
\<close>

subsection \<open>Concretization bounds\<close>

lemma gamma_sup_ub1[intro]: "\<gamma> a \<subseteq> \<gamma> (a \<squnion> b)" for a b :: "'a::numeric_domain"
  by (rule gamma_mono[OF sup_ge1])

lemma gamma_sup_ub2[intro]: "\<gamma> b \<subseteq> \<gamma> (a \<squnion> b)" for a b :: "'a::numeric_domain"
  by (rule gamma_mono[OF sup_ge2])

text \<open>
  Emptiness is downward closed under the abstract order: it follows from
  \<open>gamma_mono\<close> alone, with no per-domain fact needed. This is what lets the
  generic transfer dispatcher's short-circuit stay monotone: a smaller input
  can only be witness-empty \<^emph>\<open>more\<close> often than a larger one, never less.
\<close>
lemma is_empty_antimono:
  "a \<le> b \<Longrightarrow> is_empty b \<Longrightarrow> is_empty a" for a b :: "'a::numeric_domain"
  using gamma_mono unfolding is_empty_correct by blast

subsection \<open>Domains with widening\<close>

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

subsection \<open>Printing values\<close>

text \<open>
  How a solved value is shown, following Goblint's notation (\<open>1+3\<int>\<close>, \<open>\<top>\<close>,
  \<open>\<bottom>\<close>). Nothing is proved about it: it is not part of any soundness claim.

  A \<^typ>\<open>String.literal\<close> holds ASCII only, so a mathematical symbol is written
  as its Isabelle symbol name without the backslash --- \<open><int>\<close> for \<open>\<int>\<close> --- and
  the CLI decodes these tokens into Unicode before rendering. No variable name,
  numeral or bracket a printer emits contains \<open><\<close>, so the tokens are unambiguous.
\<close>

abbreviation (input) sym_bottom :: String.literal where "sym_bottom \<equiv> STR ''<bottom>''"
abbreviation (input) sym_top :: String.literal where "sym_top \<equiv> STR ''<top>''"
abbreviation (input) sym_int :: String.literal where "sym_int \<equiv> STR ''<int>''"
abbreviation (input) sym_infinity :: String.literal where "sym_infinity \<equiv> STR ''<infinity>''"
abbreviation (input) sym_le :: String.literal where "sym_le \<equiv> STR ''<le>''"
abbreviation (input) sym_ge :: String.literal where "sym_ge \<equiv> STR ''<ge>''"
abbreviation (input) sym_and :: String.literal where "sym_and \<equiv> STR ''<and>''"

fun string_of_nat :: "nat \<Rightarrow> String.literal" where
  "string_of_nat n =
     (if n < 10 then String.implode [char_of (n + 48)]
      else string_of_nat (n div 10) + String.implode [char_of (n mod 10 + 48)])"

definition string_of_int :: "int \<Rightarrow> String.literal" where
  "string_of_int i =
     (if i < 0 then STR ''-'' + string_of_nat (nat (- i))
      else string_of_nat (nat i))"

end

