theory Abstract_Domain
  imports "Voblint_VIMP.VIMP_Syntax" "Voblint_VIMP.VIMP_Expr" "TD.Update_rules"
    "HOL-Library.Monad_Syntax"
begin

hide_const (open) Update_rules.N

unbundle lattice_syntax

section \<open>Abstract domain: locale and lifted state concretization\<close>

text \<open>
  An abstract domain is a type 'a equipped with:
    bot     : bottom element (empty concretization)
    sup     : sound upper bound (for RHS fold over predecessor edges)
    widen   : widening operator (ensures termination)
    \<gamma>   : concretization map  'a => int set

  bot and sup come from the bounded_semilattice_sup_bot type class.
  'a abs_state = vname => 'a inherits the same class pointwise via HOL's
  fun instances, so we never need to define lifted-bot / lifted-join.
\<close>

type_synonym 'a abs_state = "vname => 'a"

(* HOL ships fun :: (type, bounded_lattice) bounded_lattice but not this
   weaker pointwise instance; abs_state needs it for TD_side part_post_solution. *)
instance "fun" :: (type, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

(* Helper exposed globally: sup over any semilattice_sup is comp_fun_commute.
   Available to downstream proofs that thread mem_image_le_fold etc. *)
lemma comp_fun_commute_sup:
  "comp_fun_commute ((\<squnion>) :: 'a::semilattice_sup \<Rightarrow> 'a \<Rightarrow> 'a)"
  by unfold_locales (simp add: fun_eq_iff sup_left_commute)

text \<open>Pointwise join on abstract states is idempotent because the value-domain
  semilattice structure lifts pointwise.  Finite folds can therefore use the
  standard idempotent-join laws without a separate state-level assumption.\<close>
lemma join_state_comp_fun_idem:
  "comp_fun_idem ((\<squnion>) ::
     'a::semilattice_sup abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  by (rule comp_fun_idem_sup)

subsection \<open>Sound-domain type class\<close>

class computable_domain = bounded_semilattice_sup_bot + order_top +
  fixes is_bot :: "'a \<Rightarrow> bool"
  fixes is_top :: "'a \<Rightarrow> bool"

class sound_domain = computable_domain +
  fixes gamma :: "'a \<Rightarrow> int set"
  assumes gamma_bot: "gamma bot = {}"
  assumes gamma_mono: "a \<le> b \<Longrightarrow> gamma a \<subseteq> gamma b"
  assumes is_bot_correct: "is_bot a \<longleftrightarrow> gamma a = {}"
  assumes is_top_correct: "is_top a \<longleftrightarrow> a = top"

text \<open>
  \<open>computable_domain\<close> carries exactly the executable per-element operations a
  concrete domain's runtime representation needs: the lattice structure plus
  \<open>is_bot\<close>/\<open>is_top\<close>, both finite decision procedures on every real instance
  (Interval's bound comparison, Sign's constructor match, ...). \<open>sound_domain\<close>
  extends it with \<open>gamma\<close>, which is not executable in general (an infinite
  \<^typ>\<open>int set\<close>) and exists purely to state and prove soundness. Splitting the
  class this way keeps \<open>gamma\<close> out of the type-class dictionary that code
  generation must materialize for any constant that only needs \<open>is_bot\<close>/
  \<open>is_top\<close> (the finite witness-bottom tests over a resolved state, in
  particular): requesting \<open>'a::computable_domain\<close> there never drags \<^const>\<open>gamma\<close>'s
  code equation into the dependency closure, even though every
  \<^class>\<open>sound_domain\<close> instance is automatically a \<^class>\<open>computable_domain\<close>
  instance too.
\<close>

text \<open>
  \<open>is_bot\<close> mirrors Goblint's own \<open>Lattice.Bot\<close> signature
  (@{url "https://github.com/goblint/analyzer/blob/master/src/domain/lattice.ml"}):
  \<open>val is_bot: t -> bool\<close> is a per-domain operation there too, not a
  derived equality test against one canonical bottom value. The reason is
  the same in both codebases: many domains have representations with more
  than one bottom-denoting value (Interval's inverted bound pairs, e.g.
  \<^term>\<open>Ivl (Fin 5) (Fin (-1))\<close>, none of them favored over \<open>bot\<close> itself),
  so \<open>a = bot\<close> would silently miss some of them. Fixing \<open>is_bot\<close> as its own
  class operation, correct against \<^const>\<open>gamma\<close> rather than against
  \<^const>\<open>bot\<close>, makes every \<^class>\<open>sound_domain\<close> instance responsible for
  its own exact emptiness test, the same obligation every domain already
  carries for \<^const>\<open>gamma\<close> itself.
\<close>

subsection \<open>Lifted concretization\<close>

definition gamma_state :: "('a::sound_domain) abs_state \<Rightarrow> store set" ("\<lbrakk>_\<rbrakk>") where
  "gamma_state \<sigma> = {s. \<forall>x. s x \<in> gamma (\<sigma> x)}"

(* Note: pointwise bot / sup on 'a abs_state come from HOL's
   fun :: bot and fun :: sup instances; no extra definitions needed. *)

subsection \<open>Derived gamma-sup bounds\<close>

lemma gamma_sup_ub1: "gamma a \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  by (rule gamma_mono[OF sup_ge1])

lemma gamma_sup_ub2: "gamma b \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  by (rule gamma_mono[OF sup_ge2])

lemma gamma_sup_sound: "gamma a \<union> gamma b \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  using gamma_sup_ub1 gamma_sup_ub2 by blast

subsection \<open>Lifted concretization lemmas\<close>

lemma gamma_state_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> \<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def le_fun_def
  using gamma_mono by blast

lemma gamma_state_bot:
  "\<lbrakk>bot :: 'a::sound_domain abs_state\<rbrakk> = {}"
  unfolding gamma_state_def bot_fun_def using gamma_bot by auto

lemma gamma_state_sup_ub1:
  "\<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub1 by blast

lemma gamma_state_sup_ub2:
  "\<lbrakk>sigma2\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub2 by blast

(* The pointwise projection gamma_state_def unfolds to; downstream proofs
   cite this instead of re-unfolding the definition at each site. *)
lemma gamma_stateD [dest]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<forall>x. s x \<in> gamma (\<sigma> x)"
  for \<sigma> :: "'a::sound_domain abs_state"
  unfolding gamma_state_def by simp

subsection \<open>Witness-bottom abstract states\<close>

text \<open>
  \<^const>\<open>gamma_state\<close> is a product concretization: \<open>\<sigma>\<close> denotes no concrete store the
  moment \<^emph>\<open>any single\<close> component is itself \<^const>\<open>is_bot\<close>, regardless of what the
  other components hold. \<open>is_bot_state\<close> (below) names this witness-bottom condition
  directly, so a generic transfer dispatcher can detect and canonicalize it without
  inspecting every component of \<open>\<sigma>\<close> against \<^const>\<open>gamma\<close>.
\<close>

definition is_bot_state :: "('a::sound_domain) abs_state \<Rightarrow> bool" where
  "is_bot_state \<sigma> = (\<exists>x. is_bot (\<sigma> x))"

lemma is_bot_stateI [intro]:
  "is_bot (\<sigma> x) \<Longrightarrow> is_bot_state \<sigma>"
  unfolding is_bot_state_def by (rule exI)

lemma is_bot_stateE [elim]:
  assumes "is_bot_state \<sigma>"
  obtains x where "is_bot (\<sigma> x)"
  using assms unfolding is_bot_state_def by blast

lemma is_bot_state_gamma_state_empty:
  assumes "is_bot_state \<sigma>"
  shows "gamma_state \<sigma> = {}"
proof -
  from assms obtain x where "is_bot (\<sigma> x)" by (rule is_bot_stateE)
  then have "gamma (\<sigma> x) = {}" by (simp add: is_bot_correct)
  then show ?thesis
    unfolding gamma_state_def by auto
qed

lemma gamma_state_empty_is_bot_state:
  assumes "gamma_state \<sigma> = {}"
  shows "is_bot_state \<sigma>"
proof (rule ccontr)
  assume "\<not> is_bot_state \<sigma>"
  then have nonempty: "\<And>x. \<exists>v. v \<in> gamma (\<sigma> x)"
    unfolding is_bot_state_def using is_bot_correct by blast
  define s where "s = (\<lambda>x. SOME v. v \<in> gamma (\<sigma> x))"
  have s_prop: "s x \<in> gamma (\<sigma> x)" for x
    unfolding s_def using nonempty[of x] by (rule someI_ex)
  then have "s \<in> gamma_state \<sigma>"
    unfolding gamma_state_def by simp
  with assms show False by simp
qed

lemma is_bot_state_iff_gamma_state_empty:
  "is_bot_state \<sigma> \<longleftrightarrow> gamma_state \<sigma> = {}"
  using is_bot_state_gamma_state_empty gamma_state_empty_is_bot_state by blast

lemma is_bot_state_bot [simp]:
  "is_bot_state (bot :: 'a::sound_domain abs_state)"
  unfolding is_bot_state_def bot_fun_def
  using is_bot_correct gamma_bot by blast

text \<open>
  A concrete witness rules out witness-bottom directly: the generic dispatcher's
  short-circuit condition can never fire on an abstract state some reachable
  concrete store still belongs to.
\<close>
lemma is_bot_state_witnessI:
  "s \<in> gamma_state \<sigma> \<Longrightarrow> \<not> is_bot_state \<sigma>"
  using is_bot_state_gamma_state_empty by blast

text \<open>
  Witness-bottom is downward closed under the abstract order: it follows from
  \<open>gamma_mono\<close> alone, with no per-domain fact needed. This is what lets the generic
  transfer dispatcher's short-circuit stay monotone: a smaller input can only be witness-
  bottom \<^emph>\<open>more\<close> often than a larger one, never less.
\<close>
lemma is_bot_mono:
  "a \<le> b \<Longrightarrow> is_bot b \<Longrightarrow> is_bot a" for a b :: "'a::sound_domain"
  using gamma_mono is_bot_correct by blast

lemma is_bot_state_mono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> is_bot_state \<sigma>2 \<Longrightarrow> is_bot_state \<sigma>1"
  for \<sigma>1 \<sigma>2 :: "'a::sound_domain abs_state"
  unfolding is_bot_state_def le_fun_def using is_bot_mono by blast

text \<open>
  A join operand that is already live keeps the join live, regardless of the
  other operand: its own nonempty \<^const>\<open>gamma_state\<close> only grows under
  \<open>\<squnion>\<close> (\<open>sup_ge1\<close> / \<open>sup_ge2\<close>), so \<open>is_bot_state_mono\<close> transports
  liveness upward. The contrapositive is what \<open>normalize_state\<close> (below)
  needs: only a join of two already-dead operands can stay dead.
\<close>

lemma is_bot_state_sup1: "is_bot_state (\<sigma> \<squnion> \<tau>) \<Longrightarrow> is_bot_state \<sigma>"
  for \<sigma> \<tau> :: "'a::sound_domain abs_state"
  using is_bot_state_mono[OF sup_ge1] .

lemma is_bot_state_sup2: "is_bot_state (\<sigma> \<squnion> \<tau>) \<Longrightarrow> is_bot_state \<tau>"
  for \<sigma> \<tau> :: "'a::sound_domain abs_state"
  using is_bot_state_mono[OF sup_ge2] .

subsection \<open>Canonical-bottom state reduction\<close>

text \<open>
  \<^typ>\<open>'a abs_state\<close> is a product lattice: many states denote the empty
  concretization (any state with an \<^const>\<open>is_bot\<close> component at some
  location), yet the pointwise order does not identify them with the single
  canonical \<^term>\<open>bot\<close> state. Plain pointwise \<open>\<squnion>\<close> can therefore
  \<^emph>\<open>resurrect\<close> two witness-bottom operands into a live result, when their
  witness locations differ: each operand's own live locations pass a nonempty
  \<^const>\<open>gamma\<close> through the join (\<open>gamma_sup_ub1\<close> /
  \<open>gamma_sup_ub2\<close>), even though every location the \<^emph>\<open>other\<close> operand
  independently narrowed to \<^const>\<open>is_bot\<close> is individually unrecoverable.
  \<open>normalize_state\<close> collapses every witness-bottom representative to
  the one canonical \<^term>\<open>bot\<close> state before such a join runs, so two states
  that each denote the empty set locally now compare equal (both
  \<^term>\<open>bot\<close>) and their join stays canonically empty too.
\<close>

definition normalize_state :: "('a::sound_domain) abs_state \<Rightarrow> 'a abs_state" where
  "normalize_state \<sigma> = (if is_bot_state \<sigma> then bot else \<sigma>)"

lemma normalize_state_le: "normalize_state \<sigma> \<le> \<sigma>"
  unfolding normalize_state_def by simp

lemma normalize_state_bot_state [simp]:
  "is_bot_state \<sigma> \<Longrightarrow> normalize_state \<sigma> = bot"
  unfolding normalize_state_def by simp

lemma normalize_state_not_bot_state [simp]:
  "\<not> is_bot_state \<sigma> \<Longrightarrow> normalize_state \<sigma> = \<sigma>"
  unfolding normalize_state_def by simp

lemma gamma_state_normalize_state [simp]:
  "gamma_state (normalize_state \<sigma>) = gamma_state \<sigma>"
  unfolding normalize_state_def
  by (cases "is_bot_state \<sigma>") (simp_all add: is_bot_state_gamma_state_empty gamma_state_bot)

lemma normalize_state_idem [simp]:
  "normalize_state (normalize_state \<sigma>) = normalize_state \<sigma>"
  unfolding normalize_state_def by simp

lemma normalize_state_bot [simp]:
  "normalize_state (bot :: 'a::sound_domain abs_state) = bot"
  by simp

lemma is_bot_state_normalize_state [simp]:
  "is_bot_state (normalize_state \<sigma>) = is_bot_state \<sigma>"
  using is_bot_state_iff_gamma_state_empty gamma_state_normalize_state by metis

lemma normalize_state_mono:
  "\<sigma> \<le> \<tau> \<Longrightarrow> normalize_state \<sigma> \<le> normalize_state \<tau>"
proof -
  assume le: "\<sigma> \<le> \<tau>"
  show ?thesis
  proof (cases "is_bot_state \<sigma>")
    case True
    then show ?thesis by simp
  next
    case False
    then have "\<not> is_bot_state \<tau>" using le is_bot_state_mono by blast
    with False le show ?thesis by simp
  qed
qed

text \<open>
  \<open>state_sup\<close> is the reduced join: normalize both operands to the
  canonical witness-bottom representative first, then join. Two states that
  are each individually dead now join to \<^term>\<open>bot\<close> instead of resurrecting
  each other's untouched live locations.
\<close>

definition state_sup :: "('a::sound_domain) abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "state_sup \<sigma> \<tau> = normalize_state \<sigma> \<squnion> normalize_state \<tau>"

lemma state_sup_sound1: "gamma_state \<sigma> \<subseteq> gamma_state (state_sup \<sigma> \<tau>)"
proof -
  have "gamma_state (normalize_state \<sigma>) \<subseteq> gamma_state (normalize_state \<sigma> \<squnion> normalize_state \<tau>)"
    by (rule gamma_state_sup_ub1)
  then show ?thesis unfolding state_sup_def by simp
qed

lemma state_sup_sound2: "gamma_state \<tau> \<subseteq> gamma_state (state_sup \<sigma> \<tau>)"
proof -
  have "gamma_state (normalize_state \<tau>) \<subseteq> gamma_state (normalize_state \<sigma> \<squnion> normalize_state \<tau>)"
    by (rule gamma_state_sup_ub2)
  then show ?thesis unfolding state_sup_def by simp
qed

lemma state_sup_mono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> \<tau>1 \<le> \<tau>2 \<Longrightarrow> state_sup \<sigma>1 \<tau>1 \<le> state_sup \<sigma>2 \<tau>2"
  unfolding state_sup_def using normalize_state_mono sup_mono by blast

lemma state_sup_least:
  assumes "\<sigma> \<le> u" and "\<tau> \<le> u"
  shows "state_sup \<sigma> \<tau> \<le> u"
proof -
  have "normalize_state \<sigma> \<le> u" using normalize_state_le assms(1) by (rule order_trans)
  moreover have "normalize_state \<tau> \<le> u" using normalize_state_le assms(2) by (rule order_trans)
  ultimately show ?thesis unfolding state_sup_def by (rule sup_least)
qed

lemma sup_fold_ge:
  fixes S :: "'a::bounded_semilattice_sup_bot set"
  assumes "finite S" and "x \<in> S"
  shows "x \<le> Finite_Set.fold (\<squnion>) bot S"
  using assms
proof (induct S rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert a F)
  have fold_ins: "Finite_Set.fold (\<squnion>) bot (insert a F)
      = a \<squnion> Finite_Set.fold (\<squnion>) bot F"
    by (metis (full_types) Sup_fin.eq_fold Sup_fin.insert finite.simps insert.hyps(1) insert_commute
        insert_not_empty)
  show ?case
  proof (cases "x = a")
    case True show ?thesis using True fold_ins by simp
  next
    case False
    then have "x \<in> F" using insert.prems by simp
    then have "x \<le> Finite_Set.fold (\<squnion>) bot F" by (rule insert.hyps(3))
    then show ?thesis using fold_ins le_supI2 by metis
  qed
qed

lemma gamma_abs_sup_set_ub:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> gamma x \<subseteq> gamma (Finite_Set.fold (\<squnion>) bot S)"
  for x :: "'a::sound_domain"
  using gamma_mono sup_fold_ge by auto

subsection \<open>Structural reachability lift (Goblint's \<open>Lift\<close>/\<open>Dom\<close>)\<close>

text \<open>
  Mirrors Goblint's lifted-domain construction
  (@{url \<open>https://github.com/goblint/analyzer/blob/master/src/framework/analyses.ml\<close>}):
  \<open>module Dom (LD: Lattice.S) = struct include Lattice.LiftConf (...) (LD) ... end\<close>, whose
  outer \<open>`Bot\<close> means dead code and whose \<open>unlift\<close> only accepts \<open>`Lifted x\<close>. Reachability is
  carried as an explicit tag on top of the analysis-local state, not rediscovered from the
  state's own contents. \<open>Bot\<close> mirrors Goblint's lifted \<open>`Bot\<close>; \<open>Lifted\<close> mirrors \<open>`Lifted\<close>.
  Goblint's lift also carries an outer \<open>`Top\<close> for its own pre-analysis bookkeeping; every
  @{class sound_domain} instance here already has its own \<open>top\<close>, so this lift stays
  two-valued. \<open>Bot\<close> is strictly below every \<open>Lifted a\<close> regardless of \<open>a\<close> -- including
  \<open>Lifted bot\<close> -- since dead-by-construction and reachable-but-locally-bottom are the two
  concepts this lift exists to keep separate.
\<close>
(* Quickcheck's narrowing plugin automatically derives narrowing-based
   counterexample-generation support for datatypes.

   For this lifted datatype, enabling the plugin leads to a duplicate fact
   declaration for `Abstract_Domain.arity_narrowing_lifted` when the datatype
   is used in our abstract-domain locale setup. The actual theorem proof may
   already be complete ("No subgoals!"); the failure happens afterwards while
   Isabelle registers the generated Quickcheck infrastructure.

   We therefore disable only the `quickcheck_narrowing` datatype plugin here.
   This does not affect the datatype itself, its induction/recursion rules,
   executable code, lattice/domain instances, or the abstract-domain
   narrowing operator `\<Delta>`. It only means that Quickcheck's narrowing backend
   is not generated automatically for `'a lifted`.
*)
datatype (plugins del: quickcheck_narrowing) 'a lifted =
  Bot | Lifted 'a

instantiation lifted :: (order) order
begin

fun less_eq_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> bool" where
  "less_eq_lifted Bot _ = True"
| "less_eq_lifted (Lifted _) Bot = False"
| "less_eq_lifted (Lifted a) (Lifted b) = (a \<le> b)"

definition less_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> bool" where
  "less_lifted x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a lifted"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_lifted_def by (rule refl)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) simp_all
qed

end

instantiation lifted :: (type) bot
begin
definition bot_lifted :: "'a lifted" where "bot_lifted = Bot"
instance ..
end

lemma bot_lifted_eq [simp]: "(bot :: 'a lifted) = Bot"
  unfolding bot_lifted_def by (rule refl)

instance lifted :: (order) order_bot
  by standard (simp add: bot_lifted_def)

instantiation lifted :: (semilattice_sup) semilattice_sup
begin

fun sup_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "sup_lifted Bot y = y"
| "sup_lifted x Bot = x"
| "sup_lifted (Lifted a) (Lifted b) = Lifted (a \<squnion> b)"

instance
proof
  fix x y z :: "'a lifted"
  show "x \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" by (cases x; cases y; cases z) simp_all
qed

end

text \<open>
  The vendored TD solver's own storage requires \<open>'d::bounded_semilattice_sup_bot\<close>
  (@{theory_text \<open>TD_side\<close>}'s \<open>T :: ('x,'g,'d::bounded_semilattice_sup_bot) eqsT\<close>).
  \<open>lifted\<close> already carries \<open>order_bot\<close> and \<open>semilattice_sup\<close> separately; this
  registers the combined class explicitly (Isabelle does not infer class
  membership from having both parents' instances alone), which is what lets a
  lifted payload -- e.g. \<open>'a abs_state lifted\<close> -- instantiate the solver's \<open>'d\<close>
  at all.
\<close>

instance lifted :: (semilattice_sup) bounded_semilattice_sup_bot ..

text \<open>
  The warrowing update rule needs \<^typ>\<open>'a lifted\<close> itself to carry \<open>widen\<close>/\<open>narrow\<close> once the
  executable trees it runs store a lifted payload. \<open>Bot\<close> keeps the same role here as in the
  \<open>sup\<close> instance above: a structural placeholder, neutral for \<open>widen\<close>/\<open>narrow\<close> against a
  \<open>Lifted\<close> operand, with only the \<open>Lifted\<close>/\<open>Lifted\<close> case deferring to the base domain's own
  operation. \<open>quickcheck_narrowing\<close> is disabled on the \<open>lifted\<close> datatype declaration above:
  Isabelle/HOL's own built-in \<open>narrowing\<close> class (for Quickcheck's narrowing-based counterexample
  search) collides with the vendored solver's \<open>narrowing\<close> class of the same base name, and the
  datatype package's default Quickcheck plugin registers an arity for \<open>lifted\<close> under that
  colliding name before this instantiation gets a chance to.
\<close>

instantiation lifted :: (widening) widening
begin

fun widen_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "widen_lifted Bot y = y"
| "widen_lifted x Bot = x"
| "widen_lifted (Lifted a) (Lifted b) = Lifted (a \<nabla> b)"

instance proof intro_classes
  fix x y :: "'a lifted"
  show "x \<le> x \<nabla> y" by (cases x; cases y) (simp_all add: widen_ge1)
  show "y \<le> x \<nabla> y" by (cases x; cases y) (simp_all add: widen_ge2)
qed

end

instantiation lifted :: (narrowing) narrowing
begin

fun narrow_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "narrow_lifted Bot y = Bot"
| "narrow_lifted (Lifted a) Bot = Bot"
| "narrow_lifted (Lifted a) (Lifted b) = Lifted (a \<Delta> b)"

instance proof intro_classes
  fix a b :: "'a lifted"
  show "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b"
    by (cases a; cases b) (simp_all add: narrow_ge)
  show "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a"
    by (cases a; cases b) (simp_all add: narrow_le)
qed

end

text \<open>
  Concretization and reachability are supplied generically, parametric in the payload's own
  \<open>gam\<close>/\<open>is_bot_pred\<close>, rather than as a fresh type class: at the \<open>abs_state lifted\<close>
  instantiation the payload's concretization is @{const gamma_state} (into @{typ \<open>store set\<close>}),
  which is a different codomain than @{class sound_domain}'s own per-element \<open>gamma\<close>
  (into @{typ \<open>int set\<close>}), so this cannot be phrased as a single class member.
\<close>

definition is_bot_lift :: "'a lifted \<Rightarrow> bool" where
  "is_bot_lift x = (x = Bot)"

lemma is_bot_lift_iff [simp]: "is_bot_lift x \<longleftrightarrow> x = Bot"
  unfolding is_bot_lift_def by (rule refl)

definition gamma_lift :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a lifted \<Rightarrow> 'b set" where
  "gamma_lift gam x = (case x of Bot \<Rightarrow> {} | Lifted a \<Rightarrow> gam a)"

lemma gamma_lift_Bot [simp]: "gamma_lift gam Bot = {}"
  unfolding gamma_lift_def by simp

lemma gamma_lift_Lifted [simp]: "gamma_lift gam (Lifted a) = gam a"
  unfolding gamma_lift_def by simp

text \<open>
  Concretization for a complete reconstructed lifted state: \<open>Bot\<close> denotes an
  unreachable program point and concretizes to no concrete state at all, while
  \<open>Lifted \<sigma>\<close> concretizes exactly as \<open>\<sigma>\<close> already does. Stating soundness against
  this -- rather than case-splitting \<open>Bot\<close>/\<open>Lifted\<close> at every use site -- makes the
  \<open>Bot\<close> case discharge itself: its premise \<open>s \<in> gamma_state_lift Bot\<close> is \<open>s \<in> {}\<close>,
  vacuously false.
\<close>

abbreviation gamma_state_lift :: "'a::sound_domain abs_state lifted \<Rightarrow> store set" where
  "gamma_state_lift \<equiv> gamma_lift gamma_state"

lemma gamma_lift_mono:
  fixes x y :: "'a::order lifted"
  assumes gam_mono: "\<And>a b. a \<le> b \<Longrightarrow> gam a \<subseteq> gam b"
    and le: "x \<le> y"
  shows "gamma_lift gam x \<subseteq> gamma_lift gam y"
  using le by (cases x; cases y) (auto simp: gam_mono)

text \<open>
  \<open>is_bot_state\<close>'s lifted counterpart: a solver-level \<open>Bot\<close> already means the
  point itself is unreachable, while \<open>Lifted \<sigma>\<close> defers to \<open>is_bot_state \<sigma>\<close>'s
  own product-emptiness witness -- one component of \<open>\<sigma>\<close> collapsing to bottom
  empties the whole point's concretization exactly as it does for a plain,
  unlifted \<^typ>\<open>'a abs_state\<close>. The iff below needs no new argument beyond
  \<open>is_bot_state_iff_gamma_state_empty\<close> and \<^const>\<open>gamma_lift\<close>'s own case
  split.
\<close>

fun is_bot_state_lift :: "'a::sound_domain abs_state lifted \<Rightarrow> bool" where
  "is_bot_state_lift Bot = True"
| "is_bot_state_lift (Lifted \<sigma>) = is_bot_state \<sigma>"

lemma is_bot_state_lift_iff:
  "is_bot_state_lift s \<longleftrightarrow> gamma_state_lift s = {}"
  by (cases s) (simp_all add: is_bot_state_iff_gamma_state_empty)

text \<open>
  \<open>bind_lift\<close> is the reachability monad's Kleisli bind, exactly \<^const>\<open>Option.bind\<close>'s
  shape with \<open>Bot\<close> for \<open>None\<close> and \<open>Lifted\<close> for \<open>Some\<close>: \<open>Bot\<close> in, \<open>Bot\<close> out, without ever
  calling \<open>f\<close> -- matching Goblint's \<open>unlift\<close> being called before dispatch rather than inside
  each analysis's \<open>assign\<close>/\<open>branch\<close>. \<open>normalize_lift\<close> is the one Voblint-specific piece:
  it turns a domain-produced witness-bottom raw result back into the canonical structural
  \<open>Bot\<close>, the counterpart of Goblint's transfer functions raising \<open>Deadcode\<close> when their own
  computation lands on bottom. \<open>transfer_lift\<close>/\<open>transfer_lift2\<close> compose the two: the shape
  every generic edge/combine dispatcher actually calls.
\<close>

fun bind_lift :: "'a lifted \<Rightarrow> ('a \<Rightarrow> 'b lifted) \<Rightarrow> 'b lifted" where
  "bind_lift Bot f = Bot"
| "bind_lift (Lifted a) f = f a"

lemma bind_lift_Bot [simp]: "bind_lift Bot f = Bot" by simp

lemma bind_lift_Lifted [simp]: "bind_lift (Lifted a) f = f a" by simp

text \<open>
  Registers \<^const>\<open>bind_lift\<close> under \<^const>\<open>Monad_Syntax.bind\<close>'s ad hoc overloading, so
  \<open>x >>= f\<close> and \<open>do { a <- x; f a }\<close> both parse to exactly \<open>bind_lift x f\<close> -- a pure
  syntax translation resolved at elaboration time, so every lemma about \<^const>\<open>bind_lift\<close>
  applies unchanged to code written with \<open>do\<close> notation. Registered here, immediately after
  \<^const>\<open>bind_lift\<close>'s definition, so the reachability monad's own combinators below can use
  \<open>do\<close> notation too.
\<close>

adhoc_overloading Monad_Syntax.bind == bind_lift

definition normalize_lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a lifted" where
  "normalize_lift is_bot_pred a = (if is_bot_pred a then Bot else Lifted a)"

lemma normalize_lift_bot [simp]: "is_bot_pred a \<Longrightarrow> normalize_lift is_bot_pred a = Bot"
  unfolding normalize_lift_def by simp

lemma normalize_lift_not_bot [simp]:
  "\<not> is_bot_pred a \<Longrightarrow> normalize_lift is_bot_pred a = Lifted a"
  unfolding normalize_lift_def by simp

definition transfer_lift ::
  "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a lifted \<Rightarrow> 'b lifted" where
  "transfer_lift is_bot_pred f x = do { a <- x; normalize_lift is_bot_pred (f a) }"

definition transfer_lift2 ::
  "('c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a lifted \<Rightarrow> 'b lifted \<Rightarrow> 'c lifted" where
  "transfer_lift2 is_bot_pred f x y =
     do { a <- x; b <- y; normalize_lift is_bot_pred (f a b) }"

lemma transfer_lift_Bot [simp]: "transfer_lift is_bot_pred f Bot = Bot"
  unfolding transfer_lift_def by simp

lemma transfer_lift_Lifted [simp]:
  "transfer_lift is_bot_pred f (Lifted a) = normalize_lift is_bot_pred (f a)"
  unfolding transfer_lift_def by simp

lemma transfer_lift2_Bot_left [simp]: "transfer_lift2 is_bot_pred f Bot y = Bot"
  unfolding transfer_lift2_def by simp

lemma transfer_lift2_Bot_right [simp]: "transfer_lift2 is_bot_pred f (Lifted a) Bot = Bot"
  unfolding transfer_lift2_def by simp

lemma transfer_lift2_Lifted [simp]:
  "transfer_lift2 is_bot_pred f (Lifted a) (Lifted b) = normalize_lift is_bot_pred (f a b)"
  unfolding transfer_lift2_def by simp

subsection \<open>Canonical deadness: no \<^const>\<open>Lifted\<close> payload is ever witness-bottom\<close>

text \<open>
  \<open>normalized_lift\<close> names the discipline every solver-facing lifted value is meant to
  keep: \<^const>\<open>Bot\<close> is the \<^emph>\<open>sole\<close> representation of "this program point denotes no
  concrete store" -- a \<^const>\<open>Lifted\<close> payload \<open>is_bot_pred\<close> still calls bottom is a
  representation the framework never lets escape a value-producing step, not a second,
  competing way to say the same thing. \<open>normalize_lift\<close>'s own \<open>if\<close> makes every one of
  its outputs self-normalized: the \<^const>\<open>Lifted\<close> branch only fires when \<open>is_bot_pred\<close>
  already said no. \<open>transfer_lift\<close>/\<open>transfer_lift2\<close> route every domain transfer step
  through exactly this \<open>if\<close>, so no transfer step can ever hand back a \<^const>\<open>Lifted\<close>
  payload \<open>is_bot_pred\<close> still calls bottom, regardless of what the pre-lift inputs
  looked like.

  The lemmas below extend this from a single transfer step to every other value-producing
  primitive a solver combines lifted values with: \<open>\<squnion>\<close> (joining several contributions at a
  program point) and \<open>\<nabla>\<Delta>\<close> (the warrowing update rule). Both need only that \<open>is_bot_pred\<close>
  itself is downward closed under the payload's order (\<open>mono\<close> below) -- exactly
  \<open>is_bot_mono\<close>'s shape at \<^class>\<open>sound_domain\<close>, or \<open>resolved_st_q_is_bot_for\<close>'s own
  monotonicity once bridged through \<open>fun_of_resolved_st_q_for_mono\<close> -- not any fact
  specific to how \<open>is_bot_pred\<close> itself is computed.
\<close>

definition normalized_lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lifted \<Rightarrow> bool" where
  "normalized_lift is_bot_pred x = (case x of Bot \<Rightarrow> True | Lifted a \<Rightarrow> \<not> is_bot_pred a)"

lemma normalized_lift_Bot [simp]: "normalized_lift is_bot_pred Bot"
  unfolding normalized_lift_def by simp

lemma normalized_lift_Lifted [simp]:
  "normalized_lift is_bot_pred (Lifted a) \<longleftrightarrow> \<not> is_bot_pred a"
  unfolding normalized_lift_def by simp

lemma normalize_lift_normalized:
  "normalized_lift is_bot_pred (normalize_lift is_bot_pred a)"
  unfolding normalize_lift_def by (cases "is_bot_pred a") simp_all

lemma transfer_lift_normalized:
  "normalized_lift is_bot_pred (transfer_lift is_bot_pred f x)"
  by (cases x) (simp_all add: transfer_lift_def normalize_lift_normalized)

lemma transfer_lift2_normalized:
  "normalized_lift is_bot_pred (transfer_lift2 is_bot_pred f x y)"
  by (cases x; cases y) (simp_all add: transfer_lift2_def normalize_lift_normalized)

text \<open>
  \<open>canonicalize_lift\<close> re-normalizes an already-lifted value against \<open>is_bot_pred\<close>: a
  \<^const>\<open>Lifted\<close> payload that has since become witness-bottom (e.g. read from a
  representation that does not itself carry the \<open>transfer_lift\<close> discipline) collapses
  to \<^const>\<open>Bot\<close>, exactly as if it had been produced by a transfer step in the first
  place. It is \<open>transfer_lift is_bot_pred id\<close>, not a new bottom test: reusing
  \<^const>\<open>transfer_lift\<close> at the identity function is what makes
  \<open>canonicalize_lift_normalized\<close> immediate from \<open>transfer_lift_normalized\<close> rather than
  a second proof of the same fact.
\<close>

definition canonicalize_lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "canonicalize_lift is_bot_pred = transfer_lift is_bot_pred id"

lemma canonicalize_lift_Bot [simp]: "canonicalize_lift is_bot_pred Bot = Bot"
  unfolding canonicalize_lift_def by simp

lemma canonicalize_lift_Lifted [simp]:
  "canonicalize_lift is_bot_pred (Lifted a) = normalize_lift is_bot_pred a"
  unfolding canonicalize_lift_def by simp

lemma canonicalize_lift_normalized:
  "normalized_lift is_bot_pred (canonicalize_lift is_bot_pred x)"
  unfolding canonicalize_lift_def by (rule transfer_lift_normalized)

text \<open>
  \<open>\<squnion>\<close> preserves \<open>normalized_lift\<close> from two already-normalized operands: \<^const>\<open>Bot\<close> is
  \<open>\<squnion>\<close>'s identity on \<^typ>\<open>'a lifted\<close> (\<open>sup_lifted.simps\<close>), so the only case needing
  \<open>mono\<close> at all is \<^const>\<open>Lifted\<close>/\<^const>\<open>Lifted\<close>, where \<open>sup_ge1\<close>/\<open>sup_ge2\<close> place each
  operand below the join and \<open>mono\<close>'s contrapositive carries non-bottomness upward.
\<close>

lemma normalized_lift_sup:
  fixes x y :: "'a::semilattice_sup lifted"
  assumes mono: "\<And>a b::'a. a \<le> b \<Longrightarrow> is_bot_pred b \<Longrightarrow> is_bot_pred a"
    and nx: "normalized_lift is_bot_pred x"
    and ny: "normalized_lift is_bot_pred y"
  shows "normalized_lift is_bot_pred (x \<squnion> y)"
  using nx ny by (cases x; cases y) (auto dest: mono[OF sup_ge1] mono[OF sup_ge2])

text \<open>
  \<open>map_lift\<close> is the reachability functor's map (\<open>Option.map\<close>'s analogue), used to push a
  total, never-re-collapsing operation such as a local/global split through the lift.
\<close>

definition map_lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a lifted \<Rightarrow> 'b lifted" where
  "map_lift f x = do { a <- x; Lifted (f a) }"

lemma map_lift_Bot [simp]: "map_lift f Bot = Bot"
  unfolding map_lift_def by simp

lemma map_lift_Lifted [simp]: "map_lift f (Lifted a) = Lifted (f a)"
  unfolding map_lift_def by simp

lemma map_lift_mono:
  fixes x y :: "'a::order lifted"
  assumes f_mono: "\<And>a b. a \<le> b \<Longrightarrow> f a \<le> (f b :: 'b::order)"
    and le: "x \<le> y"
  shows "map_lift f x \<le> map_lift f y"
  using le by (cases x; cases y) (auto simp: f_mono)

lemma map_lift_sup:
  fixes x y :: "'a::semilattice_sup lifted"
  assumes f_sup: "\<And>a b. f (a \<squnion> b) = (f a \<squnion> f b :: 'b::semilattice_sup)"
  shows "map_lift f (x \<squnion> y) = map_lift f x \<squnion> map_lift f y"
  by (cases x; cases y) (simp_all add: f_sup)

text \<open>
  Generic monotonicity for the reachability dispatch, proved once here instead of at every
  instantiation (\<open>abs_state\<close>, \<open>resolved_st_q\<close>, ...): whenever the underlying transfer is
  monotone and the bottom predicate is downward closed (as \<open>is_bot_state\<close> always is, via
  \<open>is_bot_state_mono\<close>), \<open>transfer_lift\<close>/\<open>transfer_lift2\<close> are monotone.
\<close>

lemma normalize_lift_mono:
  fixes a b :: "'a::order"
  assumes f_le: "a \<le> b"
    and bot_mono: "is_bot_pred b \<Longrightarrow> is_bot_pred a"
  shows "normalize_lift is_bot_pred a \<le> normalize_lift is_bot_pred b"
  unfolding normalize_lift_def using f_le bot_mono by auto

lemma transfer_lift_mono:
  fixes x1 x2 :: "'a::order lifted"
  assumes f_mono: "\<And>a b. a \<le> b \<Longrightarrow> f a \<le> f b"
    and bot_mono: "\<And>a b. a \<le> b \<Longrightarrow> is_bot_pred b \<Longrightarrow> is_bot_pred a"
    and le: "x1 \<le> x2"
  shows "transfer_lift is_bot_pred f x1 \<le> (transfer_lift is_bot_pred f x2 :: 'b::order lifted)"
  using le
proof (cases x1)
  case Bot
  then show ?thesis by simp
next
  case (Lifted a)
  with le obtain b where x2_eq: "x2 = Lifted b" and ab: "a \<le> b"
    by (cases x2) simp_all
  show ?thesis
    unfolding Lifted x2_eq transfer_lift_Lifted
  proof (rule normalize_lift_mono)
    show "f a \<le> f b" by (rule f_mono[OF ab])
    show "is_bot_pred (f b) \<Longrightarrow> is_bot_pred (f a)"
      using bot_mono[OF f_mono[OF ab]] .
  qed
qed

lemma transfer_lift2_mono:
  fixes x1 x2 :: "'a::order lifted" and y1 y2 :: "'b::order lifted"
  assumes f_mono: "\<And>a1 a2 b1 b2. a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> f a1 b1 \<le> f a2 b2"
    and bot_mono: "\<And>a b. a \<le> b \<Longrightarrow> is_bot_pred b \<Longrightarrow> is_bot_pred a"
    and lex: "x1 \<le> x2" and ley: "y1 \<le> y2"
  shows "transfer_lift2 is_bot_pred f x1 y1 \<le> (transfer_lift2 is_bot_pred f x2 y2 :: 'c::order lifted)"
  using lex ley
proof (cases x1)
  case Bot
  then show ?thesis by simp
next
  case (Lifted a)
  with lex obtain a' where x2_eq: "x2 = Lifted a'" and aa: "a \<le> a'"
    by (cases x2) simp_all
  show ?thesis
  proof (cases y1)
    case Bot
    then show ?thesis using Lifted by simp
  next
    case (Lifted b)
    with ley obtain b' where y2_eq: "y2 = Lifted b'" and bb: "b \<le> b'"
      by (cases y2) simp_all
    show ?thesis
      unfolding \<open>x1 = Lifted a\<close> x2_eq \<open>y1 = Lifted b\<close> y2_eq transfer_lift2_Lifted
    proof (rule normalize_lift_mono)
      show "f a b \<le> f a' b'" by (rule f_mono[OF aa bb])
      show "is_bot_pred (f a' b') \<Longrightarrow> is_bot_pred (f a b)"
        using bot_mono[OF f_mono[OF aa bb]] .
    qed
  qed
qed

subsection \<open>Role-aware local/global assembly\<close>

text \<open>
  \<^type>\<open>strategy_tree\<close> forces one shared payload type across \<open>QueryL\<close>/\<open>QueryG\<close>/
  \<open>Side\<close>/\<open>Answer\<close> (AD-51): there is no room for locals and globals to carry different
  types. Reconstructing one solver-facing edge input therefore joins a queried local
  unknown with the accumulated global while both already share the same
  \<^type>\<open>lifted\<close> payload -- but the two slots are not interchangeable. A local
  \<^const>\<open>Bot\<close> means this control-flow point is unreachable and must dominate
  regardless of what the global side holds; a global \<^const>\<open>Bot\<close> means only that no
  side contribution has been published yet and must act as \<open>\<squnion>\<close>'s identity. The
  symmetric \<open>sup_lifted\<close> is wrong here: \<open>Bot \<squnion> Lifted g = Lifted g\<close> would let
  any live global resurrect a dead local predecessor, the same resurrection shape
  \<open>is_bot_state (su \<squnion> g)\<close>-style checks on a reconstructed join already miss (AD-52),
  one layer up. \<open>assemble_local_global\<close> is deliberately independent of any global-key
  type or routing policy (\<open>unit\<close>, named globals, ...): a unit-specific tree
  constructor only supplies which key to query, never a special case of this join.
\<close>

fun assemble_local_global :: "'b::semilattice_sup lifted \<Rightarrow> 'b lifted \<Rightarrow> 'b lifted" where
  "assemble_local_global Bot g = Bot"
| "assemble_local_global (Lifted su) Bot = Lifted su"
| "assemble_local_global (Lifted su) (Lifted sg) = Lifted (su \<squnion> sg)"

lemma assemble_local_global_mono:
  fixes l1 l2 g1 g2 :: "'b::semilattice_sup lifted"
  assumes "l1 \<le> l2" and "g1 \<le> g2"
  shows "assemble_local_global l1 g1 \<le> assemble_local_global l2 g2"
  apply(cases l1; cases l2; cases g1; cases g2)
  using assms by (auto simp add: sup.coboundedI1 sup.coboundedI2)
 
lemma assemble_local_global_ge_local[simp]:
  fixes l g :: "'b::semilattice_sup lifted"
  shows "l \<le> assemble_local_global l g"
  by (cases l; cases g) simp_all

text \<open>
  The concretization of an assembled input reduces to the ordinary raw-join
  concretization on a witness: \<open>Bot\<close> in the local slot concretizes to nothing
  (matching the \<open>Bot\<close>-dominates role), while \<open>Lifted su\<close> concretizes exactly as
  the pre-lift raw reconstruction \<open>su \<squnion> g'\<close> did, with \<open>g'\<close> the global slot's own
  payload (or \<open>bot\<close>, the global role's neutral element, when it is itself \<open>Bot\<close>).
  This is the bridge every witness-based edge/local-tree soundness proof uses to
  fall back onto its pre-lift \<open>tf_sound_*_forD\<close> fact once a concrete witness rules
  out \<open>Bot\<close> in the local slot.
\<close>
lemma assemble_local_global_Lifted:
  fixes su :: "'b::bounded_semilattice_sup_bot" and g :: "'b lifted"
  shows "assemble_local_global (Lifted su) g = Lifted (su \<squnion> (case g of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))"
  by (cases g) simp_all

lemma gamma_state_lift_assemble_local_global:
  fixes l g :: "'a::sound_domain abs_state lifted"
  shows "gamma_state_lift (assemble_local_global l g) =
           (case l of Bot \<Rightarrow> {}
            | Lifted su \<Rightarrow> \<lbrakk>su \<squnion> (case g of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>)"
  by (cases l; cases g) simp_all

subsection \<open>Abstract domain locale (with widening)\<close>

text \<open>
  Extends sound_domain with widening for termination guarantees.
  Required when connecting to the TD solver for a domain with
  infinite ascending chains (e.g., intervals).

  Finite domains (sign, parity) instantiate this with widen = sup;
  the widen axioms then hold trivially from sup_ge1/sup_ge2.
\<close>

subsection \<open>Abstract-domain type class (with widening)\<close>

text \<open>
  Extends sound_domain with widening for termination guarantees.
  Required when connecting to the TD solver for a domain with
  infinite ascending chains (e.g., intervals).

  Finite domains (sign, parity) instantiate this with widen = sup;
  the widen axioms then hold trivially from sup_ge1/sup_ge2.

  Inherits widen from TD.Update_rules widening rather than re-fixing it,
  so sign :: warrowing and ivl :: warrowing instantiations remain consistent.
\<close>

class abstract_domain = sound_domain + widening

text \<open>The vendored solver's update rules are stated for a carrier that is both a bounded
  semilattice and carries the respective operator; these name the combinations once so a
  sort constraint can cite them.\<close>

class bounded_widening = bounded_semilattice_sup_bot + widening
class bounded_narrowing = bounded_semilattice_sup_bot + narrowing
class bounded_warrowing = bounded_semilattice_sup_bot + warrowing

subsection \<open>Derived widening-gamma bounds\<close>

lemma widen_ub1: "gamma a \<subseteq> gamma (a \<nabla> b)" for a b :: "'a::abstract_domain"
  by (rule gamma_mono[OF widen_ge1])

lemma widen_ub2: "gamma b \<subseteq> gamma (a \<nabla> b)" for a b :: "'a::abstract_domain"
  by (rule gamma_mono[OF widen_ge2])

subsection \<open>Lifted widening\<close>

definition widen_state ::
    "('a::abstract_domain) abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  where
  "widen_state sigma1 sigma2 = (\<lambda>x. widen (sigma1 x) (sigma2 x))"

text \<open>
  The warrowing update rule needs \<open>'d::bounded_warrowing\<close>. \<^typ>\<open>'a lifted\<close> already
  carries \<open>widening\<close>/\<open>narrowing\<close> separately and \<open>bounded_semilattice_sup_bot\<close>; this
  registers the combined class explicitly, mirroring \<open>bounded_semilattice_sup_bot\<close>'s own
  combined registration above.
\<close>

instance lifted :: (bounded_warrowing) bounded_warrowing ..

text \<open>
  \<open>\<nabla>\<Delta>\<close> preserves \<^const>\<open>normalized_lift\<close> from just its \<^emph>\<open>right\<close> operand being
  normalized, matching \<open>warrowing_properties\<close>'s own asymmetry: \<open>b \<le> a \<nabla>\<Delta> b\<close> holds
  unconditionally, on whichever branch (\<open>\<nabla>\<close> or \<open>\<Delta>\<close>) the \<open>b \<le> a\<close> test picks, so only
  \<open>y\<close> -- the operand playing \<open>warrowing_properties\<close>'s \<open>b\<close> -- needs to already be
  non-bottom. Stated after the \<open>bounded_warrowing\<close> instance above, because \<open>\<nabla>\<Delta>\<close> on
  \<^typ>\<open>'a lifted\<close> only exists once that instance is in scope.
\<close>

lemma normalized_lift_warrow:
  fixes x y :: "'a::bounded_warrowing lifted"
  assumes mono: "\<And>a b::'a. a \<le> b \<Longrightarrow> is_bot_pred b \<Longrightarrow> is_bot_pred a"
    and ny: "normalized_lift is_bot_pred y"
  shows "normalized_lift is_bot_pred (x \<nabla>\<Delta> y)"
proof (cases x)
  case Bot
  show ?thesis
  proof (cases y)
    case Bot
    with \<open>x = Bot\<close> show ?thesis by (simp add: warrow_def)
  next
    case (Lifted b)
    with \<open>x = Bot\<close> ny show ?thesis by (simp add: warrow_def)
  qed
next
  case (Lifted a)
  show ?thesis
  proof (cases y)
    case Bot
    with \<open>x = Lifted a\<close> show ?thesis by (simp add: warrow_def)
  next
    case (Lifted b)
    with ny have not_bot_b: "\<not> is_bot_pred b" by simp
    show ?thesis
    proof (cases "y \<le> x")
      case True
      then have "b \<le> a" using \<open>x = Lifted a\<close> \<open>y = Lifted b\<close> by simp
      then have "b \<le> a \<Delta> b" by (rule narrow_ge)
      with mono not_bot_b have "\<not> is_bot_pred (a \<Delta> b)" by blast
      with True \<open>x = Lifted a\<close> \<open>y = Lifted b\<close> show ?thesis by (simp add: warrow_def)
    next
      case False
      have "b \<le> a \<nabla> b" by (rule widen_ge2)
      with mono not_bot_b have "\<not> is_bot_pred (a \<nabla> b)" by blast
      with False \<open>x = Lifted a\<close> \<open>y = Lifted b\<close> show ?thesis by (simp add: warrow_def)
    qed
  qed
qed

subsection \<open>Printable-domain typeclass\<close>

text \<open>
  The @{text show_val} class equips an abstract value type with a string
  printer.  Separate from @{class abstract_domain} so the abstract-domain
  class stays a purely semantic object; rendering is a separate concern.

  Every domain used in visualisation instantiates this class.
  The @{text Analysis_GraphViz} rendering layer is parameterised over any
  @{text "'a::show_val"} and needs no domain-specific code paths.
\<close>

class show_val =
  fixes show_val :: "'a \<Rightarrow> string"

subsection \<open>String utilities for show_val instances\<close>

text \<open>
  Shared nat/int-to-string helpers so domain @{class show_val} instances
  do not each re-define them.
\<close>

fun show_nat :: "nat \<Rightarrow> string" where
  "show_nat n =
     (if n < 10 then [char_of (n + 48)]
      else show_nat (n div 10) @ [char_of (n mod 10 + 48)])"

definition show_int :: "int \<Rightarrow> string" where
  "show_int i =
     (if i < 0 then ''-'' @ show_nat (nat (- i))
      else show_nat (nat i))"

end
