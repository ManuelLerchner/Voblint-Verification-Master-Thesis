theory Abstract_Domain
  imports "Voblint_VIMP.VIMP_Syntax" "Voblint_VIMP.VIMP_Expr" "TD.Update_rules"
    "Voblint_CFG.CFG_Def" "HOL-Library.Monad_Syntax"
begin

hide_const (open) Update_rules.N

text \<open>The solver unknown for a program point is a CFG node.  Analysis-facing code keeps the
  short name \<open>pp\<close> for it; a return node is \<^term>\<open>FunctionResult p\<close>, a callee entry
  \<^term>\<open>FunctionEntry p\<close>, an ordinary location \<^term>\<open>Statement n\<close>.\<close>
type_synonym pp = cfg_node

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

subsection \<open>Backward-analysis locale\<close>

text \<open>
  A semantic intersection preserves every concrete value shared by both
  operands. It need not be the lattice infimum: a domain may normalize an
  empty result while its representation order still distinguishes several
  empty elements. This locale records the preservation obligation;
  \<open>backward_domain_refined\<close> adds the reductiveness and monotonicity needed
  by solver-facing filters.
\<close>


locale semantic_intersection =
  fixes intersect :: "'a::sound_domain => 'a => 'a"
  assumes intersect_sound[intro]:
    "n \<in> gamma a \<Longrightarrow> n \<in> gamma b \<Longrightarrow> n \<in> gamma (intersect a b)"

text \<open>
  Extends @{class sound_domain} with the infrastructure for backward
  (inverse) evaluation of guards and arithmetic expressions. Per-domain:
  provide a @{locale semantic_intersection} instance, aval_abs, and inv_*
  operators; the generic afilter / bfilter and their soundness theorems
  follow by induction.
\<close>

locale backward_domain =
  semantic_intersection intersect
    for intersect :: "'a::sound_domain => 'a => 'a" +
  fixes
    aval_abs  :: "tyenv => ikind => exp => 'a abs_state => 'a"
    and tobool :: "'a => bool option"
    and inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_eq    :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "ikind => 'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "ikind => 'a => 'a => 'a => 'a * 'a"
    and inv_times :: "ikind => 'a => 'a => 'a => 'a * 'a"
  assumes
    aval_abs_sound[intro]:
      "(\<forall>x. s x \<in> gamma (\<sigma> x)) \<Longrightarrow> taval \<Gamma> ik e s \<in> gamma (aval_abs \<Gamma> ik e \<sigma>)"
  and inv_less_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 < n2) = res
       \<Longrightarrow> n1 \<in> gamma (fst (inv_less res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less res a1 a2))"
  and inv_eq_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 = n2) = res
       \<Longrightarrow> n1 \<in> gamma (fst (inv_eq res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq res a1 a2))"
  and inv_plus_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> ik_norm ik (n1 + n2) \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_plus ik r a1 a2)) \<and> n2 \<in> gamma (snd (inv_plus ik r a1 a2))"
  and inv_minus_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> ik_norm ik (n1 - n2) \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_minus ik r a1 a2)) \<and> n2 \<in> gamma (snd (inv_minus ik r a1 a2))"
  and inv_times_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> ik_norm ik (n1 * n2) \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_times ik r a1 a2)) \<and> n2 \<in> gamma (snd (inv_times ik r a1 a2))"
  and tobool_sound:
      "tobool p = Some b \<Longrightarrow> i \<in> gamma p \<Longrightarrow> truthy i = b"
begin

text \<open>
  \<open>afilter\<close> takes an explicit \<open>ik\<close>: \<^const>\<open>taval\<close>'s \<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>
  evaluate their operands at the very same \<open>ik\<close> as the node itself (no
  re-synthesis), so a caller narrowing through an arithmetic node must pass
  that same \<open>ik\<close> down unchanged -- exactly mirroring \<^const>\<open>taval\<close>'s own
  recursion. \<open>V x\<close>'s leaf case does not consult \<open>ik\<close> itself: the caller
  already established \<open>a\<close> at the correct kind.
\<close>
fun afilter :: "tyenv => ikind => exp => 'a => 'a abs_state => 'a abs_state" where
    "afilter \<Gamma> ik (V x) a \<sigma> = \<sigma>(x := intersect a (\<sigma> x))"
  | "afilter \<Gamma> ik (Plus  e1 e2) a \<sigma> =
       (let (a1, a2) = inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)
        in afilter \<Gamma> ik e1 a1 (afilter \<Gamma> ik e2 a2 \<sigma>))"
  | "afilter \<Gamma> ik (Minus e1 e2) a \<sigma> =
       (let (a1, a2) = inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)
        in afilter \<Gamma> ik e1 a1 (afilter \<Gamma> ik e2 a2 \<sigma>))"
  | "afilter \<Gamma> ik (Times e1 e2) a \<sigma> =
       (let (a1, a2) = inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)
        in afilter \<Gamma> ik e1 a1 (afilter \<Gamma> ik e2 a2 \<sigma>))"
  | "afilter \<Gamma> ik _ a \<sigma> = \<sigma>"

text \<open>
  \<open>feasible\<close> is the forward half of Goblint's two-phase branch handling, as a
  predicate: evaluate \<open>e\<close> forward and ask whether the abstract value that
  yields leaves the selected polarity possible at all. A bottom value denotes
  no store, and a definite \<open>tobool\<close> answer disagreeing with \<open>pol\<close> rules the
  polarity out; every other case keeps it open. Backward narrowing cannot
  replace this test: a Boolean-valued subexpression in an operand position
  inverts to a target \<open>afilter\<close> has no rule to push through a comparison node,
  so the target is dropped and the state survives unrefined even where no state
  satisfies the condition.

  The leading \<open>is_bot\<close> test is not redundant with the \<open>tobool\<close> one. An
  author's \<open>tobool\<close> is free to answer arbitrarily at its own domain's bottom
  (every answer is vacuously sound there, since \<open>gamma bot = {}\<close>), so it need
  not, and generally does not, agree across a bottom/non-bottom pair
  \<open>\<sigma>1 \<le> \<sigma>2\<close> the way \<open>tobool_mono\<close> requires. Answering \<open>is_bot\<close> directly,
  ahead of \<open>tobool\<close>, sidesteps that disagreement instead of relying on it, and
  is what makes \<open>feasible_mono\<close> hold.
\<close>

text \<open>
  \<open>feasible\<close> tests a full sub-expression's own truthiness, exactly like
  \<^const>\<open>taval_syn\<close>'s top-level entry: it synthesizes its own kind from \<open>e\<close>
  itself (\<open>opk (esyn \<Gamma> e)\<close>) rather than taking one from the caller, since
  \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>/\<open>Less\<close>/\<open>Eq\<close> -- the shapes \<open>feasible\<close> is ever called on --
  never consult an externally supplied \<open>ik\<close> either.
\<close>

definition feasible :: "tyenv => exp => bool => 'a abs_state => bool" where
  "feasible \<Gamma> e pol \<sigma> =
     (let ik = opk (esyn \<Gamma> e) in
      \<not> is_bot (aval_abs \<Gamma> ik e \<sigma>) \<and> tobool (aval_abs \<Gamma> ik e \<sigma>) \<noteq> Some (\<not> pol))"

text \<open>
  Every state a concrete store witnesses is feasible for the polarity that
  store takes: \<open>aval_abs_sound\<close> rules out the bottom case and \<open>tobool_sound\<close>
  the disagreeing-answer case. This is what makes the gate's \<open>bot\<close> outcome
  sound wherever it fires -- it fires only when no represented store exists.
\<close>

lemma feasible_of_concrete:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and "truthy (taval_syn \<Gamma> e s) = pol"
  shows "feasible \<Gamma> e pol \<sigma>"
proof -
  let ?ik = "opk (esyn \<Gamma> e)"
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF assms(1)] .
  have ea: "taval \<Gamma> ?ik e s \<in> gamma (aval_abs \<Gamma> ?ik e \<sigma>)" using aval_abs_sound[OF gs] by simp
  have nb: "\<not> is_bot (aval_abs \<Gamma> ?ik e \<sigma>)" using ea is_bot_correct by auto
  have "tobool (aval_abs \<Gamma> ?ik e \<sigma>) \<noteq> Some (\<not> pol)"
  proof
    assume "tobool (aval_abs \<Gamma> ?ik e \<sigma>) = Some (\<not> pol)"
    then have "truthy (taval \<Gamma> ?ik e s) = (\<not> pol)" using tobool_sound[OF _ ea] by simp
    then show False using assms(2) by (simp add: taval_syn_def)
  qed
  with nb show ?thesis by (simp add: feasible_def)
qed
text \<open>
  \<open>bfilter\<close> narrows a state under an assumed truth value of \<open>e\<close>: \<open>bfilter e
  True\<close> is \<open>assume e\<close>, \<open>bfilter e False\<close> is \<open>assume-not e\<close>. \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>
  distribute structurally (De Morgan, over \<open>\<squnion>\<close> for the disjunctive branch);
  \<open>Less\<close>/\<open>Eq\<close> go straight through \<open>inv_less\<close>/\<open>inv_eq\<close> on their two operands.
  Every other constructor -- \<open>N\<close>, \<open>V\<close>, \<open>Plus\<close>, \<open>Minus\<close>, \<open>Times\<close> -- has no
  Boolean-shaped narrowing operator of its own, so the fallback case reduces
  truthiness to the one comparison every domain already inverts: \<open>truthy
  (aval e s) = res\<close> iff \<open>(aval e s = 0) = (\<not> res)\<close>, so \<open>inv_eq (\<not> res)\<close>
  against the abstract constant \<open>0\<close> narrows \<open>e\<close>'s own target value, and
  \<open>afilter\<close> propagates that target through \<open>e\<close>'s structure. This reuses
  \<open>inv_eq\<close>/\<open>afilter\<close> rather than adding a new domain-author operator.

  The two disjunctive cases -- \<open>Or _ _ True\<close> and \<open>And _ _ False\<close> -- gate each
  side on \<open>feasible\<close> before joining, matching Goblint's \<open>inv_exp\<close>, which
  refines the arms of a disjunction separately and drops one whose refinement
  contradicts. Without the gate, a side no state satisfies still contributes
  its own unrefined incoming state and the join discards what the other side
  established: the empty target such a side inverts to is dropped wherever
  \<open>afilter\<close> has no rule for the node carrying it, so the narrowing that would
  have signalled the contradiction never happens. \<open>bot\<close> is the unit of \<open>\<squnion>\<close>,
  so gating an infeasible side removes it from the join exactly.
\<close>

text \<open>
  \<open>bfilter\<close> takes no separate \<open>ik\<close>: every case synthesizes its own kind from
  the sub-expression(s) it dispatches on (\<open>opk (esyn \<Gamma> _)\<close> or
  \<open>opk (kjoin (esyn \<Gamma> _) (esyn \<Gamma> _))\<close>), exactly mirroring \<^const>\<open>taval\<close>'s
  own \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> cases, none of which consult an
  externally supplied kind either.
\<close>
fun bfilter :: "tyenv => exp => bool => 'a abs_state => 'a abs_state" where
    "bfilter \<Gamma> (Less e1 e2) res \<sigma> =
       (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2));
            (a1, a2) = inv_less res (aval_abs \<Gamma> k e1 \<sigma>) (aval_abs \<Gamma> k e2 \<sigma>)
        in afilter \<Gamma> k e1 a1 (afilter \<Gamma> k e2 a2 \<sigma>))"
  | "bfilter \<Gamma> (Not b) res \<sigma> = bfilter \<Gamma> b (\<not> res) \<sigma>"
  | "bfilter \<Gamma> (And b1 b2) True  \<sigma> = bfilter \<Gamma> b1 True  (bfilter \<Gamma> b2 True  \<sigma>)"
  | "bfilter \<Gamma> (And b1 b2) False \<sigma> =
       (if feasible \<Gamma> b1 False \<sigma> then bfilter \<Gamma> b1 False \<sigma> else bot)
       \<squnion> (if feasible \<Gamma> b2 False \<sigma> then bfilter \<Gamma> b2 False \<sigma> else bot)"
  | "bfilter \<Gamma> (Or  b1 b2) True  \<sigma> =
       (if feasible \<Gamma> b1 True \<sigma> then bfilter \<Gamma> b1 True \<sigma> else bot)
       \<squnion> (if feasible \<Gamma> b2 True \<sigma> then bfilter \<Gamma> b2 True \<sigma> else bot)"
  | "bfilter \<Gamma> (Or  b1 b2) False \<sigma> = bfilter \<Gamma> b1 False (bfilter \<Gamma> b2 False \<sigma>)"
  | "bfilter \<Gamma> (Eq  e1 e2) res  \<sigma> =
       (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2));
            (a1, a2) = inv_eq res (aval_abs \<Gamma> k e1 \<sigma>) (aval_abs \<Gamma> k e2 \<sigma>)
        in afilter \<Gamma> k e1 a1 (afilter \<Gamma> k e2 a2 \<sigma>))"
  | "bfilter \<Gamma> e res \<sigma> =
       (let k = opk (esyn \<Gamma> e);
            (a1, a2) = inv_eq (\<not> res) (aval_abs \<Gamma> k e \<sigma>) (aval_abs \<Gamma> k (N 0) \<sigma>)
        in afilter \<Gamma> k e a1 \<sigma>)"
text \<open>
  \<open>styped \<Gamma> s\<close> (\<^theory>\<open>Voblint_VIMP.VIMP_Typing\<close>) is an explicit, honestly-scoped
  premise, not a guess: \<open>\<^theory>\<open>Voblint_VIMP.VIMP_Proc\<close>\<close>'s
  \<open>pstep_preserves_sstyped\<close>/\<open>pcompletes_preserves_styped\<close> already prove every
  concrete store the small-step semantics reaches stays within its variables'
  declared kinds. \<open>V x\<close>'s leaf case is genuinely unsound without it: \<open>taval \<Gamma>
  ik (V x) s = ik_norm ik (s x)\<close>, and inverting that cast to recover \<open>s x \<in>
  gamma a\<close> from \<open>ik_norm ik (s x) \<in> gamma a\<close> needs \<open>s x\<close> already in \<open>ik\<close>'s
  range. That existing proof is not yet threaded through the CFG-execution /
  activation-trace / DG-framework soundness chain up to this call site --
  \<open>styped\<close> is carried here as an assumption pending that wiring, not
  discharged by it.
\<close>
lemma afilter_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "taval \<Gamma> ik e s \<in> gamma a" "styped \<Gamma> s" "wt_exp \<Gamma> e ik"
  shows "s \<in> \<lbrakk>afilter \<Gamma> ik e a \<sigma>\<rbrakk>"
using assms proof (induction e arbitrary: ik a \<sigma>)
  case (N n)
  then show ?case by simp
next
  case (V x)
  have ik_choice: "ik = \<Gamma> x \<or> ik = ik_promote (\<Gamma> x)" using V.prems(4) by simp
  have sx_range: "s x \<in> ik_range ik"
  proof (cases "ik = \<Gamma> x")
    case True
    with V.prems(3) show ?thesis by (simp add: styped_def)
  next
    case False
    with ik_choice have ik_prom: "ik = ik_promote (\<Gamma> x)" by simp
    have "s x \<in> ik_range (\<Gamma> x)" using V.prems(3) by (simp add: styped_def)
    with ik_range_promote_mono[of "\<Gamma> x"] ik_prom show ?thesis by auto
  qed
  have norm_id: "ik_norm ik (s x) = s x" by (rule ik_norm_id[OF sx_range])
  have sx_a: "s x \<in> gamma a"
    using V.prems(2) norm_id by simp
  have sx_s: "s x \<in> gamma (\<sigma> x)"
    using gamma_stateD[OF V.prems(1)] by simp
  show ?case
    unfolding gamma_state_def afilter.simps
  proof (intro CollectI allI)
    fix y show "s y \<in> gamma ((\<sigma>(x := intersect a (\<sigma> x))) y)"
      using intersect_sound[OF sx_a sx_s] gamma_stateD[OF V.prems(1)]
      by (cases "y = x") auto
  qed
next
  case (Plus e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)"
    by (cases "inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Plus.prems(1)] .
  have e1a: "taval \<Gamma> ik e1 s \<in> gamma (aval_abs \<Gamma> ik e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "taval \<Gamma> ik e2 s \<in> gamma (aval_abs \<Gamma> ik e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have asum: "ik_norm ik (taval \<Gamma> ik e1 s + taval \<Gamma> ik e2 s) \<in> gamma a" using Plus.prems(2) by simp
  have inv12: "taval \<Gamma> ik e1 s \<in> gamma a1 \<and> taval \<Gamma> ik e2 s \<in> gamma a2"
    using inv_plus_sound[OF e1a e2a asum] pair[symmetric] by simp
  have wt1: "wt_exp \<Gamma> e1 ik" and wt2: "wt_exp \<Gamma> e2 ik" using Plus.prems(4) by simp_all
  have gs2: "s \<in> \<lbrakk>afilter \<Gamma> ik e2 a2 \<sigma>\<rbrakk>"
    using Plus.IH(2)[OF Plus.prems(1) inv12[THEN conjunct2] Plus.prems(3) wt2] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Plus.IH(1)[OF gs2 inv12[THEN conjunct1] Plus.prems(3) wt1] by simp
next
  case (Minus e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)"
    by (cases "inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Minus.prems(1)] .
  have e1a: "taval \<Gamma> ik e1 s \<in> gamma (aval_abs \<Gamma> ik e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "taval \<Gamma> ik e2 s \<in> gamma (aval_abs \<Gamma> ik e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have adiff: "ik_norm ik (taval \<Gamma> ik e1 s - taval \<Gamma> ik e2 s) \<in> gamma a" using Minus.prems(2) by simp
  have inv12: "taval \<Gamma> ik e1 s \<in> gamma a1 \<and> taval \<Gamma> ik e2 s \<in> gamma a2"
    using inv_minus_sound[OF e1a e2a adiff] pair[symmetric] by simp
  have wt1: "wt_exp \<Gamma> e1 ik" and wt2: "wt_exp \<Gamma> e2 ik" using Minus.prems(4) by simp_all
  have gs2: "s \<in> \<lbrakk>afilter \<Gamma> ik e2 a2 \<sigma>\<rbrakk>"
    using Minus.IH(2)[OF Minus.prems(1) inv12[THEN conjunct2] Minus.prems(3) wt2] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Minus.IH(1)[OF gs2 inv12[THEN conjunct1] Minus.prems(3) wt1] by simp
next
  case (Times e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)"
    by (cases "inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Times.prems(1)] .
  have e1a: "taval \<Gamma> ik e1 s \<in> gamma (aval_abs \<Gamma> ik e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "taval \<Gamma> ik e2 s \<in> gamma (aval_abs \<Gamma> ik e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have aprod: "ik_norm ik (taval \<Gamma> ik e1 s * taval \<Gamma> ik e2 s) \<in> gamma a" using Times.prems(2) by simp
  have inv12: "taval \<Gamma> ik e1 s \<in> gamma a1 \<and> taval \<Gamma> ik e2 s \<in> gamma a2"
    using inv_times_sound[OF e1a e2a aprod] pair[symmetric] by simp
  have wt1: "wt_exp \<Gamma> e1 ik" and wt2: "wt_exp \<Gamma> e2 ik" using Times.prems(4) by simp_all
  have gs2: "s \<in> \<lbrakk>afilter \<Gamma> ik e2 a2 \<sigma>\<rbrakk>"
    using Times.IH(2)[OF Times.prems(1) inv12[THEN conjunct2] Times.prems(3) wt2] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Times.IH(1)[OF gs2 inv12[THEN conjunct1] Times.prems(3) wt1] by simp
next
  case (Less e1 e2) then show ?case by simp
next
  case (Eq e1 e2) then show ?case by simp
next
  case (Not e) then show ?case by simp
next
  case (And e1 e2) then show ?case by simp
next
  case (Or e1 e2) then show ?case by simp
qed

text \<open>
  Every constructor without its own Boolean-shaped narrowing operator --
  \<open>N\<close>, \<open>V\<close>, \<open>Plus\<close>, \<open>Minus\<close>, \<open>Times\<close> -- reduces \<open>bfilter\<close>'s target truth
  value to an \<open>inv_eq\<close> narrowing against the abstract constant \<open>0\<close> (see
  \<open>bfilter\<close>'s own comment), then propagates the narrowed target through
  \<open>afilter\<close>. Proved once here, generically in \<open>e\<close>, so the induction below
  cites it instead of repeating the same \<open>inv_eq\<close>/\<open>afilter_sound\<close> chain per
  arithmetic constructor.
\<close>
lemma bfilter_default_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (taval \<Gamma> (opk (esyn \<Gamma> e)) e s) = res" "styped \<Gamma> s" "wt_exp \<Gamma> e (opk (esyn \<Gamma> e))"
  shows "s \<in> \<lbrakk>afilter \<Gamma> (opk (esyn \<Gamma> e)) e
      (fst (inv_eq (\<not> res) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) e \<sigma>) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) (N 0) \<sigma>))) \<sigma>\<rbrakk>"
proof -
  let ?ik = "opk (esyn \<Gamma> e)"
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF assms(1)] .
  have ea: "taval \<Gamma> ?ik e s \<in> gamma (aval_abs \<Gamma> ?ik e \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e0: "taval \<Gamma> ?ik (N 0) s \<in> gamma (aval_abs \<Gamma> ?ik (N 0) \<sigma>)"
    by (rule aval_abs_sound[of s \<sigma> \<Gamma> ?ik "N 0", OF gs])
  have eq0: "(taval \<Gamma> ?ik e s = taval \<Gamma> ?ik (N 0) s) = (\<not> res)" using assms(2) by auto
  have "taval \<Gamma> ?ik e s \<in> gamma (fst (inv_eq (\<not> res) (aval_abs \<Gamma> ?ik e \<sigma>) (aval_abs \<Gamma> ?ik (N 0) \<sigma>)))"
    using inv_eq_sound[OF ea e0 eq0] by simp
  then show ?thesis using afilter_sound[OF assms(1) _ assms(3) assms(4)] by simp
qed

lemma bfilter_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (taval_syn \<Gamma> e s) = res" "styped \<Gamma> s" "wt_exp \<Gamma> e (opk (esyn \<Gamma> e))"
  shows "s \<in> \<lbrakk>bfilter \<Gamma> e res \<sigma>\<rbrakk>"
using assms proof (induction e arbitrary: res \<sigma>)
  case (N n) show ?case
    using bfilter_default_sound[OF N.prems(1) N.prems(2)[unfolded taval_syn_def] N.prems(3) N.prems(4)]
    by simp
next
  case (V x) show ?case
    using bfilter_default_sound[OF V.prems(1) V.prems(2)[unfolded taval_syn_def] V.prems(3) V.prems(4)]
    by (simp add: bfilter.simps Let_def case_prod_beta fun_upd_def)
next
  case (Plus e1 e2) show ?case
    using bfilter_default_sound[OF Plus.prems(1) Plus.prems(2)[unfolded taval_syn_def]
      Plus.prems(3) Plus.prems(4)]
    by (simp add: Let_def case_prod_beta)
next
  case (Minus e1 e2) show ?case
    using bfilter_default_sound[OF Minus.prems(1) Minus.prems(2)[unfolded taval_syn_def]
      Minus.prems(3) Minus.prems(4)]
    by (simp add: Let_def case_prod_beta)
next
  case (Times e1 e2) show ?case
    using bfilter_default_sound[OF Times.prems(1) Times.prems(2)[unfolded taval_syn_def]
      Times.prems(3) Times.prems(4)]
    by (simp add: Let_def case_prod_beta)
next
  case (Not e)
  have bv': "truthy (taval_syn \<Gamma> e s) = (\<not> res)" using Not.prems(2) by (auto simp: taval_syn_def split: if_splits)
  have wte: "wt_exp \<Gamma> e (opk (esyn \<Gamma> e))" using Not.prems(4) by simp
  from Not.IH[OF Not.prems(1) bv' Not.prems(3) wte] show ?case by simp
next
  case (And e1 e2)
  have wt1: "wt_exp \<Gamma> e1 (opk (esyn \<Gamma> e1))" and wt2: "wt_exp \<Gamma> e2 (opk (esyn \<Gamma> e2))"
    using And.prems(4) by simp_all
  show ?case proof (cases res)
    case True
    have v1: "truthy (taval_syn \<Gamma> e1 s) = True" and v2: "truthy (taval_syn \<Gamma> e2 s) = True"
      using And.prems(2) True by (auto simp: taval_syn_def split: if_splits)
    have gs2: "s \<in> \<lbrakk>bfilter \<Gamma> e2 True \<sigma>\<rbrakk>"
      using And.IH(2)[OF And.prems(1) v2 And.prems(3) wt2] by simp
    show ?thesis
      using And.IH(1)[OF gs2 v1 And.prems(3) wt1] by (simp add: True)
  next
    case False
    have disj: "\<not> truthy (taval_syn \<Gamma> e1 s) \<or> \<not> truthy (taval_syn \<Gamma> e2 s)"
      using And.prems(2) False by (auto simp: taval_syn_def split: if_splits)
    show ?thesis proof (cases "truthy (taval_syn \<Gamma> e1 s)")
      case b1F: False
      have v1: "truthy (taval_syn \<Gamma> e1 s) = False" using b1F by simp
      have h: "s \<in> \<lbrakk>bfilter \<Gamma> e1 False \<sigma>\<rbrakk>"
        using And.IH(1)[OF And.prems(1) v1 And.prems(3) wt1] by simp
      have g: "feasible \<Gamma> e1 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v1])
      have sup1: "s \<in> \<lbrakk>bfilter \<Gamma> e1 False \<sigma>
                       \<squnion> (if feasible \<Gamma> e2 False \<sigma> then bfilter \<Gamma> e2 False \<sigma> else bot)\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub1 h] .
      have eqb: "bfilter \<Gamma> (And e1 e2) res \<sigma>
                   = bfilter \<Gamma> e1 False \<sigma>
                     \<squnion> (if feasible \<Gamma> e2 False \<sigma> then bfilter \<Gamma> e2 False \<sigma> else bot)"
        using False g by simp
      show ?thesis unfolding eqb by (rule sup1)
    next
      case b1T: True
      have v2: "truthy (taval_syn \<Gamma> e2 s) = False" using disj b1T by simp
      have h: "s \<in> \<lbrakk>bfilter \<Gamma> e2 False \<sigma>\<rbrakk>"
        using And.IH(2)[OF And.prems(1) v2 And.prems(3) wt2] by simp
      have g: "feasible \<Gamma> e2 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v2])
      have sup2: "s \<in> \<lbrakk>(if feasible \<Gamma> e1 False \<sigma> then bfilter \<Gamma> e1 False \<sigma> else bot)
                       \<squnion> bfilter \<Gamma> e2 False \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub2 h] .
      have eqb: "bfilter \<Gamma> (And e1 e2) res \<sigma>
                   = (if feasible \<Gamma> e1 False \<sigma> then bfilter \<Gamma> e1 False \<sigma> else bot)
                     \<squnion> bfilter \<Gamma> e2 False \<sigma>"
        using False g by simp
      show ?thesis unfolding eqb by (rule sup2)
    qed
  qed
next
  case (Or e1 e2)
  have wt1: "wt_exp \<Gamma> e1 (opk (esyn \<Gamma> e1))" and wt2: "wt_exp \<Gamma> e2 (opk (esyn \<Gamma> e2))"
    using Or.prems(4) by simp_all
  show ?case proof (cases res)
    case True
    have disj: "truthy (taval_syn \<Gamma> e1 s) \<or> truthy (taval_syn \<Gamma> e2 s)"
      using Or.prems(2) True by (auto simp: taval_syn_def split: if_splits)
    show ?thesis proof (cases "truthy (taval_syn \<Gamma> e1 s)")
      case b1T: True
      have v1: "truthy (taval_syn \<Gamma> e1 s) = True" using b1T by simp
      have h: "s \<in> \<lbrakk>bfilter \<Gamma> e1 True \<sigma>\<rbrakk>"
        using Or.IH(1)[OF Or.prems(1) v1 Or.prems(3) wt1] by simp
      have g: "feasible \<Gamma> e1 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v1])
      have sup1: "s \<in> \<lbrakk>bfilter \<Gamma> e1 True \<sigma>
                       \<squnion> (if feasible \<Gamma> e2 True \<sigma> then bfilter \<Gamma> e2 True \<sigma> else bot)\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub1 h] .
      have eqb: "bfilter \<Gamma> (Or e1 e2) res \<sigma>
                   = bfilter \<Gamma> e1 True \<sigma>
                     \<squnion> (if feasible \<Gamma> e2 True \<sigma> then bfilter \<Gamma> e2 True \<sigma> else bot)"
        using True g by simp
      show ?thesis unfolding eqb by (rule sup1)
    next
      case b1F: False
      have v2: "truthy (taval_syn \<Gamma> e2 s) = True" using disj b1F by simp
      have h: "s \<in> \<lbrakk>bfilter \<Gamma> e2 True \<sigma>\<rbrakk>"
        using Or.IH(2)[OF Or.prems(1) v2 Or.prems(3) wt2] by simp
      have g: "feasible \<Gamma> e2 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v2])
      have sup2: "s \<in> \<lbrakk>(if feasible \<Gamma> e1 True \<sigma> then bfilter \<Gamma> e1 True \<sigma> else bot)
                       \<squnion> bfilter \<Gamma> e2 True \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub2 h] .
      have eqb: "bfilter \<Gamma> (Or e1 e2) res \<sigma>
                   = (if feasible \<Gamma> e1 True \<sigma> then bfilter \<Gamma> e1 True \<sigma> else bot)
                     \<squnion> bfilter \<Gamma> e2 True \<sigma>"
        using True g by simp
      show ?thesis unfolding eqb by (rule sup2)
    qed
  next
    case False
    have v1: "truthy (taval_syn \<Gamma> e1 s) = False" and v2: "truthy (taval_syn \<Gamma> e2 s) = False"
      using Or.prems(2) False by (auto simp: taval_syn_def split: if_splits)
    have gs2: "s \<in> \<lbrakk>bfilter \<Gamma> e2 False \<sigma>\<rbrakk>"
      using Or.IH(2)[OF Or.prems(1) v2 Or.prems(3) wt2] by simp
    show ?thesis
      using Or.IH(1)[OF gs2 v1 Or.prems(3) wt1] by (simp add: False)
  qed
next
  case (Less e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have wt1: "wt_exp \<Gamma> e1 ?k" and wt2: "wt_exp \<Gamma> e2 ?k" using Less.prems(4) by (simp_all add: Let_def)
  obtain a1 a2 where pair: "(a1, a2) = inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>) (aval_abs \<Gamma> ?k e2 \<sigma>)"
    by (cases "inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>) (aval_abs \<Gamma> ?k e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Less.prems(1)] .
  have e1a: "taval \<Gamma> ?k e1 s \<in> gamma (aval_abs \<Gamma> ?k e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "taval \<Gamma> ?k e2 s \<in> gamma (aval_abs \<Gamma> ?k e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have less: "(taval \<Gamma> ?k e1 s < taval \<Gamma> ?k e2 s) = res"
    using Less.prems(2) by (auto simp: taval_syn_def Let_def split: if_splits)
  have inv12: "taval \<Gamma> ?k e1 s \<in> gamma a1 \<and> taval \<Gamma> ?k e2 s \<in> gamma a2"
    using inv_less_sound[OF e1a e2a less] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter \<Gamma> ?k e2 a2 \<sigma>\<rbrakk>"
    using afilter_sound[OF Less.prems(1) inv12[THEN conjunct2] Less.prems(3) wt2] by simp
  show ?case
    unfolding bfilter.simps pair[symmetric] Let_def
    using afilter_sound[OF gs2 inv12[THEN conjunct1] Less.prems(3) wt1] by simp
next
  case (Eq e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have wt1: "wt_exp \<Gamma> e1 ?k" and wt2: "wt_exp \<Gamma> e2 ?k" using Eq.prems(4) by (simp_all add: Let_def)
  obtain a1 a2 where pair: "(a1, a2) = inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>) (aval_abs \<Gamma> ?k e2 \<sigma>)"
    by (cases "inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>) (aval_abs \<Gamma> ?k e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Eq.prems(1)] .
  have e1a: "taval \<Gamma> ?k e1 s \<in> gamma (aval_abs \<Gamma> ?k e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "taval \<Gamma> ?k e2 s \<in> gamma (aval_abs \<Gamma> ?k e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have eq: "(taval \<Gamma> ?k e1 s = taval \<Gamma> ?k e2 s) = res"
    using Eq.prems(2) by (auto simp: taval_syn_def Let_def split: if_splits)
  have inv12: "taval \<Gamma> ?k e1 s \<in> gamma a1 \<and> taval \<Gamma> ?k e2 s \<in> gamma a2"
    using inv_eq_sound[OF e1a e2a eq] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter \<Gamma> ?k e2 a2 \<sigma>\<rbrakk>"
    using afilter_sound[OF Eq.prems(1) inv12[THEN conjunct2] Eq.prems(3) wt2] by simp
  show ?case
    unfolding bfilter.simps pair[symmetric] Let_def
    using afilter_sound[OF gs2 inv12[THEN conjunct1] Eq.prems(3) wt1] by simp
qed


text \<open>
  \<open>branch_lifted\<close> is the canonical Goblint-aligned branch semantics: the
  forward \<open>feasible\<close> gate on the whole condition ahead of \<open>bfilter\<close>, matching
  \<open>Base.branch\<close>'s \<open>eval_rv\<close> / \<open>to_bool\<close> dead-code gate ahead of \<open>invariant\<close>.
  An infeasible condition denotes \<open>Bot\<close> -- no concrete successor, matching
  Goblint's \<open>Deadcode\<close> as an outer control-flow fact rather than a value of the
  domain -- while every other case narrows via \<open>bfilter\<close> and returns
  \<open>Lifted\<close>. \<open>tobool\<close>'s definite answer, when present, is exactly \<open>truthy\<close> of
  every concrete value \<open>aval_abs e \<sigma>\<close> represents; \<open>truthy (aval e s) = pol\<close>
  for a represented \<open>s\<close> then forces that answer to equal \<open>pol\<close>, so the \<open>Bot\<close>
  case below is exercised only when no represented \<open>s\<close> exists at all.

  It is the same gate \<open>bfilter\<close> applies per disjunct inside its two join cases,
  here run on the whole condition -- which is what makes it a control-flow fact
  rather than a narrowing.

  \<open>branch\<close> is the plain-\<open>abs_state\<close> projection of \<open>branch_lifted\<close>, used by
  \<open>domain_transfer\<close>'s \<open>tf_branch\<close> field (and hence \<open>apply_tf\<close>) and the
  executable mirror: it collapses \<open>Bot\<close> to ordinary \<open>bot\<close>, so a caller that
  never needs to distinguish "no successor" from "successor whose store is
  bottom" can keep working with plain \<open>abs_state\<close>. The routed D/\<Gamma> pipeline
  instead consumes \<open>branch_lifted\<close> directly, so that a dead branch never has to
  be reconstructed as a whole-state-bottom value indistinguishable from an
  ordinary local/global-restricted result.
\<close>

definition branch_lifted :: "tyenv => exp => bool => 'a abs_state => 'a abs_state lifted" where
  "branch_lifted \<Gamma> e pol \<sigma> = (if feasible \<Gamma> e pol \<sigma> then Lifted (bfilter \<Gamma> e pol \<sigma>) else Bot)"

definition branch :: "tyenv => exp => bool => 'a abs_state => 'a abs_state" where
  "branch \<Gamma> e pol \<sigma> = (case branch_lifted \<Gamma> e pol \<sigma> of Bot \<Rightarrow> bot | Lifted \<sigma>' \<Rightarrow> \<sigma>')"

text \<open>
  The plain-state case split, recovered as a lemma rather than the primitive
  definition: callers reasoning about \<open>branch\<close> at the plain \<open>abs_state\<close> level
  (\<open>domain_transfer\<close>'s \<open>tf_branch\<close> field, the executable mirror) unfold through
  this instead of \<open>branch_lifted\<close>.
\<close>

lemma branch_unfold:
  "branch \<Gamma> e pol \<sigma> = (if feasible \<Gamma> e pol \<sigma> then bfilter \<Gamma> e pol \<sigma> else bot)"
  unfolding branch_def branch_lifted_def by simp

text \<open>
  \<open>bfilter\<close>'s two join cases, restated through \<open>branch\<close>: each disjunct is
  narrowed by exactly the operator the branch transfer applies to a whole
  condition, and the results are joined. This is the shape Goblint's \<open>inv_exp\<close>
  has for \<open>LOr\<close> -- refine each arm, drop an arm whose refinement raises
  \<open>Deadcode\<close> -- with \<open>bot\<close> in place of the exception, since \<open>bot\<close> is the unit
  of \<open>\<squnion>\<close>. Downstream mirrors and their correctness proofs cite these rather
  than re-deriving the gate from \<open>bfilter\<close>'s primitive equations.
\<close>

lemma bfilter_And_False_branch:
  "bfilter \<Gamma> (And b1 b2) False \<sigma> = branch \<Gamma> b1 False \<sigma> \<squnion> branch \<Gamma> b2 False \<sigma>"
  by (simp add: branch_unfold)

lemma bfilter_Or_True_branch:
  "bfilter \<Gamma> (Or b1 b2) True \<sigma> = branch \<Gamma> b1 True \<sigma> \<squnion> branch \<Gamma> b2 True \<sigma>"
  by (simp add: branch_unfold)

lemma branch_lifted_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (taval_syn \<Gamma> e s) = pol" "styped \<Gamma> s" "wt_exp \<Gamma> e (opk (esyn \<Gamma> e))"
  shows "s \<in> gamma_state_lift (branch_lifted \<Gamma> e pol \<sigma>)"
proof -
  have "feasible \<Gamma> e pol \<sigma>" by (rule feasible_of_concrete[OF assms(1,2)])
  then show ?thesis
    using bfilter_sound[OF assms(1,2,3,4)] by (simp add: branch_lifted_def)
qed

lemma branch_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (taval_syn \<Gamma> e s) = pol" "styped \<Gamma> s" "wt_exp \<Gamma> e (opk (esyn \<Gamma> e))"
  shows "s \<in> \<lbrakk>branch \<Gamma> e pol \<sigma>\<rbrakk>"
proof -
  have "s \<in> gamma_state_lift (branch_lifted \<Gamma> e pol \<sigma>)" by (rule branch_lifted_sound[OF assms])
  then show ?thesis
    unfolding branch_def by (cases "branch_lifted \<Gamma> e pol \<sigma>") simp_all
qed

text \<open>
  \<open>branch\<close> only ever narrows further than \<open>bfilter\<close>: it either falls
  through to \<open>bfilter\<close> unchanged, or short-circuits to \<open>bot\<close>, and \<open>bot\<close> is
  least. Callers that only need an upper bound on \<open>branch\<close>'s result -- e.g.
  post-fixpoint checks -- can reuse their existing \<open>bfilter\<close>-level
  reasoning through this fact instead of re-deriving it against \<open>branch\<close>'s
  case split.
\<close>

lemma branch_le_bfilter: "branch \<Gamma> e pol \<sigma> \<le> bfilter \<Gamma> e pol \<sigma>"
  unfolding branch_unfold by (auto split: option.splits)

end


subsection \<open>Conservative inverse operator\<close>

text \<open>
  A domain that is too coarse for useful arithmetic inversion (e.g. sign,
  which cannot narrow either operand of a plus/minus/times from its result)
  instantiates @{term inv_plus} / @{term inv_minus} / @{term inv_times} with
  this shared no-op: both operands pass through unchanged. Any
  @{class sound_domain} discharges its soundness for free, so domains share
  one proof instead of each restating the same trivial obligation.
\<close>

definition inv_conservative :: "ikind => 'a => 'a => 'a => 'a * 'a" where
  "inv_conservative ik r a1 a2 = (a1, a2)"

lemma inv_conservative_sound:
  fixes a1 a2 :: "'a::sound_domain"
  assumes "n1 \<in> gamma a1" and "n2 \<in> gamma a2"
  shows
    "n1 \<in> gamma (fst (inv_conservative ik r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_conservative ik r a1 a2))"
  using assms by (simp add: inv_conservative_def)

lemma inv_conservative_reductive1:
  fixes a1 a2 :: "'a::sound_domain"
  shows "fst (inv_conservative ik r a1 a2) \<le> a1"
  by (simp add: inv_conservative_def)

lemma inv_conservative_reductive2:
  fixes a1 a2 :: "'a::sound_domain"
  shows "snd (inv_conservative ik r a1 a2) \<le> a2"
  by (simp add: inv_conservative_def)

text \<open>
  The same no-op shape for \<open>inv_eq\<close>: unlike \<open>inv_plus\<close>/\<open>inv_minus\<close>/\<open>inv_times\<close>,
  \<open>inv_eq\<close>'s first argument is \<open>bool\<close> (the assumed truth value, as for
  \<open>inv_less\<close>), not \<open>'a\<close>, so \<open>inv_conservative\<close> cannot be reused verbatim ---
  its three arguments all share one type. A domain not yet ready with a real
  equality narrowing (or one too coarse for it to help) instantiates \<open>inv_eq\<close>
  with this identity instead.
\<close>

definition inv_eq_identity :: "bool => 'a => 'a => 'a * 'a" where
  "inv_eq_identity res a1 a2 = (a1, a2)"

lemma inv_eq_identity_sound:
  fixes a1 a2 :: "'a::sound_domain"
  assumes "n1 \<in> gamma a1" and "n2 \<in> gamma a2"
  shows "n1 \<in> gamma (fst (inv_eq_identity res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq_identity res a1 a2))"
  using assms by (simp add: inv_eq_identity_def)

subsection \<open>Pairwise order for reductive/monotone inverse operators\<close>

text \<open>
  A minimal componentwise order on \<open>'a * 'a\<close>, used only to state each inverse
  operator's monotonicity and reductiveness as a single fact about its returned
  pair rather than as two separately-assumed projections. Deliberately not
  \<open>'a * 'a\<close>'s own \<open>\<le>\<close>: some already-transitively-imported theory instantiates
  \<open>('a,'b) prod :: order\<close> here with a non-componentwise (order-with-a-\<open><\<close>-disjunct)
  definition, so relying on the ambient \<open>\<le>\<close> would silently pick up the wrong
  relation. This local, self-contained \<open>\<le>_pair\<close> avoids that entirely.
\<close>

definition le_pair :: "'a::order \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "le_pair p q \<longleftrightarrow> fst p \<le> fst q \<and> snd p \<le> snd q"

lemma le_pairI: "fst p \<le> fst q \<Longrightarrow> snd p \<le> snd q \<Longrightarrow> le_pair p q"
  unfolding le_pair_def by simp

lemma le_pair_fst: "le_pair p q \<Longrightarrow> fst p \<le> fst q"
  unfolding le_pair_def by simp

lemma le_pair_snd: "le_pair p q \<Longrightarrow> snd p \<le> snd q"
  unfolding le_pair_def by simp

subsection \<open>Refined backward-analysis locale\<close>

text \<open>
  Extends @{locale backward_domain} with two orthogonal strengthenings of the
  domain-author operators, bundled into one locale so a concrete domain proves
  both against a single interpretation rather than reproving @{locale
  backward_domain}'s base soundness once per strengthening:

    - Monotonicity: the generic @{term afilter} / @{term bfilter} are then
      monotone in the abstract state (and target value) by the same induction
      that proves their soundness.

    - Reductiveness: each operator's result is below the input operand it
      refines -- refinement narrows, never enlarges. Bottom-preservation for
      \<open>intersect\<close>/\<open>inv_*\<close> -- needed so a compound \<open>afilter\<close>/\<open>bfilter\<close>'s recursive
      re-narrowing of an already-dead location cannot revive it -- follows
      generically from this via @{thm is_bot_mono} and \<open>bot\<close>'s leastness,
      rather than as separate per-operator bottom axioms.

  Each \<open>inv_*\<close> operator's mono/reductive contract is one @{const le_pair} fact
  about its returned pair rather than two separately-assumed \<open>fst\<close>/\<open>snd\<close>
  projections; the componentwise facts \<open>afilter_mono\<close>/\<open>bfilter_mono\<close>'s own
  induction needs are derived from these once, inside this locale.
\<close>

locale backward_domain_refined = backward_domain +
  assumes intersect_mono[intro]:
      "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> intersect a1 b1 \<le> intersect a2 b2"
  and aval_abs_mono[intro]:
      "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> aval_abs \<Gamma> ik e \<sigma>1 \<le> aval_abs \<Gamma> ik e \<sigma>2"
  and inv_less_mono:
      "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_less res x1 y1) (inv_less res x2 y2)"
  and inv_eq_mono:
      "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_eq res x1 y1) (inv_eq res x2 y2)"
  and inv_plus_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
       le_pair (inv_plus ik r1 x1 y1) (inv_plus ik r2 x2 y2)"
  and inv_minus_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
       le_pair (inv_minus ik r1 x1 y1) (inv_minus ik r2 x2 y2)"
  and inv_times_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
       le_pair (inv_times ik r1 x1 y1) (inv_times ik r2 x2 y2)"
  and intersect_reductive1[intro]: "intersect a b \<le> a"
  and intersect_reductive2[intro]: "intersect a b \<le> b"
  and inv_less_reductive: "le_pair (inv_less res a1 a2) (a1, a2)"
  and inv_eq_reductive: "le_pair (inv_eq res a1 a2) (a1, a2)"
  and inv_plus_reductive: "le_pair (inv_plus ik r a1 a2) (a1, a2)"
  and inv_minus_reductive: "le_pair (inv_minus ik r a1 a2) (a1, a2)"
  and inv_times_reductive: "le_pair (inv_times ik r a1 a2) (a1, a2)"
  and tobool_mono:
      "\<not> is_bot (p1::'a) \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some (bv::bool) \<Longrightarrow> tobool p1 = Some bv"
begin

text \<open>Componentwise projections of each pair-shaped reductive assumption, used by the
  bottom-preservation lemmas below.\<close>

lemma inv_less_reductive1: "fst (inv_less res a1 a2) \<le> a1"
  using le_pair_fst[OF inv_less_reductive] by simp
lemma inv_less_reductive2: "snd (inv_less res a1 a2) \<le> a2"
  using le_pair_snd[OF inv_less_reductive] by simp

lemma inv_eq_reductive1: "fst (inv_eq res a1 a2) \<le> a1"
  using le_pair_fst[OF inv_eq_reductive] by simp
lemma inv_eq_reductive2: "snd (inv_eq res a1 a2) \<le> a2"
  using le_pair_snd[OF inv_eq_reductive] by simp

lemma inv_plus_reductive1: "fst (inv_plus ik r a1 a2) \<le> a1"
  using le_pair_fst[OF inv_plus_reductive] by simp
lemma inv_plus_reductive2: "snd (inv_plus ik r a1 a2) \<le> a2"
  using le_pair_snd[OF inv_plus_reductive] by simp

lemma inv_minus_reductive1: "fst (inv_minus ik r a1 a2) \<le> a1"
  using le_pair_fst[OF inv_minus_reductive] by simp
lemma inv_minus_reductive2: "snd (inv_minus ik r a1 a2) \<le> a2"
  using le_pair_snd[OF inv_minus_reductive] by simp

lemma inv_times_reductive1: "fst (inv_times ik r a1 a2) \<le> a1"
  using le_pair_fst[OF inv_times_reductive] by simp
lemma inv_times_reductive2: "snd (inv_times ik r a1 a2) \<le> a2"
  using le_pair_snd[OF inv_times_reductive] by simp

text \<open>Componentwise conjunctions of each pair-shaped monotonicity assumption, used by
  \<open>afilter_mono\<close>/\<open>bfilter_mono\<close>'s own induction below.\<close>

lemma inv_less_mono_conj:
  "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
   fst (inv_less res x1 y1) \<le> fst (inv_less res x2 y2) \<and>
   snd (inv_less res x1 y1) \<le> snd (inv_less res x2 y2)"
  using inv_less_mono le_pair_fst le_pair_snd by blast

lemma inv_eq_mono_conj:
  "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
   fst (inv_eq res x1 y1) \<le> fst (inv_eq res x2 y2) \<and>
   snd (inv_eq res x1 y1) \<le> snd (inv_eq res x2 y2)"
  using inv_eq_mono le_pair_fst le_pair_snd by blast

lemma inv_plus_mono_conj:
  "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
   fst (inv_plus ik r1 x1 y1) \<le> fst (inv_plus ik r2 x2 y2) \<and>
   snd (inv_plus ik r1 x1 y1) \<le> snd (inv_plus ik r2 x2 y2)"
  using inv_plus_mono le_pair_fst le_pair_snd by metis

lemma inv_minus_mono_conj:
  "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
   fst (inv_minus ik r1 x1 y1) \<le> fst (inv_minus ik r2 x2 y2) \<and>
   snd (inv_minus ik r1 x1 y1) \<le> snd (inv_minus ik r2 x2 y2)"
  using inv_minus_mono le_pair_fst le_pair_snd by metis

lemma inv_times_mono_conj:
  "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
   fst (inv_times ik r1 x1 y1) \<le> fst (inv_times ik r2 x2 y2) \<and>
   snd (inv_times ik r1 x1 y1) \<le> snd (inv_times ik r2 x2 y2)"
  using inv_times_mono le_pair_fst le_pair_snd by metis

text \<open>Bottom-preservation, bare (not \<open>[intro]\<close>): @{term "intersect_bot1"}/@{term "intersect_bot2"}
  conclude the same @{term is_bot} goal from different premises, so tagging both would
  make \<open>blast\<close>/\<open>auto\<close> search ambiguous wherever these are pulled in unqualified; cited
  by name instead, matching this file's existing convention for non-searched facts.\<close>

lemma intersect_bot1: "is_bot a \<Longrightarrow> is_bot (intersect a b)"
  using intersect_reductive1 is_bot_mono by blast
lemma intersect_bot2: "is_bot b \<Longrightarrow> is_bot (intersect a b)"
  using intersect_reductive2 is_bot_mono by blast

lemma inv_less_fst_bot: "is_bot a1 \<Longrightarrow> is_bot (fst (inv_less res a1 a2))"
  using inv_less_reductive1 is_bot_mono by blast
lemma inv_less_snd_bot: "is_bot a2 \<Longrightarrow> is_bot (snd (inv_less res a1 a2))"
  using inv_less_reductive2 is_bot_mono by blast

lemma inv_eq_fst_bot: "is_bot a1 \<Longrightarrow> is_bot (fst (inv_eq res a1 a2))"
  using inv_eq_reductive1 is_bot_mono by blast
lemma inv_eq_snd_bot: "is_bot a2 \<Longrightarrow> is_bot (snd (inv_eq res a1 a2))"
  using inv_eq_reductive2 is_bot_mono by blast

lemma inv_plus_fst_bot: "is_bot a1 \<Longrightarrow> is_bot (fst (inv_plus ik r a1 a2))"
  using inv_plus_reductive1 is_bot_mono by blast
lemma inv_plus_snd_bot: "is_bot a2 \<Longrightarrow> is_bot (snd (inv_plus ik r a1 a2))"
  using inv_plus_reductive2 is_bot_mono by blast

lemma inv_minus_fst_bot: "is_bot a1 \<Longrightarrow> is_bot (fst (inv_minus ik r a1 a2))"
  using inv_minus_reductive1 is_bot_mono by blast
lemma inv_minus_snd_bot: "is_bot a2 \<Longrightarrow> is_bot (snd (inv_minus ik r a1 a2))"
  using inv_minus_reductive2 is_bot_mono by blast

lemma inv_times_fst_bot: "is_bot a1 \<Longrightarrow> is_bot (fst (inv_times ik r a1 a2))"
  using inv_times_reductive1 is_bot_mono by blast
lemma inv_times_snd_bot: "is_bot a2 \<Longrightarrow> is_bot (snd (inv_times ik r a1 a2))"
  using inv_times_reductive2 is_bot_mono by blast

text \<open>Expose the @{term afilter} arithmetic recursions in @{term fst} / @{term snd} form.\<close>
lemma afilter_Plus_unfold:
  "afilter \<Gamma> ik (Plus e1 e2) a \<sigma> =
     afilter \<Gamma> ik e1 (fst (inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)))
               (afilter \<Gamma> ik e2 (snd (inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_Minus_unfold:
  "afilter \<Gamma> ik (Minus e1 e2) a \<sigma> =
     afilter \<Gamma> ik e1 (fst (inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)))
               (afilter \<Gamma> ik e2 (snd (inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_Times_unfold:
  "afilter \<Gamma> ik (Times e1 e2) a \<sigma> =
     afilter \<Gamma> ik e1 (fst (inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)))
               (afilter \<Gamma> ik e2 (snd (inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma bfilter_Less_unfold:
  "bfilter \<Gamma> (Less e1 e2) res \<sigma> =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2)) in
      afilter \<Gamma> k e1 (fst (inv_less res (aval_abs \<Gamma> k e1 \<sigma>) (aval_abs \<Gamma> k e2 \<sigma>)))
               (afilter \<Gamma> k e2 (snd (inv_less res (aval_abs \<Gamma> k e1 \<sigma>) (aval_abs \<Gamma> k e2 \<sigma>))) \<sigma>))"
  by (simp add: Let_def case_prod_beta)

lemma bfilter_Eq_unfold:
  "bfilter \<Gamma> (Eq e1 e2) res \<sigma> =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2)) in
      afilter \<Gamma> k e1 (fst (inv_eq res (aval_abs \<Gamma> k e1 \<sigma>) (aval_abs \<Gamma> k e2 \<sigma>)))
               (afilter \<Gamma> k e2 (snd (inv_eq res (aval_abs \<Gamma> k e1 \<sigma>) (aval_abs \<Gamma> k e2 \<sigma>))) \<sigma>))"
  by (simp add: Let_def case_prod_beta)

lemma afilter_mono:
  "a1 \<le> a2 \<Longrightarrow> \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> afilter \<Gamma> ik e a1 \<sigma>1 \<le> afilter \<Gamma> ik e a2 \<sigma>2"
proof (induction e arbitrary: ik a1 a2 \<sigma>1 \<sigma>2)
  case (N n)
  then show ?case by simp
next
  case (V x)
  show ?case
    unfolding afilter.simps
  proof (rule le_funI)
    fix y
    show "(\<sigma>1(x := intersect a1 (\<sigma>1 x))) y \<le> (\<sigma>2(x := intersect a2 (\<sigma>2 x))) y"
    proof (cases "y = x")
      case True
      thus ?thesis using intersect_mono[OF V.prems(1) le_funD[OF V.prems(2)]] by simp
    next
      case False thus ?thesis using le_funD[OF V.prems(2)] by simp
    qed
  qed
next
  case (Plus e1 e2)
  have v1: "aval_abs \<Gamma> ik e1 \<sigma>1 \<le> aval_abs \<Gamma> ik e1 \<sigma>2" by (rule aval_abs_mono[OF Plus.prems(2)])
  have v2: "aval_abs \<Gamma> ik e2 \<sigma>1 \<le> aval_abs \<Gamma> ik e2 \<sigma>2" by (rule aval_abs_mono[OF Plus.prems(2)])
  have iv: "fst (inv_plus ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))
              \<le> fst (inv_plus ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))
          \<and> snd (inv_plus ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))
              \<le> snd (inv_plus ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))"
    by (rule inv_plus_mono_conj[OF Plus.prems(1) v1 v2])
  have step: "afilter \<Gamma> ik e2 (snd (inv_plus ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))) \<sigma>1
            \<le> afilter \<Gamma> ik e2 (snd (inv_plus ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))) \<sigma>2"
    by (rule Plus.IH(2)[OF conjunct2[OF iv] Plus.prems(2)])
  show ?case unfolding afilter_Plus_unfold
    by (rule Plus.IH(1)[OF conjunct1[OF iv] step])
next
  case (Minus e1 e2)
  have v1: "aval_abs \<Gamma> ik e1 \<sigma>1 \<le> aval_abs \<Gamma> ik e1 \<sigma>2" by (rule aval_abs_mono[OF Minus.prems(2)])
  have v2: "aval_abs \<Gamma> ik e2 \<sigma>1 \<le> aval_abs \<Gamma> ik e2 \<sigma>2" by (rule aval_abs_mono[OF Minus.prems(2)])
  have iv: "fst (inv_minus ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))
              \<le> fst (inv_minus ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))
          \<and> snd (inv_minus ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))
              \<le> snd (inv_minus ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))"
    by (rule inv_minus_mono_conj[OF Minus.prems(1) v1 v2])
  have step: "afilter \<Gamma> ik e2 (snd (inv_minus ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))) \<sigma>1
            \<le> afilter \<Gamma> ik e2 (snd (inv_minus ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))) \<sigma>2"
    by (rule Minus.IH(2)[OF conjunct2[OF iv] Minus.prems(2)])
  show ?case unfolding afilter_Minus_unfold
    by (rule Minus.IH(1)[OF conjunct1[OF iv] step])
next
  case (Times e1 e2)
  have v1: "aval_abs \<Gamma> ik e1 \<sigma>1 \<le> aval_abs \<Gamma> ik e1 \<sigma>2" by (rule aval_abs_mono[OF Times.prems(2)])
  have v2: "aval_abs \<Gamma> ik e2 \<sigma>1 \<le> aval_abs \<Gamma> ik e2 \<sigma>2" by (rule aval_abs_mono[OF Times.prems(2)])
  have iv: "fst (inv_times ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))
              \<le> fst (inv_times ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))
          \<and> snd (inv_times ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))
              \<le> snd (inv_times ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))"
    by (rule inv_times_mono_conj[OF Times.prems(1) v1 v2])
  have step: "afilter \<Gamma> ik e2 (snd (inv_times ik a1 (aval_abs \<Gamma> ik e1 \<sigma>1) (aval_abs \<Gamma> ik e2 \<sigma>1))) \<sigma>1
            \<le> afilter \<Gamma> ik e2 (snd (inv_times ik a2 (aval_abs \<Gamma> ik e1 \<sigma>2) (aval_abs \<Gamma> ik e2 \<sigma>2))) \<sigma>2"
    by (rule Times.IH(2)[OF conjunct2[OF iv] Times.prems(2)])
  show ?case unfolding afilter_Times_unfold
    by (rule Times.IH(1)[OF conjunct1[OF iv] step])
next
  case (Less e1 e2) then show ?case by simp
next
  case (Eq e1 e2) then show ?case by simp
next
  case (Not e) then show ?case by simp
next
  case (And e1 e2) then show ?case by simp
next
  case (Or e1 e2) then show ?case by simp
qed

text \<open>
  Monotonicity companion to \<open>bfilter_default_sound\<close>: the same \<open>inv_eq\<close>-
  against-\<open>0\<close> reduction is monotone in \<open>\<sigma>\<close>, following directly from
  \<open>aval_abs_mono\<close>, \<open>inv_eq_mono\<close>, and \<open>afilter_mono\<close>.
\<close>
lemma bfilter_default_mono:
  assumes "\<sigma>1 \<le> \<sigma>2"
  shows "afilter \<Gamma> (opk (esyn \<Gamma> e)) e
           (fst (inv_eq (\<not> res) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) e \<sigma>1) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) (N 0) \<sigma>1))) \<sigma>1
       \<le> afilter \<Gamma> (opk (esyn \<Gamma> e)) e
           (fst (inv_eq (\<not> res) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) e \<sigma>2) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) (N 0) \<sigma>2))) \<sigma>2"
proof -
  let ?ik = "opk (esyn \<Gamma> e)"
  have v1: "aval_abs \<Gamma> ?ik e \<sigma>1 \<le> aval_abs \<Gamma> ?ik e \<sigma>2" by (rule aval_abs_mono[OF assms])
  have v0: "aval_abs \<Gamma> ?ik (N 0) \<sigma>1 \<le> aval_abs \<Gamma> ?ik (N 0) \<sigma>2" by (rule aval_abs_mono[OF assms])
  have iv: "fst (inv_eq (\<not> res) (aval_abs \<Gamma> ?ik e \<sigma>1) (aval_abs \<Gamma> ?ik (N 0) \<sigma>1))
              \<le> fst (inv_eq (\<not> res) (aval_abs \<Gamma> ?ik e \<sigma>2) (aval_abs \<Gamma> ?ik (N 0) \<sigma>2))"
    using inv_eq_mono_conj[OF v1 v0] by simp
  show ?thesis by (rule afilter_mono[OF iv assms])
qed

text \<open>
  The forward gate is monotone in the direction its call sites need: a state
  whose forward value already rules the selected polarity out cannot become
  feasible by shrinking. \<open>is_bot_mono\<close> settles the bottom case and
  \<open>tobool_mono\<close> the definite-answer case. \<open>tobool_mono\<close> explicitly excludes
  bottom operands -- an author's \<open>tobool\<close> may answer arbitrarily there, since
  \<open>gamma bot = {}\<close> makes every answer vacuously sound -- which is why
  \<open>feasible\<close> tests \<open>is_bot\<close> first rather than relying on \<open>tobool\<close> to agree
  across a bottom/non-bottom pair.
\<close>

lemma feasible_mono:
  assumes "sigma1 \<le> sigma2" and "feasible \<Gamma> e pol sigma1"
  shows "feasible \<Gamma> e pol sigma2"
proof -
  let ?ik = "opk (esyn \<Gamma> e)"
  have v: "aval_abs \<Gamma> ?ik e sigma1 \<le> aval_abs \<Gamma> ?ik e sigma2" by (rule aval_abs_mono[OF assms(1)])  have nb1: "\<not> is_bot (aval_abs \<Gamma> ?ik e sigma1)"
    using assms(2) by (simp add: feasible_def Let_def)
  have nb2: "\<not> is_bot (aval_abs \<Gamma> ?ik e sigma2)" using nb1 is_bot_mono[OF v] by blast
  have "tobool (aval_abs \<Gamma> ?ik e sigma2) \<noteq> Some (\<not> pol)"
  proof
    assume "tobool (aval_abs \<Gamma> ?ik e sigma2) = Some (\<not> pol)"
    then have "tobool (aval_abs \<Gamma> ?ik e sigma1) = Some (\<not> pol)"
      using tobool_mono[OF nb1 v] by simp
    then show False using assms(2) by (simp add: feasible_def)
  qed
  with nb2 show ?thesis by (simp add: feasible_def)
qed

text \<open>
  Monotonicity of a single gated disjunct -- the shape \<open>bfilter\<close>'s two join
  cases need. An infeasible disjunct contributes \<open>bot\<close>, which is below
  everything; a feasible one stays feasible in the larger state.
\<close>

lemma gate_mono:
  assumes "sigma1 \<le> sigma2" and "bfilter \<Gamma> e pol sigma1 \<le> bfilter \<Gamma> e pol sigma2"
  shows "(if feasible \<Gamma> e pol sigma1 then bfilter \<Gamma> e pol sigma1 else bot)
           \<le> (if feasible \<Gamma> e pol sigma2 then bfilter \<Gamma> e pol sigma2 else bot)"
proof (cases "feasible \<Gamma> e pol sigma1")
  case True
  have "feasible \<Gamma> e pol sigma2" by (rule feasible_mono[OF assms(1) True])
  with True assms(2) show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed
lemma bfilter_mono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> bfilter \<Gamma> b res \<sigma>1 \<le> bfilter \<Gamma> b res \<sigma>2"
proof (induction b arbitrary: res \<sigma>1 \<sigma>2)
  case (N n) show ?case
    using bfilter_default_mono[where e = "N n" and res = res, OF N.prems]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (V x) show ?case
    using bfilter_default_mono[where e = "V x" and res = res, OF V.prems]
    by (simp add: bfilter.simps Let_def case_prod_beta fun_upd_def)
next
  case (Plus e1 e2) show ?case
    using bfilter_default_mono[where e = "Plus e1 e2" and res = res, OF Plus.prems]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (Minus e1 e2) show ?case
    using bfilter_default_mono[where e = "Minus e1 e2" and res = res, OF Minus.prems]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (Times e1 e2) show ?case
    using bfilter_default_mono[where e = "Times e1 e2" and res = res, OF Times.prems]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (Not b) show ?case unfolding bfilter.simps by (rule Not.IH[OF Not.prems])
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    have c: "bfilter \<Gamma> b2 True \<sigma>1 \<le> bfilter \<Gamma> b2 True \<sigma>2" by (rule And.IH(2)[OF And.prems])
    have "bfilter \<Gamma> b1 True (bfilter \<Gamma> b2 True \<sigma>1) \<le> bfilter \<Gamma> b1 True (bfilter \<Gamma> b2 True \<sigma>2)"
      by (rule And.IH(1)[OF c])
    thus ?thesis using True by simp
  next
    case False
    have c1: "(if feasible \<Gamma> b1 False \<sigma>1 then bfilter \<Gamma> b1 False \<sigma>1 else bot)
                \<le> (if feasible \<Gamma> b1 False \<sigma>2 then bfilter \<Gamma> b1 False \<sigma>2 else bot)"
      by (rule gate_mono[OF And.prems And.IH(1)[OF And.prems]])
    have c2: "(if feasible \<Gamma> b2 False \<sigma>1 then bfilter \<Gamma> b2 False \<sigma>1 else bot)
                \<le> (if feasible \<Gamma> b2 False \<sigma>2 then bfilter \<Gamma> b2 False \<sigma>2 else bot)"
      by (rule gate_mono[OF And.prems And.IH(2)[OF And.prems]])
    have eq1: "bfilter \<Gamma> (And b1 b2) res \<sigma>1
                 = (if feasible \<Gamma> b1 False \<sigma>1 then bfilter \<Gamma> b1 False \<sigma>1 else bot)
                   \<squnion> (if feasible \<Gamma> b2 False \<sigma>1 then bfilter \<Gamma> b2 False \<sigma>1 else bot)"
      using False by simp
    have eq2: "bfilter \<Gamma> (And b1 b2) res \<sigma>2
                 = (if feasible \<Gamma> b1 False \<sigma>2 then bfilter \<Gamma> b1 False \<sigma>2 else bot)
                   \<squnion> (if feasible \<Gamma> b2 False \<sigma>2 then bfilter \<Gamma> b2 False \<sigma>2 else bot)"
      using False by simp
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    have c1: "(if feasible \<Gamma> b1 True \<sigma>1 then bfilter \<Gamma> b1 True \<sigma>1 else bot)
                \<le> (if feasible \<Gamma> b1 True \<sigma>2 then bfilter \<Gamma> b1 True \<sigma>2 else bot)"
      by (rule gate_mono[OF Or.prems Or.IH(1)[OF Or.prems]])
    have c2: "(if feasible \<Gamma> b2 True \<sigma>1 then bfilter \<Gamma> b2 True \<sigma>1 else bot)
                \<le> (if feasible \<Gamma> b2 True \<sigma>2 then bfilter \<Gamma> b2 True \<sigma>2 else bot)"
      by (rule gate_mono[OF Or.prems Or.IH(2)[OF Or.prems]])
    have eq1: "bfilter \<Gamma> (Or b1 b2) res \<sigma>1
                 = (if feasible \<Gamma> b1 True \<sigma>1 then bfilter \<Gamma> b1 True \<sigma>1 else bot)
                   \<squnion> (if feasible \<Gamma> b2 True \<sigma>1 then bfilter \<Gamma> b2 True \<sigma>1 else bot)"
      using True by simp
    have eq2: "bfilter \<Gamma> (Or b1 b2) res \<sigma>2
                 = (if feasible \<Gamma> b1 True \<sigma>2 then bfilter \<Gamma> b1 True \<sigma>2 else bot)
                   \<squnion> (if feasible \<Gamma> b2 True \<sigma>2 then bfilter \<Gamma> b2 True \<sigma>2 else bot)"
      using True by simp
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])  next
    case False
    have c: "bfilter \<Gamma> b2 False \<sigma>1 \<le> bfilter \<Gamma> b2 False \<sigma>2" by (rule Or.IH(2)[OF Or.prems])
    have "bfilter \<Gamma> b1 False (bfilter \<Gamma> b2 False \<sigma>1) \<le> bfilter \<Gamma> b1 False (bfilter \<Gamma> b2 False \<sigma>2)"
      by (rule Or.IH(1)[OF c])
    thus ?thesis using False by simp
  qed
next
  case (Less e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have v1: "aval_abs \<Gamma> ?k e1 \<sigma>1 \<le> aval_abs \<Gamma> ?k e1 \<sigma>2" by (rule aval_abs_mono[OF Less.prems])
  have v2: "aval_abs \<Gamma> ?k e2 \<sigma>1 \<le> aval_abs \<Gamma> ?k e2 \<sigma>2" by (rule aval_abs_mono[OF Less.prems])
  have iv: "fst (inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>1) (aval_abs \<Gamma> ?k e2 \<sigma>1))
              \<le> fst (inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>2) (aval_abs \<Gamma> ?k e2 \<sigma>2))
          \<and> snd (inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>1) (aval_abs \<Gamma> ?k e2 \<sigma>1))
              \<le> snd (inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>2) (aval_abs \<Gamma> ?k e2 \<sigma>2))"
    by (rule inv_less_mono_conj[OF v1 v2])
  have step: "afilter \<Gamma> ?k e2 (snd (inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>1) (aval_abs \<Gamma> ?k e2 \<sigma>1))) \<sigma>1
            \<le> afilter \<Gamma> ?k e2 (snd (inv_less res (aval_abs \<Gamma> ?k e1 \<sigma>2) (aval_abs \<Gamma> ?k e2 \<sigma>2))) \<sigma>2"
    by (rule afilter_mono[OF conjunct2[OF iv] Less.prems])
  show ?case unfolding bfilter_Less_unfold Let_def
    by (rule afilter_mono[OF conjunct1[OF iv] step])
next
  case (Eq e1 e2)
  let ?k = "opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))"
  have v1: "aval_abs \<Gamma> ?k e1 \<sigma>1 \<le> aval_abs \<Gamma> ?k e1 \<sigma>2" by (rule aval_abs_mono[OF Eq.prems])
  have v2: "aval_abs \<Gamma> ?k e2 \<sigma>1 \<le> aval_abs \<Gamma> ?k e2 \<sigma>2" by (rule aval_abs_mono[OF Eq.prems])
  have iv: "fst (inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>1) (aval_abs \<Gamma> ?k e2 \<sigma>1))
              \<le> fst (inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>2) (aval_abs \<Gamma> ?k e2 \<sigma>2))
          \<and> snd (inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>1) (aval_abs \<Gamma> ?k e2 \<sigma>1))
              \<le> snd (inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>2) (aval_abs \<Gamma> ?k e2 \<sigma>2))"
    by (rule inv_eq_mono_conj[OF v1 v2])
  have step: "afilter \<Gamma> ?k e2 (snd (inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>1) (aval_abs \<Gamma> ?k e2 \<sigma>1))) \<sigma>1
            \<le> afilter \<Gamma> ?k e2 (snd (inv_eq res (aval_abs \<Gamma> ?k e1 \<sigma>2) (aval_abs \<Gamma> ?k e2 \<sigma>2))) \<sigma>2"
    by (rule afilter_mono[OF conjunct2[OF iv] Eq.prems])
  show ?case unfolding bfilter_Eq_unfold Let_def
    by (rule afilter_mono[OF conjunct1[OF iv] step])
qed

text \<open>
  \<open>branch_lifted\<close>'s gate is the same \<open>feasible\<close> test \<open>bfilter\<close>'s join cases
  apply per disjunct, so its monotonicity is \<open>feasible_mono\<close> and
  \<open>bfilter_mono\<close> together. \<open>branch_mono\<close> follows: \<open>branch\<close>'s
  \<open>Bot => bot | Lifted s => s\<close> projection is itself monotone (\<open>Bot\<close> is least,
  so it can only project below whatever the \<open>Lifted\<close> side projects to).
\<close>
lemma branch_lifted_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch_lifted \<Gamma> e pol sigma1 \<le> branch_lifted \<Gamma> e pol sigma2"
proof (cases "feasible \<Gamma> e pol sigma1")
  case False
  then show ?thesis by (simp add: branch_lifted_def)
next
  case True
  have "feasible \<Gamma> e pol sigma2" by (rule feasible_mono[OF assms True])
  with True show ?thesis
    by (simp add: branch_lifted_def bfilter_mono[OF assms])
qed
lemma branch_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch \<Gamma> e pol sigma1 \<le> branch \<Gamma> e pol sigma2"
proof -
  have lm: "branch_lifted \<Gamma> e pol sigma1 \<le> branch_lifted \<Gamma> e pol sigma2"
    by (rule branch_lifted_mono[OF assms])
  show ?thesis
    unfolding branch_def
    using lm by (cases "branch_lifted \<Gamma> e pol sigma1"; cases "branch_lifted \<Gamma> e pol sigma2") auto
qed


text \<open>
  Reductiveness of the whole recursion, not just its individual \<open>intersect\<close>/\<open>inv_*\<close>
  steps: @{term \<open>afilter e a \<sigma>\<close>}/@{term \<open>bfilter b res \<sigma>\<close>} are always \<le> their
  input state. This is what lets a compound expression's re-narrowing of an
  already-settled location never revive it -- each recursive step only shrinks
  the state further, so once some location is @{const is_bot}, it stays
  @{const is_bot} through every later step (@{thm is_bot_state_mono}).
\<close>

lemma afilter_reductive: "afilter \<Gamma> ik e a \<sigma> \<le> \<sigma>"
proof (induction e arbitrary: ik a \<sigma>)
  case (N n)
  then show ?case by simp
next
  case (V x)
  show ?case
    unfolding afilter.simps
  proof (rule le_funI)
    fix y show "(\<sigma>(x := intersect a (\<sigma> x))) y \<le> \<sigma> y"
      by (cases "y = x") (auto intro: intersect_reductive2)
  qed
next
  case (Plus e1 e2)
  have h2: "afilter \<Gamma> ik e2 (snd (inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma> \<le> \<sigma>"
    by (rule Plus.IH(2))
  have h1: "afilter \<Gamma> ik e1 (fst (inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)))
              (afilter \<Gamma> ik e2 (snd (inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>)
            \<le> afilter \<Gamma> ik e2 (snd (inv_plus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>"
    by (rule Plus.IH(1))
  show ?case unfolding afilter_Plus_unfold by (rule order_trans[OF h1 h2])
next
  case (Minus e1 e2)
  have h2: "afilter \<Gamma> ik e2 (snd (inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma> \<le> \<sigma>"
    by (rule Minus.IH(2))
  have h1: "afilter \<Gamma> ik e1 (fst (inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)))
              (afilter \<Gamma> ik e2 (snd (inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>)
            \<le> afilter \<Gamma> ik e2 (snd (inv_minus ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>"
    by (rule Minus.IH(1))
  show ?case unfolding afilter_Minus_unfold by (rule order_trans[OF h1 h2])
next
  case (Times e1 e2)
  have h2: "afilter \<Gamma> ik e2 (snd (inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma> \<le> \<sigma>"
    by (rule Times.IH(2))
  have h1: "afilter \<Gamma> ik e1 (fst (inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>)))
              (afilter \<Gamma> ik e2 (snd (inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>)
            \<le> afilter \<Gamma> ik e2 (snd (inv_times ik a (aval_abs \<Gamma> ik e1 \<sigma>) (aval_abs \<Gamma> ik e2 \<sigma>))) \<sigma>"
    by (rule Times.IH(1))
  show ?case unfolding afilter_Times_unfold by (rule order_trans[OF h1 h2])
next
  case (Less e1 e2) show ?case by simp
next
  case (Eq e1 e2) show ?case by simp
next
  case (Not e) show ?case by simp
next
  case (And e1 e2) show ?case by simp
next
  case (Or e1 e2) show ?case by simp
qed

text \<open>
  Reductiveness companion to \<open>bfilter_default_sound\<close>: the \<open>inv_eq\<close>-against-\<open>0\<close>
  reduction is exactly an \<open>afilter\<close> call, so reductiveness falls straight out
  of \<open>afilter_reductive\<close> with no further argument.
\<close>
lemma bfilter_default_reductive:
  "afilter \<Gamma> (opk (esyn \<Gamma> e)) e
     (fst (inv_eq (\<not> res) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) e \<sigma>) (aval_abs \<Gamma> (opk (esyn \<Gamma> e)) (N 0) \<sigma>))) \<sigma> \<le> \<sigma>"
  by (rule afilter_reductive)

lemma bfilter_reductive: "bfilter \<Gamma> b res \<sigma> \<le> \<sigma>"
proof (induction b arbitrary: res \<sigma>)
  case (N n) show ?case
    using bfilter_default_reductive[where e = "N n" and res = res]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (V x) show ?case
    using bfilter_default_reductive[where e = "V x" and res = res]
    by (simp add: bfilter.simps Let_def case_prod_beta fun_upd_def)
next
  case (Plus e1 e2) show ?case
    using bfilter_default_reductive[where e = "Plus e1 e2" and res = res]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (Minus e1 e2) show ?case
    using bfilter_default_reductive[where e = "Minus e1 e2" and res = res]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (Times e1 e2) show ?case
    using bfilter_default_reductive[where e = "Times e1 e2" and res = res]
    by (simp add: bfilter.simps Let_def case_prod_beta)
next
  case (Not b)
  show ?case unfolding bfilter.simps by (rule Not.IH)
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    have c: "bfilter \<Gamma> b2 True \<sigma> \<le> \<sigma>" by (rule And.IH(2))
    have "bfilter \<Gamma> b1 True (bfilter \<Gamma> b2 True \<sigma>) \<le> bfilter \<Gamma> b2 True \<sigma>" by (rule And.IH(1))
    also have "... \<le> \<sigma>" by (rule c)
    finally show ?thesis using True by simp
  next
    case False
    have c1: "(if feasible \<Gamma> b1 False \<sigma> then bfilter \<Gamma> b1 False \<sigma> else bot) \<le> \<sigma>"
      using And.IH(1) by simp
    have c2: "(if feasible \<Gamma> b2 False \<sigma> then bfilter \<Gamma> b2 False \<sigma> else bot) \<le> \<sigma>"
      using And.IH(2) by simp
    have e1: "bfilter \<Gamma> (And b1 b2) res \<sigma>
                = (if feasible \<Gamma> b1 False \<sigma> then bfilter \<Gamma> b1 False \<sigma> else bot)
                  \<squnion> (if feasible \<Gamma> b2 False \<sigma> then bfilter \<Gamma> b2 False \<sigma> else bot)"
      using False by simp
    show ?thesis unfolding e1 by (rule sup_least[OF c1 c2])
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    have c1: "(if feasible \<Gamma> b1 True \<sigma> then bfilter \<Gamma> b1 True \<sigma> else bot) \<le> \<sigma>"
      using Or.IH(1) by simp
    have c2: "(if feasible \<Gamma> b2 True \<sigma> then bfilter \<Gamma> b2 True \<sigma> else bot) \<le> \<sigma>"
      using Or.IH(2) by simp
    have e1: "bfilter \<Gamma> (Or b1 b2) res \<sigma>
                = (if feasible \<Gamma> b1 True \<sigma> then bfilter \<Gamma> b1 True \<sigma> else bot)
                  \<squnion> (if feasible \<Gamma> b2 True \<sigma> then bfilter \<Gamma> b2 True \<sigma> else bot)"
      using True by simp
    show ?thesis unfolding e1 by (rule sup_least[OF c1 c2])
  next
    case False
    have c: "bfilter \<Gamma> b2 False \<sigma> \<le> \<sigma>" by (rule Or.IH(2))
    have "bfilter \<Gamma> b1 False (bfilter \<Gamma> b2 False \<sigma>) \<le> bfilter \<Gamma> b2 False \<sigma>" by (rule Or.IH(1))
    also have "... \<le> \<sigma>" by (rule c)
    finally show ?thesis using False by simp
  qed
next
  case (Less e1 e2)
  show ?case unfolding bfilter_Less_unfold Let_def
    by (rule order_trans[OF afilter_reductive afilter_reductive])
next
  case (Eq e1 e2)
  show ?case unfolding bfilter_Eq_unfold Let_def
    by (rule order_trans[OF afilter_reductive afilter_reductive])
qed

end

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
