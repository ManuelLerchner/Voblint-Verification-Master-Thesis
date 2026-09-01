theory Reachability_Lift
  imports Abstract_Domain "HOL-Library.Monad_Syntax"
begin

section \<open>Explicit reachability over an abstract carrier\<close>

text \<open>
  The outer \<open>Bot\<close> represents an unreachable control-flow point; \<open>Lifted a\<close>
  represents a reachable point carrying \<open>a\<close>. The construction provides the
  order, joins, solver updates, concretization, and normalized transfer
  combinators independently of any particular abstract-state representation.
\<close>

text \<open>
  Mirrors Goblint's lifted-domain construction
  (@{url \<open>https://github.com/goblint/analyzer/blob/master/src/framework/analyses.ml\<close>}):
  \<open>module Dom (LD: Lattice.S) = struct include Lattice.LiftConf (...) (LD) ... end\<close>, whose
  outer \<open>`Bot\<close> means dead code and whose \<open>unlift\<close> only accepts \<open>`Lifted x\<close>. Reachability is
  carried as an explicit tag on top of the analysis-local state, not rediscovered from the
  state's own contents. \<open>Bot\<close> mirrors Goblint's lifted \<open>`Bot\<close>; \<open>Lifted\<close> mirrors \<open>`Lifted\<close>.
  Goblint's lift also carries an outer \<open>`Top\<close> for its own pre-analysis bookkeeping; every
  @{class sound_domain} instance here already has its own \<open>top\<close>, so this lift stays
  two-valued. At the raw lifted representation, \<open>Bot\<close> is strictly below every \<open>Lifted a\<close>
  regardless of \<open>a\<close> -- including \<open>Lifted bot\<close>, which remains distinct from \<open>Bot\<close> even
  though \<open>a\<close> is itself locally bottom -- since dead-by-construction and
  reachable-but-locally-bottom are the two concepts this lift exists to keep separate. The
  normalization discipline developed below (\<open>normalize_lift\<close>, \<open>normalized_lift\<close>) then
  layers a stronger, Voblint-specific invariant on top: every solver-facing payload an
  arbitrary caller-supplied predicate \<open>empty_pred\<close> classifies as bottom is additionally
  canonicalized to structural \<open>Bot\<close>, so \<open>Lifted a\<close> with an \<open>empty_pred\<close>-bottom \<open>a\<close> never
  actually escapes a value-producing step in practice, even though the raw datatype and
  order permit it. This theory does not know or assume that \<open>empty_pred\<close> means semantic
  emptiness -- \<open>Nonrelational_Reachability\<close> is where \<open>empty_pred\<close> is instantiated to
  \<open>is_empty_state\<close> and proved to coincide with an empty concretization.
\<close>

subsection \<open>The lifted order and lattice structure\<close>

(* Disable Quickcheck's narrowing plugin because its generated narrowing
   arity collides with the vendored TD solver's class of the same name.
   This affects only Quickcheck infrastructure. *)
datatype (plugins del: quickcheck_narrowing) 'a lifted =
  Bot | Lifted 'a

text \<open>
  The vendored TD solver stores values at sort \<open>bounded_semilattice_sup_bot\<close>
  (@{theory_text \<open>TD_side\<close>}'s \<open>T :: ('x,'g,'d::bounded_semilattice_sup_bot) eqsT\<close>),
  so \<open>lifted\<close> instantiates that combined structure directly in one step --
  order, bottom, and join together -- rather than building it up through the
  three separate parent classes (\<open>order\<close>, \<open>bot\<close>, \<open>semilattice_sup\<close>) and
  bridging them with intermediate \<open>instance\<close> declarations. This intentionally
  gives up the weaker standalone arities that instantiating each parent
  separately would have provided (\<open>'a::type \<Rightarrow> 'a lifted :: bot\<close> and
  \<open>'a::order \<Rightarrow> 'a lifted :: order\<close>), for an arbitrary or merely ordered
  payload; consequently the generic lifted lemmas below (\<open>gamma_lift_mono\<close>,
  \<open>map_lift_mono\<close>, \<open>normalize_lift_mono\<close>, \<open>transfer_lift_mono\<close>,
  \<open>transfer_lift2_mono\<close>) and the standalone widening/narrowing instances are
  stated at \<open>semilattice_sup\<close> as well. A caller that only needs the weak
  standalone \<open>bot\<close> arity does not automatically satisfy this, and has to
  restate at the sort its real call sites already require.
\<close>

instantiation lifted :: (semilattice_sup) bounded_semilattice_sup_bot
begin

fun less_eq_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> bool" where
    "less_eq_lifted Bot _ = True"
  | "less_eq_lifted (Lifted _) Bot = False"
  | "less_eq_lifted (Lifted a) (Lifted b) = (a \<le> b)"

definition less_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> bool" where
  "less_lifted x y = (x \<le> y \<and> \<not> y \<le> x)"

definition bot_lifted :: "'a lifted" where "bot_lifted = Bot"

fun sup_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
    "sup_lifted Bot y = y"
  | "sup_lifted x Bot = x"
  | "sup_lifted (Lifted a) (Lifted b) = Lifted (a \<squnion> b)"

instance
proof intro_classes
  fix x y z :: "'a lifted"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_lifted_def by (rule refl)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) simp_all
  show "x \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" by (cases x; cases y; cases z) simp_all
  show "bot \<le> x" by (cases x) (simp_all add: bot_lifted_def)
qed

end

lemma bot_lifted_eq [simp]: "(bot :: 'a::semilattice_sup lifted) = Bot"
  unfolding bot_lifted_def by (rule refl)

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

instantiation lifted :: ("{semilattice_sup,widening}") widening
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

instantiation lifted :: ("{semilattice_sup,narrowing}") narrowing
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


subsection \<open>Generic concretization\<close>

definition gamma_lift :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a lifted \<Rightarrow> 'b set" where
  "gamma_lift gam x = (case x of Bot \<Rightarrow> {} | Lifted a \<Rightarrow> gam a)"

lemma gamma_lift_Bot [simp]: "gamma_lift gam Bot = {}"
  unfolding gamma_lift_def by simp

lemma gamma_lift_Lifted [simp]: "gamma_lift gam (Lifted a) = gam a"
  unfolding gamma_lift_def by simp


lemma gamma_lift_mono:
  fixes x y :: "'a::semilattice_sup lifted"
  assumes gam_mono: "\<And>a b. a \<le> b \<Longrightarrow> gam a \<subseteq> gam b"
    and le: "x \<le> y"
  shows "gamma_lift gam x \<subseteq> gamma_lift gam y"
  using le by (cases x; cases y) (auto simp: gam_mono)

subsection \<open>Generic reachability combinators\<close>

text \<open>
  \<open>bind_lift\<close> is the reachability monad's Kleisli bind, exactly \<^const>\<open>Option.bind\<close>'s
  shape with \<open>Bot\<close> for \<open>None\<close> and \<open>Lifted\<close> for \<open>Some\<close>: \<open>Bot\<close> in, \<open>Bot\<close> out, without ever
  calling \<open>f\<close> -- matching Goblint's \<open>unlift\<close> being called before dispatch rather than inside
  each analysis's \<open>assign\<close>/\<open>branch\<close>. \<open>map_lift\<close> is its functor counterpart (\<open>Option.map\<close>'s
  analogue), for pushing a total, never-re-collapsing operation through the lift. Both are
  representation-independent: neither one inspects whether a \<open>Lifted\<close> payload happens to be
  semantically empty. That is a separate concern, taken up below in
  \<^emph>\<open>Canonical-bottom normalization\<close>.
\<close>

fun bind_lift :: "'a lifted \<Rightarrow> ('a \<Rightarrow> 'b lifted) \<Rightarrow> 'b lifted" where
  "bind_lift Bot f = Bot"
| "bind_lift (Lifted a) f = f a"

lemma bind_lift_left_identity: "bind_lift (Lifted a) f = f a" by simp

lemma bind_lift_right_identity [simp]: "bind_lift x Lifted = x"
  by (cases x) simp_all

lemma bind_lift_assoc:
  "bind_lift (bind_lift x f) g = bind_lift x (\<lambda>a. bind_lift (f a) g)"
  by (cases x) simp_all

text \<open>
  Registers \<^const>\<open>bind_lift\<close> under \<^const>\<open>Monad_Syntax.bind\<close>'s ad hoc overloading, so
  \<open>x >>= f\<close> and \<open>do { a <- x; f a }\<close> both parse to exactly \<open>bind_lift x f\<close> -- a pure
  syntax translation resolved at elaboration time, so every lemma about \<^const>\<open>bind_lift\<close>
  applies unchanged to code written with \<open>do\<close> notation. Registered here, immediately after
  \<^const>\<open>bind_lift\<close>'s definition, so the reachability combinators below can use \<open>do\<close>
  notation too.
\<close>

adhoc_overloading Monad_Syntax.bind == bind_lift

definition map_lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a lifted \<Rightarrow> 'b lifted" where
  "map_lift f x = do { a <- x; Lifted (f a) }"

lemma map_lift_Bot [simp]: "map_lift f Bot = Bot"
  unfolding map_lift_def by simp

lemma map_lift_Lifted [simp]: "map_lift f (Lifted a) = Lifted (f a)"
  unfolding map_lift_def by simp

lemma map_lift_mono:
  fixes x y :: "'a::semilattice_sup lifted"
  assumes f_mono: "\<And>a b. a \<le> b \<Longrightarrow> f a \<le> (f b :: 'b::semilattice_sup)"
    and le: "x \<le> y"
  shows "map_lift f x \<le> map_lift f y"
  using le by (cases x; cases y) (auto simp: f_mono)

lemma map_lift_sup:
  fixes x y :: "'a::semilattice_sup lifted"
  assumes f_sup: "\<And>a b. f (a \<squnion> b) = (f a \<squnion> f b :: 'b::semilattice_sup)"
  shows "map_lift f (x \<squnion> y) = map_lift f x \<squnion> map_lift f y"
  by (cases x; cases y) (simp_all add: f_sup)

lemma map_lift_id [simp]: "map_lift id x = x"
  by (cases x) simp_all

lemma map_lift_comp [simp]: "map_lift g (map_lift f x) = map_lift (g \<circ> f) x"
  by (cases x) simp_all

subsection \<open>Canonical-bottom normalization\<close>

text \<open>
  \<open>normalize_lift\<close> is the one Voblint-specific piece on top of the generic combinators
  above: it turns a domain-produced witness-bottom raw result back into the canonical
  structural \<open>Bot\<close>, the counterpart of Goblint's transfer functions raising \<open>Deadcode\<close>
  when their own computation lands on bottom. \<open>transfer_lift\<close>/\<open>transfer_lift2\<close> compose
  \<open>bind_lift\<close> with \<open>normalize_lift\<close>: the shape every generic edge/combine dispatcher
  actually calls.
\<close>

definition normalize_lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a lifted" where
  "normalize_lift empty_pred a = (if empty_pred a then Bot else Lifted a)"

lemma normalize_lift_bot [simp]: "empty_pred a \<Longrightarrow> normalize_lift empty_pred a = Bot"
  unfolding normalize_lift_def by simp

lemma normalize_lift_not_bot [simp]:
  "\<not> empty_pred a \<Longrightarrow> normalize_lift empty_pred a = Lifted a"
  unfolding normalize_lift_def by simp

definition transfer_lift ::
  "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a lifted \<Rightarrow> 'b lifted" where
  "transfer_lift empty_pred f x = do { a <- x; normalize_lift empty_pred (f a) }"

definition transfer_lift2 ::
  "('c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a lifted \<Rightarrow> 'b lifted \<Rightarrow> 'c lifted" where
  "transfer_lift2 empty_pred f x y =
     do { a <- x; b <- y; normalize_lift empty_pred (f a b) }"

lemma transfer_lift_Bot [simp]: "transfer_lift empty_pred f Bot = Bot"
  unfolding transfer_lift_def by simp

lemma transfer_lift_Lifted [simp]:
  "transfer_lift empty_pred f (Lifted a) = normalize_lift empty_pred (f a)"
  unfolding transfer_lift_def by simp

lemma transfer_lift2_Bot_left [simp]: "transfer_lift2 empty_pred f Bot y = Bot"
  unfolding transfer_lift2_def by simp

lemma transfer_lift2_Bot_right [simp]: "transfer_lift2 empty_pred f (Lifted a) Bot = Bot"
  unfolding transfer_lift2_def by simp

lemma transfer_lift2_Lifted [simp]:
  "transfer_lift2 empty_pred f (Lifted a) (Lifted b) = normalize_lift empty_pred (f a b)"
  unfolding transfer_lift2_def by simp

text \<open>
  \<open>normalized_lift\<close> names the discipline every solver-facing lifted value is meant to
  keep: \<^const>\<open>Bot\<close> is the \<^emph>\<open>sole\<close> representation this construction lets a caller-supplied
  \<open>empty_pred\<close> classification collapse to -- a \<^const>\<open>Lifted\<close> payload \<open>empty_pred\<close> still calls bottom is a
  representation the framework never lets escape a value-producing step, not a second,
  competing way to say the same thing. \<open>normalize_lift\<close>'s own \<open>if\<close> makes every one of
  its outputs self-normalized: the \<^const>\<open>Lifted\<close> branch only fires when \<open>empty_pred\<close>
  already said no. \<open>transfer_lift\<close>/\<open>transfer_lift2\<close> route every domain transfer step
  through exactly this \<open>if\<close>, so no transfer step can ever hand back a \<^const>\<open>Lifted\<close>
  payload \<open>empty_pred\<close> still calls bottom, regardless of what the pre-lift inputs
  looked like.

  The lemmas below extend this from a single transfer step to every other value-producing
  primitive a solver combines lifted values with: \<open>\<squnion>\<close> (joining several contributions at a
  program point) and \<open>\<nabla>\<Delta>\<close> (the warrowing update rule). Both need only that \<open>empty_pred\<close>
  itself is downward closed under the payload's order (\<open>mono\<close> below) -- exactly
  \<open>is_empty_antimono\<close>'s shape at \<^class>\<open>sound_domain\<close>, or \<open>resolved_st_q_is_bot_for\<close>'s own
  monotonicity once bridged through \<open>fun_of_resolved_st_q_for_mono\<close> -- not any fact
  specific to how \<open>empty_pred\<close> itself is computed.
\<close>

definition normalized_lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lifted \<Rightarrow> bool" where
  "normalized_lift empty_pred x = (case x of Bot \<Rightarrow> True | Lifted a \<Rightarrow> \<not> empty_pred a)"

lemma normalized_lift_Bot [simp]: "normalized_lift empty_pred Bot"
  unfolding normalized_lift_def by simp

lemma normalized_lift_Lifted [simp]:
  "normalized_lift empty_pred (Lifted a) \<longleftrightarrow> \<not> empty_pred a"
  unfolding normalized_lift_def by simp

lemma normalize_lift_normalized [simp]:
  "normalized_lift empty_pred (normalize_lift empty_pred a)"
  unfolding normalize_lift_def by (cases "empty_pred a") simp_all

lemma transfer_lift_normalized [simp]:
  "normalized_lift empty_pred (transfer_lift empty_pred f x)"
  by (cases x) (simp_all add: transfer_lift_def)

lemma transfer_lift2_normalized [simp]:
  "normalized_lift empty_pred (transfer_lift2 empty_pred f x y)"
  by (cases x; cases y) (simp_all add: transfer_lift2_def)

text \<open>
  \<open>canonicalize_lift\<close> re-normalizes an already-lifted value against \<open>empty_pred\<close>: a
  \<^const>\<open>Lifted\<close> payload that has since become witness-bottom (e.g. read from a
  representation that does not itself carry the \<open>transfer_lift\<close> discipline) collapses
  to \<^const>\<open>Bot\<close>, exactly as if it had been produced by a transfer step in the first
  place. It is \<open>transfer_lift empty_pred id\<close>, not a new bottom test: reusing
  \<^const>\<open>transfer_lift\<close> at the identity function is what makes
  \<open>canonicalize_lift_normalized\<close> immediate from \<open>transfer_lift_normalized\<close> rather than
  a second proof of the same fact.
\<close>

definition canonicalize_lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "canonicalize_lift empty_pred = transfer_lift empty_pred id"

lemma canonicalize_lift_Bot [simp]: "canonicalize_lift empty_pred Bot = Bot"
  unfolding canonicalize_lift_def by simp

lemma canonicalize_lift_Lifted [simp]:
  "canonicalize_lift empty_pred (Lifted a) = normalize_lift empty_pred a"
  unfolding canonicalize_lift_def by simp

lemma canonicalize_lift_normalized [simp]:
  "normalized_lift empty_pred (canonicalize_lift empty_pred x)"
  unfolding canonicalize_lift_def by (rule transfer_lift_normalized)

text \<open>
  \<open>\<squnion>\<close> preserves \<open>normalized_lift\<close> from two already-normalized operands: \<^const>\<open>Bot\<close> is
  \<open>\<squnion>\<close>'s identity on \<^typ>\<open>'a lifted\<close> (\<open>sup_lifted.simps\<close>), so the only case needing
  \<open>mono\<close> at all is \<^const>\<open>Lifted\<close>/\<^const>\<open>Lifted\<close>, where \<open>sup_ge1\<close>/\<open>sup_ge2\<close> place each
  operand below the join and \<open>mono\<close>'s contrapositive carries non-bottomness upward.
\<close>

lemma normalized_lift_sup:
  fixes x y :: "'a::semilattice_sup lifted"
  assumes mono: "\<And>a b::'a. a \<le> b \<Longrightarrow> empty_pred b \<Longrightarrow> empty_pred a"
    and nx: "normalized_lift empty_pred x"
    and ny: "normalized_lift empty_pred y"
  shows "normalized_lift empty_pred (x \<squnion> y)"
  using nx ny by (cases x; cases y) (auto dest: mono[OF sup_ge1] mono[OF sup_ge2])

text \<open>
  Generic monotonicity for the reachability dispatch, proved once here instead of at every
  instantiation (\<open>abs_state\<close>, \<open>resolved_st_q\<close>, ...): whenever the underlying transfer is
  monotone and the bottom predicate is downward closed (as \<open>is_empty_state\<close> always is, via
  \<open>is_empty_state_antimono\<close>), \<open>transfer_lift\<close>/\<open>transfer_lift2\<close> are monotone.
\<close>

lemma normalize_lift_mono:
  fixes a b :: "'a::semilattice_sup"
  assumes f_le: "a \<le> b"
    and bot_mono: "empty_pred b \<Longrightarrow> empty_pred a"
  shows "normalize_lift empty_pred a \<le> normalize_lift empty_pred b"
  unfolding normalize_lift_def using f_le bot_mono by auto

lemma transfer_lift_mono:
  fixes x1 x2 :: "'a::semilattice_sup lifted"
  assumes f_mono: "\<And>a b. a \<le> b \<Longrightarrow> f a \<le> f b"
    and bot_mono: "\<And>a b. a \<le> b \<Longrightarrow> empty_pred b \<Longrightarrow> empty_pred a"
    and le: "x1 \<le> x2"
  shows "transfer_lift empty_pred f x1
           \<le> (transfer_lift empty_pred f x2 :: 'b::semilattice_sup lifted)"
  using assms by (cases x1; cases x2) (auto intro!:normalize_lift_mono)

lemma transfer_lift2_mono:
  fixes x1 x2 :: "'a::semilattice_sup lifted" and y1 y2 :: "'b::semilattice_sup lifted"
  assumes f_mono: "\<And>a1 a2 b1 b2. a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> f a1 b1 \<le> f a2 b2"
    and bot_mono: "\<And>a b. a \<le> b \<Longrightarrow> empty_pred b \<Longrightarrow> empty_pred a"
    and lex: "x1 \<le> x2" and ley: "y1 \<le> y2"
  shows "transfer_lift2 empty_pred f x1 y1
           \<le> (transfer_lift2 empty_pred f x2 y2 :: 'c::semilattice_sup lifted)"
  using assms by (cases x1; cases x2; cases y1; cases y2) (auto intro: normalize_lift_mono f_mono bot_mono)

subsection \<open>Solver update integration\<close>

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
  assumes mono: "\<And>a b::'a. a \<le> b \<Longrightarrow> empty_pred b \<Longrightarrow> empty_pred a"
    and ny: "normalized_lift empty_pred y"
  shows "normalized_lift empty_pred (x \<nabla>\<Delta> y)"
  using assms unfolding warrow_def
  by (cases x; cases y)
     (auto dest: mono[OF narrow_ge] mono[OF widen_ge2]
           simp: warrow_idem)

end
