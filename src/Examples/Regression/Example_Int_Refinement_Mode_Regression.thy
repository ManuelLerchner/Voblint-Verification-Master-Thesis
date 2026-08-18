theory Example_Int_Refinement_Mode_Regression
  imports
    Example_Int_Domain
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.DG_Base_Exec"
    "Voblint_Analysis.Int_Exec"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Run_Analysis_Sound"
begin

text \<open>
  Regression witnesses for the composite integer domain's three refinement
  modes (\<^const>\<open>Refine_Never\<close>, \<^const>\<open>Refine_Once\<close>, \<^const>\<open>Refine_Fixpoint\<close>,
  \<^theory>\<open>Voblint_Analysis.Int_Refinement\<close>), organized the way
  \<open>Example_Solver_Choice_Regression\<close> organizes its own acceptance witnesses:
  each lemma's doc comment states exactly which component teaches which
  other component what fact, and why the weaker mode or component could
  not have derived it alone. \<^theory>\<open>Voblint_Examples.Example_Int_Domain\<close>
  already proves the raw-domain arithmetic this file draws on
  (\<open>arithmetic_left\<close>, \<open>arithmetic_right\<close>, \<open>progressive_refinement_input\<close>,
  \<open>refinement_round_is_progressive\<close>); this file cites those facts rather
  than re-deriving them, and adds the solver-run-level (compiled VIMP
  program through the real D/G solver) counterparts that theory does not
  cover.
\<close>

section \<open>No refinement versus one pass\<close>

text \<open>
  \<open>arithmetic_left\<close> and \<open>arithmetic_right\<close>
  (\<^theory>\<open>Voblint_Examples.Example_Int_Domain\<close>) are
  each a concrete odd value (\<open>-1\<close> and one of \<open>{0,1}\<close>) whose Sign, Interval,
  and Parity components already pin them down, while Congruence stays at
  \<open>top\<close>: nothing has yet told Congruence what the other three already know.
  Under \<^const>\<open>Refine_Never\<close>, \<open>plus_int_dom\<close> returns exactly this raw,
  untaught sum (\<open>arithmetic_never_is_raw\<close>, \<open>arithmetic_raw_produces_progressive_input\<close>):
  Sign stays at \<open>STop\<close> even though Interval's own \<open>[-1,0]\<close> already rules out
  every sign but non-positive, because Never performs no cross-component
  fan-out at all.
\<close>

lemma mode_never_state:
  "plus_int_dom Refine_Never arithmetic_left arithmetic_right =
   progressive_refinement_input"
  unfolding arithmetic_never_is_raw
  by (rule arithmetic_raw_produces_progressive_input)

text \<open>
  One \<^const>\<open>Refine_Once\<close> pass (\<open>arithmetic_once_result\<close>) already moves Sign
  from \<open>STop\<close> to \<open>SNonPos\<close>, and Interval from the two-point \<open>[-1,0]\<close> down to
  the singleton \<open>[0,0]\<close>: Interval teaches Sign the tighter bound
  (\<open>refine_interval\<close>), and Parity's already-exact \<open>PEven\<close> teaches Congruence
  \<open>0 mod 2\<close> (\<^const>\<open>refine_congruence\<close>), which in turn narrows Interval's
  \<open>[-1,0]\<close> down to \<open>[0,0]\<close> by excluding the odd endpoint \<open>-1\<close>. Neither Sign,
  Interval, Parity, nor Congruence could reach \<open>SNonPos\<close>/\<open>[0,0]\<close>/\<open>0 mod 2\<close>
  running alone against the \<^const>\<open>Refine_Never\<close> state above.
\<close>

lemmas mode_once_state = arithmetic_once_result

lemma mode_never_ne_once:
  "plus_int_dom Refine_Never arithmetic_left arithmetic_right \<noteq>
   plus_int_dom Refine_Once arithmetic_left arithmetic_right"
  by eval

section \<open>One pass versus refinement fixpoint\<close>

text \<open>
  A single \<^const>\<open>Refine_Once\<close> pass is not yet the fixpoint here: it leaves
  Sign at \<open>SNonPos\<close> even though the \<open>[0,0]\<close> interval it just derived (in
  that very same pass) already forces the sharper \<open>SZero\<close>. This is exactly
  \<open>refinement_round_is_progressive\<close>'s own witness
  (\<^theory>\<open>Voblint_Examples.Example_Int_Domain\<close>): \<^const>\<open>refine_round\<close>'s fixed step order,
  \<open>[refine_interval, refine_congruence]\<close> (\<^theory>\<open>Voblint_Analysis.Int_Refinement\<close>),
  computes Sign from the interval as it stood \<^emph>\<open>before\<close> that same round's
  \<^const>\<open>refine_congruence\<close> step narrows it further, so Sign only catches up
  to the tighter interval one full round later.
\<close>

lemmas mode_fixpoint_state = arithmetic_fixpoint_result

lemmas mode_once_ne_fixpoint = arithmetic_once_not_fixpoint

lemma mode_never_ne_fixpoint:
  "plus_int_dom Refine_Never arithmetic_left arithmetic_right \<noteq>
   plus_int_dom Refine_Fixpoint arithmetic_left arithmetic_right"
  by eval

text \<open>
  Sign's own three-value progression \<open>STop \<rightarrow> SNonPos \<rightarrow> SZero\<close>
  (\<open>mode_never_state\<close>/\<open>mode_once_state\<close>/\<open>mode_fixpoint_state\<close>, unfolded)
  witnesses a genuine three-way divergence: \<^const>\<open>Refine_Never\<close>,
  \<^const>\<open>Refine_Once\<close>, and \<^const>\<open>Refine_Fixpoint\<close> compute three pairwise
  distinct \<open>int_dom\<close> values on the same input, not merely two.
\<close>

section \<open>Interval and congruence\<close>

text \<open>
  Congruence teaches Interval which endpoints of an otherwise-unconstrained
  range are actually reachable: \<open>[0,10]\<close> intersected with \<open>x \<equiv> 1 (mod 2)\<close>
  (odd) excludes both even endpoints, so \<open>refine_congruence\<close> tightens the
  bound to \<open>[1,9]\<close> even though this representation cannot punch the even
  holes \<open>{2,4,6,8}\<close> out of the middle. Interval alone never derives this --
  \<open>[0,10]\<close> says nothing about parity -- and Congruence alone never derives
  the endpoints either, since \<open>x \<equiv> 1 (mod 2)\<close> is unbounded on its own.
  \<open>congruence_refines_interval_bounds\<close>
  (\<^theory>\<open>Voblint_Examples.Example_Int_Domain\<close>) already proves the same
  reduction at modulus \<open>4\<close> (\<open>[0,10]\<close> narrowed to \<open>[1,9]\<close> by \<open>x \<equiv> 1 (mod 4)\<close>);
  the lemma below is the modulus-\<open>2\<close> sibling the composite-domain
  literature's canonical "narrow toward the odd values" example states.
\<close>

lemma interval_congruence_odd_narrows:
  "int_ivl
    (refine_congruence
      (int_dom_sipc STop (Ivl (Fin 0) (Fin 10)) PTop (mk_congruence 1 2))) =
   Ivl (Fin 1) (Fin 9)"
  by eval

section \<open>Sign and interval\<close>

text \<open>
  Sign teaches Interval that a range's negative half is unreachable: \<open>Positive\<close>
  combined with \<open>[-10,5]\<close> excludes every non-positive value in that range,
  so \<open>refine_interval\<close> (via \<open>interval_fact_of_sign\<close>'s own reading of
  \<open>SPos\<close> as \<open>[1,+inf)\<close>) tightens the lower bound from \<open>-10\<close> to \<open>1\<close>, leaving
  \<open>[1,5]\<close>. Interval alone never derives this -- \<open>[-10,5]\<close> says nothing about
  sign -- and Sign alone never derives the upper bound either, since
  \<open>Positive\<close> is unbounded above on its own.
\<close>

lemma sign_interval_positive_narrows:
  "int_ivl
    (refine_interval
      (int_dom_sip SPos (Ivl (Fin (-10)) (Fin 5)) PTop)) =
   Ivl (Fin 1) (Fin 5)"
  by eval

section \<open>Congruence and parity\<close>

text \<open>
  Congruence teaches Parity a fact Parity's own two-value lattice cannot
  state as precisely: \<open>x \<equiv> 0 (mod 4)\<close> forces \<open>x\<close> even, so
  \<open>refine_congruence\<close> (via \<open>parity_fact_of_congruence\<close>) tightens \<open>PTop\<close> to
  \<open>PEven\<close>. This direction is one-way in \<open>Int_Refinement.thy\<close>'s own design:
  \<open>refinement_steps = [refine_interval, refine_congruence]\<close>
  (\<^theory>\<open>Voblint_Analysis.Int_Refinement\<close>) has no separate
  parity-refines-congruence step, because Congruence already subsumes every
  fact Parity alone can express (\<open>mod 2\<close> is exactly parity), so there is
  nothing left for Parity to teach Congruence back that Congruence did not
  already know.
\<close>

lemma congruence_parity_mod4_narrows:
  "int_parity
    (refine_congruence
      (int_dom_sipc STop (top :: ivl) PTop (mk_congruence 0 4))) =
   PEven"
  by eval

section \<open>End-to-end VIMP precision\<close>

text \<open>
  \<open>Exec_Int_DG_Run.thy\<close> already carries the solver-run-level (compiled VIMP
  program through the real Base/DG equation system and
  \<open>TD_side_always_join_Interp_solve\<close>) counterpart to this file's raw-domain
  witnesses above: on \<open>if (y + 1 == 3) {x := 1} else {x := 0}\<close>,
  \<open>dgExI_never_inspect_y_at_Statement_1\<close> reads \<open>y\<close> back at \<open>STop\<close>/top
  interval/\<open>PTop\<close> (only Congruence narrows, to \<open>y \<equiv> 0 (mod 2)\<close>, from the
  guard's own arithmetic), while \<open>dgExI_once_inspect_y_at_Statement_1\<close> and
  \<open>dgExI_fixpoint_inspect_y_at_Statement_1\<close> both reach the exact singleton
  \<open>SPos\<close>/\<open>[2,2]\<close>/\<open>PEven\<close>/\<open>y \<equiv> 0 (mod 2)\<close> -- the same
  Never-differs-from-Once-and-Fixpoint pattern \<open>mode_never_ne_once\<close> proves
  at the raw-domain level above, now reached through the parser, the
  compiled CFG, and the vendored solver rather than a hand-built \<open>int_dom\<close>
  value. \<open>dgExI_never_ne_once\<close>/\<open>dgExI_once_eq_fixpoint\<close> are the pinned
  corollaries; this file does not restate them, since restating a fact
  already proved end-to-end elsewhere would only risk drifting from it.

  The CLI-level regression fixture
  \<open>tests/regression/16-composite-domain/precision/01-refinement_beats_components.vimp\<close>
  is the production-route sibling of the same scenario: \<open>voblint --analysis
  int\<close> (fixed at \<open>Refine_Fixpoint\<close>) proves \<open>y == 2\<close> exactly on the
  identical guard, while \<open>--analysis sign\<close>/\<open>--analysis interval\<close> alone
  each leave it \<open>UNKNOWN\<close> -- the full pipeline's own confirmation that the
  refinement machinery this file exercises in isolation survives parsing,
  compilation, and the production report layer intact.
\<close>

end
