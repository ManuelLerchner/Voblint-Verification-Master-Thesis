theory Example_Int_Warrowing
  imports
    Voblint_Analysis_Int.Int_Refinement_Control
begin

section \<open>Where the composite widens and narrows, and where it must not refine\<close>

text \<open>
  Widening and narrowing on the product are the four components' own operators
  applied side by side, with nothing run afterward to reconcile them. This
  theory pins that by \<open>eval\<close> in both directions and then exhibits the
  concrete state that makes the omission necessary: refining after a narrow
  would break the solver's \<open>narrow_ge\<close> bracket. Vocabulary:
  \<open>int_dom_sipc s i p c\<close> overwrites \<open>top\<close> in the order sign, interval, parity,
  congruence, and \<open>mk_congruence c m\<close> is the residue class of \<open>c\<close> modulo \<open>m\<close>.
\<close>

subsection \<open>Widening is exactly componentwise\<close>

text \<open>
  Each component's own accelerating \<open>widen\<close> surfaces through unchanged:
  Interval jumps a growing upper bound straight to \<open>PlusInf\<close>
  (\<^const>\<open>widen_ivl_core\<close>, \<^theory>\<open>Voblint_Analysis_Interval.Interval_Warrowing\<close>)
  rather than merely joining to \<open>[1,3]\<close>, while Sign, Parity, and Congruence --
  whose own widening is plain join -- stay at their shared value. No
  cross-component step runs afterward.
\<close>

lemma widen_int_dom_componentwise_regression:
  "widen
     (int_dom_sipc SPos (Ivl (Fin 1) (Fin 1)) POdd (mk_congruence 1 2))
     (int_dom_sipc SPos (Ivl (Fin 3) (Fin 3)) POdd (mk_congruence 1 2)) =
   int_dom_sipc SPos (Ivl (Fin 1) PlusInf) POdd (mk_congruence 1 2)"
  by eval

subsection \<open>Narrowing is exactly componentwise\<close>

text \<open>
  Sign, Parity, and Congruence all choose the conservative \<open>narrow a b = a\<close>
  (\<^theory>\<open>Voblint_Analysis_Sign.Sign_Warrowing\<close>,
  \<^theory>\<open>Voblint_Analysis_Parity.Parity_Warrowing\<close>,
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Warrowing\<close>):
  once widened, they never narrow back, which trivially satisfies
  \<open>narrow_ge\<close>/\<open>narrow_le\<close> without needing anything about their own
  structure. Interval's \<^const>\<open>narrow_ivl_td\<close> does real work, recovering a
  finite bound from an infinite one. The composite record update runs no
  refinement afterward, so Sign and Parity stay exactly where widening
  left them even though Interval and the guard both already point at a
  narrower concrete set.
\<close>

lemma narrow_int_dom_componentwise_regression:
  "narrow
     (top :: int_dom)
     (int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PEven (top :: congruence)) =
   int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PTop (top :: congruence)"
  by eval

subsection \<open>Why post-narrow refinement would break \<open>narrow_ge\<close>\<close>

text \<open>
  The concrete counterexample behind the design comment in
  \<^theory>\<open>Voblint_Analysis_Int.Int_Warrowing\<close>. \<open>a\<close> is a widened solver state
  (top); \<open>b\<close> is a newer, more precise result that is not refinement-stable --
  \<open>STop\<close>, \<open>[-1,0]\<close>, \<open>PEven\<close>, \<open>top\<close> together already denote only the concrete
  values with even parity in \<open>[-1,0]\<close>, i.e. \<open>{0}\<close>, but Sign has not caught up.
  Componentwise narrowing recovers Interval's bound and leaves everything else
  at \<open>a\<close>'s value, satisfying \<open>b \<le> narrow a b \<le> a\<close> exactly as required.
  Running \<open>Refine_Once\<close> on top of that narrowing result -- the Goblint-style
  move this theory deliberately does not make -- lets Sign's own
  cross-component derivation from the now-exact Interval bound produce
  \<open>SNonPos\<close>, which sits strictly below \<open>b\<close>'s own \<open>STop\<close>: exactly the
  \<open>narrow_ge\<close> violation that header comment describes in the abstract.
\<close>

lemma post_narrow_refinement_would_violate_narrow_ge:
  "let a = (top :: int_dom);
       b = int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PEven (top :: congruence)
   in b \<le> a \<and> \<not> (b \<le> refine Refine_Once (narrow a b))"
  by eval

end
