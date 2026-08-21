theory Example_Int_Warrowing
  imports Voblint_Analysis.Int_Warrowing Voblint_Analysis.Int_Refinement
begin

section \<open>Composite widening and narrowing: examples\<close>

subsection \<open>Widening is exactly componentwise\<close>

text \<open>
  Each component's own accelerating \<open>widen\<close> surfaces through unchanged:
  Interval jumps a growing upper bound straight to \<open>PlusInf\<close>
  (\<open>widen_ivl_core\<close>, \<open>Interval_Warrowing.thy\<close>) rather than merely joining
  to \<open>[1,3]\<close>, while Sign, Parity, and Congruence -- whose own widening is
  plain join -- stay at their shared value. No cross-component step runs
  afterward.
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
  (\<open>Sign_Lattice.thy\<close>, \<open>Parity_Domain.thy\<close>, \<open>Congruence_Warrowing.thy\<close>):
  once widened, they never narrow back, which trivially satisfies
  \<open>narrow_ge\<close>/\<open>narrow_le\<close> without needing anything about their own
  structure. Interval's \<open>narrow_ivl_td\<close> does real work, recovering a
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

subsection \<open>The composite \<open>bounded_warrowing\<close> laws hold generically\<close>

text \<open>
  Not just spot-checked by \<open>eval\<close> at one instance: these cite the
  \<open>warrowing\<close> class facts directly at \<open>int_dom\<close>, witnessing that the
  \<open>instantiation int_dom_ext :: (int_dom_record_warrowing) warrowing\<close>
  block in \<open>Int_Warrowing.thy\<close> actually resolves and discharges its
  obligations for every \<open>a\<close>, \<open>b\<close>, not only the examples above.
\<close>

lemma int_dom_widen_ge1: "(a :: int_dom) \<le> widen a b"
  by (rule widen_ge1)

lemma int_dom_widen_ge2: "(b :: int_dom) \<le> widen a b"
  by (rule widen_ge2)

lemma int_dom_narrow_ge: "(b :: int_dom) \<le> a \<Longrightarrow> b \<le> narrow a b"
  by (rule narrow_ge)

lemma int_dom_narrow_le: "(b :: int_dom) \<le> a \<Longrightarrow> narrow a b \<le> a"
  by (rule narrow_le)

subsection \<open>Why post-narrow refinement would break \<open>narrow_ge\<close>\<close>

text \<open>
  The concrete counterexample behind \<open>Int_Warrowing.thy\<close>'s design comment.
  \<open>a\<close> is a widened solver state (top); \<open>b\<close> is a newer, more precise result
  that is not refinement-stable -- \<open>STop \<times> [-1,0] \<times> PEven \<times> top\<close> already
  denotes only concrete values with even parity in \<open>[-1,0]\<close>, i.e. \<open>{0}\<close>,
  but Sign has not caught up. Componentwise narrowing recovers Interval's
  bound and leaves everything else at \<open>a\<close>'s value, satisfying \<open>b \<le> narrow
  a b \<le> a\<close> exactly as required. Running \<open>Refine_Once\<close> on top of that
  narrowing result -- the Goblint-style move this theory deliberately does
  not make -- lets Sign's own cross-component derivation from the now-exact
  Interval bound produce \<open>SNonPos\<close>, which sits strictly below \<open>b\<close>'s own
  \<open>STop\<close>: exactly the \<open>narrow_ge\<close> violation
  \<open>Int_Warrowing.thy\<close>'s header comment describes in the abstract.
\<close>

lemma post_narrow_refinement_would_violate_narrow_ge:
  "let a = (top :: int_dom);
       b = int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PEven (top :: congruence)
   in b \<le> a \<and> \<not> (b \<le> refine Refine_Once (narrow a b))"
  by eval

end

