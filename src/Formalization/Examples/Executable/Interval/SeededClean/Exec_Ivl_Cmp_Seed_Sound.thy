theory Exec_Ivl_Cmp_Seed_Sound
  imports Voblint_Analysis.Clean_RRead_Sound Voblint_Analysis.Interval_Domain
begin

section \<open>Interval instantiates the generic seeded-clean R_read spine\<close>

text \<open>
  Interval is a thin instantiation of the domain-generic seeded-clean spine
  \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>, exactly as Sign is.  The clean transfer
  \<open>ivl_etf_clean\<close> is \<^term>\<open>clean_etf_of_transfer ivl_tf\<close>, and the whole D/G/C
  soundness spine --- the five R_read obligations, the flat theorem, the trace kernel,
  and the two context-sliced theorems --- follows from @{thm ivl_is_sound_transfer}
  with no interval-specific proof.  The only domain-specific ingredient is that
  \<^const>\<open>ivl_tf\<close> is a @{locale sound_transfer}, established in
  \<^theory>\<open>Voblint_Analysis.Interval_Domain\<close>.
\<close>

definition ivl_etf_clean :: "(unit, ivl) effectful_domain_transfer" where
  "ivl_etf_clean = clean_etf_of_transfer ivl_tf"

lemma apply_etf_ivl_etf_clean:
  "apply_etf ivl_etf_clean a u = clean_edge_tree (apply_tf ivl_tf a) u"
  unfolding ivl_etf_clean_def clean_etf_of_transfer_def by (cases a) simp_all

subsection \<open>The D/G/C soundness spine, for Interval\<close>

text \<open>
  The five R_read transfer obligations: the clean interval transfer reading only the
  local slot soundly steps the concretisation of that slot.  Each is the generic
  obligation at the concrete base transfer.
\<close>

lemmas ivl_clean_rread_nop = sound_transfer.clean_rread_nop[OF ivl_is_sound_transfer]
lemmas ivl_clean_rread_assign = sound_transfer.clean_rread_assign[OF ivl_is_sound_transfer]
lemmas ivl_clean_rread_assume = sound_transfer.clean_rread_assume[OF ivl_is_sound_transfer]
lemmas ivl_clean_rread_assume_not = sound_transfer.clean_rread_assume_not[OF ivl_is_sound_transfer]
lemmas ivl_clean_rread_enter = sound_transfer.clean_rread_enter[OF ivl_is_sound_transfer]

text \<open>Flat collecting soundness over the local read: the clean spine over-approximates
  \<^const>\<open>cfg_collect\<close> at the local slot.\<close>

lemmas ivl_clean_cfg_collect_rread = sound_transfer.clean_cfg_collect_rread[OF ivl_is_sound_transfer]

text \<open>Context-sliced collecting soundness against \<^const>\<open>cfg_collect_ctx\<close>: the conclusion
  is the per-context local slot \<open>sg (Inl (v, ctx))\<close> (R_read).  The seed obligations
  \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> correspond to Goblint \<open>Spec.enter\<close>, \<open>ENTER_MONO\<close> to
  \<open>Spec.context\<close>, and \<open>COMB\<close> to \<open>Spec.combine\<close> --- identical to Sign, since the D/G/C
  framework is domain-agnostic.\<close>

lemmas ivl_clean_ctx_collect_rread = sound_transfer.clean_ctx_collect_rread[OF ivl_is_sound_transfer]

text \<open>Its executable head-digest reduction (digest-propagation obligations discharged
  generically).\<close>

lemmas ivl_clean_ctx_collect_rread_head = sound_transfer.clean_ctx_collect_rread_head[OF ivl_is_sound_transfer]

section \<open>Scope: D/G/C soundness versus interval widening precision\<close>

text \<open>
  What is certified here is the \<^emph>\<open>D/G/C correctness\<close> of the seeded-clean spine for
  Interval: the R_read local-slot conclusion soundly over-approximates the
  context-sliced collecting semantics for \<^emph>\<open>any\<close> post-solution satisfying the
  enter / context / combine obligations.  This is orthogonal to interval
  \<^emph>\<open>precision\<close>: on programs with loops the analyzer's fixpoint is governed by the
  widening / narrowing operators of \<^class>\<open>abstract_domain\<close> (\<^const>\<open>widen_state\<close>), not
  by the R_read split.  Any imprecision an interval run exhibits on a loop is
  therefore a widening/narrowing matter, not a D/G/C matter --- the D/G/C spine is
  sound at every program point regardless of how coarse the widened invariant is.

  No executable seeded-clean interval run is provided: unlike Sign, the interval
  \<^emph>\<open>st\<close>-level seeded generator and R_read combine are not wired, so an \<open>eval\<close> witness
  would not be stable.  The soundness spine above is domain-complete on its own.
\<close>

end
