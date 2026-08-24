theory Interval_Special
  imports Interval_Backward Voblint_Core.Special_Ops
begin

section \<open>Interval: special-call semantics\<close>

text \<open>
  \<open>ivl_min\<close>/\<open>ivl_max\<close> (in \<open>Interval_Arithmetic\<close>) exist solely as the abstract
  implementation of the \<open>Min\<close>/\<open>Max\<close> special calls, mirroring how Sign's
  \<open>sign_min\<close>/\<open>sign_max\<close> exist solely for the same reason.
\<close>

subsection \<open>Special-call dispatch\<close>

definition ivl_special_ops :: "ivl special_ops" where
  "ivl_special_ops = (| special_min = ivl_min, special_max = ivl_max |)"

interpretation ivl_special: sound_special_ops ivl_special_ops aval_ivl ivl_cast
  by unfold_locales
     (auto simp: ivl_special_ops_def top_ivl_def gamma_ivl_top
           intro: ivl_min_sound ivl_max_sound ivl_min_combine_mono ivl_max_combine_mono
                  aval_ivl_sound aval_ivl_mono ivl_cast_sound ivl_cast_mono)

lemma ivl_special_ops_min [simp]: "special_min ivl_special_ops = ivl_min"
  by (simp add: ivl_special_ops_def)

lemma ivl_special_ops_max [simp]: "special_max ivl_special_ops = ivl_max"
  by (simp add: ivl_special_ops_def)

text \<open>
  \<open>special_ivl\<close> is a thin alias for \<^const>\<open>sound_special_ops.special_transfer\<close>
  at its own \<open>ivl_special_ops\<close>/\<open>aval_ivl\<close> instance -- \<open>special_transfer\<close>
  already correctly threads \<open>\<Gamma>\<close>/synthesized-kind evaluation into \<open>Min\<close>/
  \<open>Max\<close>'s two operands, so there is nothing for a per-domain reimplementation
  to add.
\<close>

definition special_ivl ::
    "tyenv => special_call => vname => (vname => ivl) => (vname => ivl)"
where
  "special_ivl = ivl_special.special_transfer"

lemmas special_ivl_sound = ivl_special.special_transfer_sound[folded special_ivl_def]
lemmas special_ivl_mono  = ivl_special.special_transfer_mono[folded special_ivl_def]

end
