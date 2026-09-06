theory Interval_Special
  imports Interval_Backward "Voblint_Analysis_Base.Special_Ops"
begin

section \<open>Interval: special-call semantics\<close>

text \<open>
  \<open>ivl_min\<close>/\<open>ivl_max\<close> (in \<open>Interval_Arithmetic\<close>) exist solely as the abstract
  implementation of the \<open>Min\<close>/\<open>Max\<close> special calls, mirroring how Sign's
  \<open>sign_min\<close>/\<open>sign_max\<close> exist solely for the same reason.
\<close>

subsection \<open>Special-call dispatch\<close>

fun special_ivl ::
    "special_call => vname => (vname => ivl) => (vname => ivl)"
where
  "special_ivl Nondet_Int x \<sigma> = \<sigma>(x := ivl_top)"
| "special_ivl (Min a b) x \<sigma> = \<sigma>(x := ivl_min (aval_ivl a \<sigma>) (aval_ivl b \<sigma>))"
| "special_ivl (Max a b) x \<sigma> = \<sigma>(x := ivl_max (aval_ivl a \<sigma>) (aval_ivl b \<sigma>))"

definition ivl_special_ops :: "ivl special_ops" where
  "ivl_special_ops = (| special_min = ivl_min, special_max = ivl_max |)"

interpretation ivl_special: sound_special_ops ivl_special_ops aval_ivl
  by unfold_locales
     (auto simp: ivl_special_ops_def top_ivl_def gamma_ivl_top
           intro: ivl_min_sound ivl_max_sound ivl_min_combine_mono ivl_max_combine_mono
                  aval_ivl_sound aval_ivl_mono)

lemma ivl_special_ops_min [simp]: "special_min ivl_special_ops = ivl_min"
  by (simp add: ivl_special_ops_def)

lemma ivl_special_ops_max [simp]: "special_max ivl_special_ops = ivl_max"
  by (simp add: ivl_special_ops_def)

lemma special_ivl_eq_transfer: "special_ivl sc x \<sigma> = ivl_special.special_transfer sc x \<sigma>"
  by (cases sc) (simp_all add: top_ivl_def)

lemmas special_ivl_sound = ivl_special.special_transfer_sound[folded special_ivl_eq_transfer]
lemmas special_ivl_mono  = ivl_special.special_transfer_mono[folded special_ivl_eq_transfer]

end
