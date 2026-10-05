theory Interval_Special
  imports Interval_Backward "Voblint_Nonrelational.Special_Ops"
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
  "special_ivl Nondet_Int x d = d(x := ivl_top)"
| "special_ivl (Min a b) x d = d(x := ivl_min (aval_ivl a d) (aval_ivl b d))"
| "special_ivl (Max a b) x d = d(x := ivl_max (aval_ivl a d) (aval_ivl b d))"

definition ivl_special_ops :: "ivl special_ops" where
  "ivl_special_ops = (| special_min = ivl_min, special_max = ivl_max |)"

interpretation ivl_special: mono_minmax_ops ivl_special_ops aval_ivl
  by unfold_locales
     (auto simp: ivl_special_ops_def top_ivl_def gamma_ivl_top
           intro: ivl_min_sound ivl_max_sound ivl_min_combine_mono ivl_max_combine_mono)

lemma ivl_special_ops_min [simp]: "special_min ivl_special_ops = ivl_min"
  by (simp add: ivl_special_ops_def)

lemma ivl_special_ops_max [simp]: "special_max ivl_special_ops = ivl_max"
  by (simp add: ivl_special_ops_def)

lemma special_ivl_eq_transfer: "special_ivl sc x d = ivl_special.special_transfer sc x d"
  by (cases sc) (simp_all add: top_ivl_def)

end
