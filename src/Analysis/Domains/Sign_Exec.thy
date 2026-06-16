theory Sign_Exec
  imports Exec_Bridge Sign_Domain
begin

section \<open>Sign per-domain seam: executable transfer mirror and commutation\<close>

text \<open>
  The generic S4 transport (\<open>Exec_Bridge.part_post_solution_st_to_abs\<close>) is
  parameterised over an executable transfer mirror \<open>tf_st\<close> with the commutation
  hypothesis \<open>fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)\<close>.  This theory
  discharges that obligation for the sign domain: \<open>sign_tf_st\<close> mirrors
  \<open>apply_tf sign_tf\<close> at \<open>sign st\<close>, action by action, and \<open>sign_tf_st_commute\<close>
  proves the commutation.  This is the single domain-specific piece of S4; every
  other ingredient is generic in the value domain.
\<close>

lemma fun_of_st_update:
  "fun_of_st (update_st s x v) = (fun_of_st s)(x := v)"
  by (rule ext) (metis fun_upd_apply lookup_update_diff lookup_update_same)

subsection \<open>Assume mirror\<close>

fun assume_sign_st :: "bexp \<Rightarrow> sign st \<Rightarrow> sign st" where
    "assume_sign_st (Less (BaseN (AExp.V x)) (BaseN (AExp.N n))) s =
       (if n = 0 then update_st s x SNeg else s)"
  | "assume_sign_st _ s = s"

lemma assume_sign_st_commute:
  "fun_of_st (assume_sign_st b s) = assume_sign b (fun_of_st s)"
  by (induction b s rule: assume_sign_st.induct)
     (auto simp: fun_of_st_update)

subsection \<open>Enter mirror (reset locals to top, keep globals)\<close>

lemma fun_rep_enter_sign_rep:
  "fun_rep_st ((\<lambda>(dl, dg, ps). (STop, dg, filter (\<lambda>(x, _). is_global x) ps)) r)
   = (\<lambda>x. if is_global x then fun_rep_st r x else STop)"
proof -
  obtain dl dg ps where r: "r = (dl, dg, ps)" using prod_cases3 by blast
  show ?thesis unfolding r
    by (rule ext) (auto simp: map_of_filter_key split: option.split)
qed

lift_definition enter_sign_st :: "sign st \<Rightarrow> sign st"
  is "\<lambda>(dl, dg, ps). (STop, dg, filter (\<lambda>(x, _). is_global x) ps)"
  by (auto simp: eq_st_def fun_rep_enter_sign_rep fun_eq_iff)

lemma enter_sign_st_commute:
  "fun_of_st (enter_sign_st s) = enter_sign (fun_of_st s)"
  unfolding enter_sign_def
  by transfer (simp add: fun_rep_enter_sign_rep)

subsection \<open>The executable sign transfer function\<close>

fun sign_tf_st :: "edge_action \<Rightarrow> sign st \<Rightarrow> sign st" where
    "sign_tf_st EA_Nop s = s"
  | "sign_tf_st (EA_Assign x a) s = update_st s x (aval_sign a (lookup_st s))"
  | "sign_tf_st (EA_Assume b) s = assume_sign_st b s"
  | "sign_tf_st (EA_AssumeNot b) s = s"
  | "sign_tf_st EA_Enter s = enter_sign_st s"

subsection \<open>Sound input seed: top everywhere\<close>

text \<open>
  \<open>top_sign_st\<close> represents \<open>\<lambda>_. STop\<close> (every variable unknown).  Its
  concretisation is the whole store space (\<open>gamma_state (\<lambda>_. STop) = UNIV\<close>), so
  seeding the analysis with it makes the certified result non-vacuous -- the
  whole point of the two-region rep (a bot-default seed would force an empty
  concretisation).
\<close>

lift_definition top_sign_st :: "sign st" is "(STop, STop, [])" .

lemma lookup_top_sign_st [simp]: "lookup_st top_sign_st x = STop"
  by transfer simp

lemma fun_of_st_top_sign_st: "fun_of_st top_sign_st = (\<lambda>_. STop)"
  by (rule ext) simp

subsection \<open>The executable sign transfer function\<close>

theorem sign_tf_st_commute:
  "fun_of_st (sign_tf_st a s) = apply_tf sign_tf a (fun_of_st s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by (simp add: sign_tf_def)
next
  case (EA_Assign x e)
  then show ?thesis
    by (simp add: sign_tf_def assign_sign_def fun_of_st_update)
next
  case (EA_Assume b)
  then show ?thesis
    by (simp add: sign_tf_def assume_sign_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis by (simp add: sign_tf_def)
next
  case EA_Enter
  then show ?thesis by (simp add: sign_tf_def enter_sign_st_commute)
qed

end
