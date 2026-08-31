theory Exec_Refinement
  imports Exec_St "Voblint_Core.State_Restriction"
begin

section \<open>Refinement between executable and abstract split states\<close>

text \<open>
  \<^const>\<open>fun_of_resolved_st_q_for\<close> reads an executable \<^typ>\<open>'a resolved_st_q\<close>
  back as an abstract \<^typ>\<open>'a abs_state\<close>. It is a homomorphism for the
  local/global projections and for the routed combine, so an executable step
  and its abstract counterpart agree after readback.
\<close>

lemma fun_of_resolved_st_q_for_restrict_local_abs [simp]:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) = restrict_local_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_local_for_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_restrict_global_abs [simp]:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) = restrict_global_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_global_for_def
  by (rule ext) simp

text \<open>The converse recombination: a local projection joined with a disjoint global
  projection is exactly the routed combine. Left bare (not \<open>[simp]\<close>) since it would
  compete with \<open>restrict_local_resolved_q_split\<close>/\<open>restrict_global_resolved_q_split\<close>
  on the same \<open>restrict_local _ \<squnion> restrict_global _\<close> redex.\<close>
lemma combine_resolved_st_q_eq_restrict_sup:
  "combine_resolved_st_q A B = restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (combine_resolved_st_q A B) =
      lookup_resolved_st_q (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (combine_resolved_st_q A B) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed

subsection \<open>Executable projection identities\<close>

lemma restrict_local_resolved_q_combine_resolved_st_q [simp]:
  "restrict_local_resolved_q (combine_resolved_st_q A B) =
     restrict_local_resolved_q A"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_local_resolved_q (combine_resolved_st_q A B)) =
      lookup_resolved_st_q (restrict_local_resolved_q A)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_local_resolved_q (combine_resolved_st_q A B)) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A) loc"
      by (cases loc; simp)
  qed
qed

lemma restrict_global_resolved_q_combine_resolved_st_q [simp]:
  "restrict_global_resolved_q (combine_resolved_st_q A B) =
     restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q (combine_resolved_st_q A B)) =
      lookup_resolved_st_q (restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q (combine_resolved_st_q A B)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed

text \<open>Executable trees use these projection identities to split combined states.\<close>
lemma restrict_local_resolved_q_split [simp]:
  "restrict_local_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_local_resolved_q A"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_local_resolved_q
      (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) =
      lookup_resolved_st_q (restrict_local_resolved_q A)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_local_resolved_q
        (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A) loc"
      by (cases loc; simp)
  qed
qed

lemma restrict_global_resolved_q_split [simp]:
  "restrict_global_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q
      (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) =
      lookup_resolved_st_q (restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q
        (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed


subsection \<open>Readback of joins\<close>

lemma map_lift_fun_of_resolved_st_q_for_sup [simp]:
  "map_lift (fun_of_resolved_st_q_for gs) (a \<squnion> b) =
   map_lift (fun_of_resolved_st_q_for gs) a \<squnion> map_lift (fun_of_resolved_st_q_for gs) b"
  by (cases a; cases b; simp)

lemma map_lift_fun_of_resolved_st_q_for_mono:
  assumes "x \<le> y"
  shows "map_lift (fun_of_resolved_st_q_for gs) x \<le> map_lift (fun_of_resolved_st_q_for gs) y"
  using assms by (cases x; cases y; simp add: fun_of_resolved_st_q_for_mono)

end
