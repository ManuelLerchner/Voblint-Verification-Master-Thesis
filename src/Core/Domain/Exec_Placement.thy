theory Exec_Placement
  imports Exec_St "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Finite executable placement scopes\<close>

type_synonym scoped_location = "pname * location"

definition scoped_location_of :: "pname => location => scoped_location" where
  "scoped_location_of owner loc = (owner, loc)"

definition placement_global_invariant ::
  "(scoped_location => bool) => bool" where
  "placement_global_invariant placed \<longleftrightarrow>
    (\<forall>p q x. placed (p, Global_Location x) = placed (q, Global_Location x))"

definition classic_keep_local :: "scoped_location => bool" where
  "classic_keep_local scoped =
    (case snd scoped of Local_Location _ => True | Global_Location _ => False)"

definition classic_publish_side :: "scoped_location => bool" where
  "classic_publish_side scoped =
    (case snd scoped of Local_Location _ => False | Global_Location _ => True)"

lemma classic_keep_local_global_invariant:
  "placement_global_invariant classic_keep_local"
  unfolding placement_global_invariant_def classic_keep_local_def by simp

lemma classic_publish_side_global_invariant:
  "placement_global_invariant classic_publish_side"
  unfolding placement_global_invariant_def classic_publish_side_def by simp

definition scope_locations :: "imp_prog => pname => location list" where
  "scope_locations p owner =
    remdups (map (location_of (storage_global p owner))
      (scope_vnames_list p owner))"

lemma set_scope_locations [simp]:
  "set (scope_locations p owner) =
    image (location_of (storage_global p owner)) (scope_vnames p owner)"
  unfolding scope_locations_def
  by simp

lemma declared_global_in_scope_locations:
  assumes "declared_global p x"
  shows "Global_Location x \<in> set (scope_locations p owner)"
proof -
  have x_scope: "x \<in> scope_vnames p owner"
    using assms unfolding scope_vnames_def by simp
  have location:
    "location_of (storage_global p owner) x = Global_Location x"
    using assms by (simp add: location_of_def)
  have member:
    "location_of (storage_global p owner) x \<in>
      image (location_of (storage_global p owner)) (scope_vnames p owner)"
    by (rule imageI[OF x_scope])
  show ?thesis
    using member location by simp
qed

lemma implicit_local_in_scope_locations:
  assumes "x \<in> scope_vnames p owner" and "\<not> declared_global p x"
  shows "Local_Location x \<in> set (scope_locations p owner)"
proof -
  have location:
    "location_of (storage_global p owner) x = Local_Location x"
    using assms by (simp add: location_of_def)
  have member:
    "location_of (storage_global p owner) x \<in>
      image (location_of (storage_global p owner)) (scope_vnames p owner)"
    by (rule imageI[OF assms(1)])
  show ?thesis
    using member location by simp
qed

subsection \<open>Materialized placement projection\<close>

fun resolved_default :: "('a::bot) resolved_st => location => 'a" where
  "resolved_default (dl, dg, entries) (Local_Location x) = dl"
| "resolved_default (dl, dg, entries) (Global_Location x) = dg"

fun raw_support :: "('a::bot) resolved_st => location list" where
  "raw_support (dl, dg, entries) = map fst entries"

definition effective_support ::
  "('a::bot) resolved_st => location list" where
  "effective_support s =
    filter (\<lambda>loc. lookup_resolved_st s loc \<noteq> resolved_default s loc)
      (remdups (raw_support s))"

definition relevant_locations ::
  "imp_prog => pname => ('a::bot) resolved_st => location list" where
  "relevant_locations p owner s =
    remdups (scope_locations p owner @ effective_support s)"

lemma set_relevant_locations [simp]:
  "set (relevant_locations p owner s) =
    set (scope_locations p owner) \<union> set (effective_support s)"
  unfolding relevant_locations_def by simp

lemma set_effective_support:
  "set (effective_support s) =
    {loc \<in> set (raw_support s).
      lookup_resolved_st s loc \<noteq> resolved_default s loc}"
  unfolding effective_support_def
  by auto

lemma eq_resolved_st_defaults:
  assumes "eq_resolved_st (dl, dg, ps) (el, eg, qs)"
  shows "dl = el \<and> dg = eg"
proof -
  obtain x where fresh:
    "x \<notin> image location_vname (set (map fst ps @ map fst qs))"
    using fresh_vname_notin[of ps qs] by auto
  have local_support:
    "Local_Location x \<notin> set (map fst ps @ map fst qs)"
  proof
    assume "Local_Location x \<in> set (map fst ps @ map fst qs)"
    then have "location_vname (Local_Location x) \<in>
        image location_vname (set (map fst ps @ map fst qs))"
      by (rule imageI)
    with fresh show False by simp
  qed
  have global_support:
    "Global_Location x \<notin> set (map fst ps @ map fst qs)"
  proof
    assume "Global_Location x \<in> set (map fst ps @ map fst qs)"
    then have "location_vname (Global_Location x) \<in>
        image location_vname (set (map fst ps @ map fst qs))"
      by (rule imageI)
    with fresh show False by simp
  qed
  have local_ps: "map_of ps (Local_Location x) = None"
    using local_support by (simp add: map_of_resolved_none_iff)
  have local_qs: "map_of qs (Local_Location x) = None"
    using local_support by (simp add: map_of_resolved_none_iff)
  have global_ps: "map_of ps (Global_Location x) = None"
    using global_support by (simp add: map_of_resolved_none_iff)
  have global_qs: "map_of qs (Global_Location x) = None"
    using global_support by (simp add: map_of_resolved_none_iff)
  have lookup:
    "lookup_resolved_st (dl, dg, ps) =
      lookup_resolved_st (el, eg, qs)"
    using assms unfolding eq_resolved_st_def by simp
  have local_lookup:
    "lookup_resolved_st (dl, dg, ps) (Local_Location x) =
      lookup_resolved_st (el, eg, qs) (Local_Location x)"
    using lookup by (rule fun_cong)
  have local_eq: "dl = el"
    using local_ps local_qs local_lookup by simp
  have global_lookup:
    "lookup_resolved_st (dl, dg, ps) (Global_Location x) =
      lookup_resolved_st (el, eg, qs) (Global_Location x)"
    using lookup by (rule fun_cong)
  have global_eq: "dg = eg"
    using global_ps global_qs global_lookup by simp
  show ?thesis using local_eq global_eq by simp
qed

lemma lookup_resolved_st_eq_default:
  assumes "loc \<notin> set (raw_support s)"
  shows "lookup_resolved_st s loc = resolved_default s loc"
proof (cases s)
  case (fields dl dg entries)
  have entries_none: "map_of entries loc = None"
    using assms fields
    by (simp add: raw_support.simps map_of_resolved_none_iff)
  show ?thesis
    using fields entries_none by (cases loc) simp_all
qed

lemma effective_support_mem_eq:
  assumes eq: "eq_resolved_st (dl, dg, ps) (el, eg, qs)"
    and loc: "loc \<in> set (effective_support (dl, dg, ps))"
  shows "loc \<in> set (effective_support (el, eg, qs))"
proof -
  have loc_ps: "loc \<in> set (map fst ps)"
    and unequal: "lookup_resolved_st (dl, dg, ps) loc \<noteq>
      resolved_default (dl, dg, ps) loc"
    using loc by (auto simp: set_effective_support raw_support.simps)
  have defaults: "dl = el \<and> dg = eg"
    using eq by (rule eq_resolved_st_defaults)
  have lookup:
    "lookup_resolved_st (dl, dg, ps) =
      lookup_resolved_st (el, eg, qs)"
    using eq unfolding eq_resolved_st_def by simp
  have lookup_loc:
    "lookup_resolved_st (dl, dg, ps) loc =
      lookup_resolved_st (el, eg, qs) loc"
    using lookup by (rule fun_cong)
  have loc_qs: "loc \<in> set (map fst qs)"
  proof (rule ccontr)
    assume not_qs: "\<not> loc \<in> set (map fst qs)"
    have qs_not: "loc \<notin> set (raw_support (el, eg, qs))"
      using not_qs by simp
    have qs_value:
      "lookup_resolved_st (el, eg, qs) loc =
        resolved_default (el, eg, qs) loc"
      using qs_not by (rule lookup_resolved_st_eq_default)
    show False
      using unequal defaults qs_value lookup_loc
      by (cases loc) simp_all
  qed
  have target_unequal:
    "lookup_resolved_st (el, eg, qs) loc \<noteq>
      resolved_default (el, eg, qs) loc"
  proof
    assume target_eq:
      "lookup_resolved_st (el, eg, qs) loc =
        resolved_default (el, eg, qs) loc"
    show False
      using unequal defaults target_eq lookup_loc
      by (cases loc) simp_all
  qed
  show ?thesis
    using loc_qs target_unequal
    by (auto simp: set_effective_support raw_support.simps)
qed

lemma eq_resolved_st_effective_support:
  assumes "eq_resolved_st (dl, dg, ps) (el, eg, qs)"
  shows
    "set (effective_support (dl, dg, ps)) =
      set (effective_support (el, eg, qs))"
proof (rule subset_antisym)
  show "set (effective_support (dl, dg, ps)) \<subseteq>
      set (effective_support (el, eg, qs))"
    using assms by (auto intro: effective_support_mem_eq)
next
  show "set (effective_support (el, eg, qs)) \<subseteq>
      set (effective_support (dl, dg, ps))"
    using assms
    by (auto intro: effective_support_mem_eq[OF
      equivp_symp[OF equivp_eq_resolved_st]])
qed


definition project_resolved_on_raw ::
  "pname => location list => (scoped_location => bool) =>
   ('a::bot) resolved_st => 'a resolved_st" where
  "project_resolved_on_raw owner universe placed s =
    foldr (\<lambda>loc result.
      if placed (owner, loc)
      then update_resolved_st result loc (lookup_resolved_st s loc)
      else result)
    (remdups (universe @ effective_support s)) (bot, bot, [])"
lemma lookup_materialize_locations:
  fixes locations :: "location list"
  shows
    "lookup_resolved_st
      (foldr (\<lambda>loc result.
        if placed (owner, loc)
        then update_resolved_st result loc (lookup_resolved_st s loc)
        else result)
        locations (bot, bot, [])) target =
      (if target \<in> set locations \<and> placed (owner, target)
       then lookup_resolved_st s target else bot)"
proof (induction locations)
  case Nil
  then show ?case by (cases target) simp_all
next
  case (Cons loc locations)
  show ?case
  proof (cases "loc = target")
    case True
    show ?thesis
    proof (cases "placed (owner, target)")
      case True
      with `loc = target` show ?thesis by simp
    next
      case False
      with `loc = target` Cons.IH show ?thesis by simp
    qed
  next
    case False
    then show ?thesis
      using Cons by (simp add: lookup_resolved_st_update_diff)
  qed
qed

lemma lookup_project_resolved_on_raw:
  "lookup_resolved_st (project_resolved_on_raw owner universe placed s) target =
    (if target \<in> set (remdups (universe @ effective_support s)) \<and>
        placed (owner, target)
     then lookup_resolved_st s target else bot)"
  unfolding project_resolved_on_raw_def
  by (rule lookup_materialize_locations)

lemma lookup_project_resolved_on_raw_relevant:
  assumes "target \<in> set (universe @ effective_support s)"
  shows
    "lookup_resolved_st (project_resolved_on_raw owner universe placed s) target =
      (if placed (owner, target) then lookup_resolved_st s target else bot)"
  using assms by (simp add: lookup_project_resolved_on_raw)

lemma eq_resolved_st_project_resolved_on_raw:
  assumes eq: "eq_resolved_st s t"
  shows "eq_resolved_st
    (project_resolved_on_raw owner universe placed s)
    (project_resolved_on_raw owner universe placed t)"
proof -
  obtain dl dg ps where s: "s = (dl, dg, ps)"
    by (cases s)
  obtain el eg qs where t: "t = (el, eg, qs)"
    by (cases t)
  have effective:
    "set (effective_support s) = set (effective_support t)"
    using eq s t by (simp add: eq_resolved_st_effective_support)
  have lookup: "lookup_resolved_st s = lookup_resolved_st t"
    using eq unfolding eq_resolved_st_def by simp
  show ?thesis
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix target
    have relevant:
      "target \<in> set (remdups (universe @ effective_support s)) \<longleftrightarrow>
        target \<in> set (remdups (universe @ effective_support t))"
      using effective by simp
    show "lookup_resolved_st
      (project_resolved_on_raw owner universe placed s) target =
      lookup_resolved_st
      (project_resolved_on_raw owner universe placed t) target"
      using relevant lookup
      by (simp add: lookup_project_resolved_on_raw fun_eq_iff)
  qed
qed

lift_definition project_resolved_on ::
  "pname => location list => (scoped_location => bool) =>
   ('a::bot) resolved_st_q => 'a resolved_st_q"
  is project_resolved_on_raw
  by (rule eq_resolved_st_project_resolved_on_raw)

lemma project_resolved_on_Abs:
  "project_resolved_on owner universe placed (Abs_resolved_st s) =
    Abs_resolved_st (project_resolved_on_raw owner universe placed s)"
  by transfer (simp add: eq_resolved_st_def)

lemma lookup_project_resolved_on_Abs:
  "lookup_resolved_st_q
    (project_resolved_on owner universe placed (Abs_resolved_st s)) target =
    (if target \<in> set (remdups (universe @ effective_support s)) \<and>
        placed (owner, target)
     then lookup_resolved_st s target else bot)"
  by (simp add: project_resolved_on_Abs lookup_project_resolved_on_raw)

lemma lookup_project_resolved_on:
  "lookup_resolved_st_q
    (project_resolved_on owner universe placed s) target =
    (if target \<in>
        set (remdups
          (universe @ effective_support (rep_resolved_st s))) \<and>
        placed (owner, target)
     then lookup_resolved_st_q s target else bot)"
proof -
  have abs: "Abs_resolved_st (rep_resolved_st s) = s"
    by simp
  show ?thesis
    using lookup_project_resolved_on_Abs[
      of owner universe placed "rep_resolved_st s" target]
    unfolding abs
    by (simp add: lookup_rep_resolved_st_q)
qed

lemma lookup_project_resolved_on_relevant:
  assumes "target \<in>
    set (universe @ effective_support (rep_resolved_st s))"
  shows
    "lookup_resolved_st_q
      (project_resolved_on owner universe placed s) target =
      (if placed (owner, target)
       then lookup_resolved_st_q s target else bot)"
  using assms by (simp add: lookup_project_resolved_on)


lemma lookup_project_resolved_on_join:
  fixes s :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  assumes relevant:
    "target \<in> set (universe @ effective_support (rep_resolved_st s))"
    and covered: "keep_local (owner, target) \<or> publish_side (owner, target)"
  shows
    "lookup_resolved_st_q
      (project_resolved_on owner universe keep_local s \<squnion>
       project_resolved_on owner universe publish_side s) target =
      lookup_resolved_st_q s target"
proof (cases "keep_local (owner, target)")
  case True
  with relevant show ?thesis
    by (simp add: lookup_project_resolved_on_relevant)
next
  case False
  with covered have publish: "publish_side (owner, target)"
    by simp
  with relevant show ?thesis
    by (simp add: lookup_project_resolved_on_relevant)
qed

lemma lookup_project_resolved_on_classic_local:
  fixes s :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  assumes relevant:
    "target \<in> set (universe @ effective_support (rep_resolved_st s))"
  shows
    "lookup_resolved_st_q
      (project_resolved_on owner universe classic_keep_local s) target =
      lookup_resolved_st_q (restrict_local_resolved_q s) target"
proof (cases target)
  case (Local_Location x)
  then show ?thesis
    using relevant
    by (simp add: classic_keep_local_def
      lookup_project_resolved_on_relevant)
next
  case (Global_Location x)
  then show ?thesis
    using relevant
    by (simp add: classic_keep_local_def
      lookup_project_resolved_on_relevant)
qed

lemma lookup_project_resolved_on_classic_side:
  fixes s :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  assumes relevant:
    "target \<in> set (universe @ effective_support (rep_resolved_st s))"
  shows
    "lookup_resolved_st_q
      (project_resolved_on owner universe classic_publish_side s) target =
      lookup_resolved_st_q (restrict_global_resolved_q s) target"
proof (cases target)
  case (Local_Location x)
  then show ?thesis
    using relevant
    by (simp add: classic_publish_side_def
      lookup_project_resolved_on_relevant)
next
  case (Global_Location x)
  then show ?thesis
    using relevant
    by (simp add: classic_publish_side_def
      lookup_project_resolved_on_relevant)
qed

end

