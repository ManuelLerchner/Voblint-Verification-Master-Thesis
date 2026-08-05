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

lemma global_location_in_scope_locations:
  assumes "Global_Location x \<in> set (scope_locations p owner)"
  shows "declared_global p x"
  using assms
  by (auto simp: location_of_def)

text \<open>\<open>storage_global p owner\<close> never actually depends on \<open>owner\<close>
  (\<open>storage_global_iff\<close>): source-declared globals are program-global facts,
  not owner-relative ones.\<close>

lemma storage_global_eq_declared_global:
  "storage_global p owner = declared_global p"
  by (rule ext) (simp add: storage_global_iff)

text \<open>Every location a scope lists already resolves back to itself under
  \<^const>\<open>declared_global\<close>: \<^const>\<open>scope_locations\<close> is built as an image of
  \<^const>\<open>location_of\<close>, so this holds for any program and owner, with no
  further side condition. A placement instance cites this directly instead of
  re-deriving the \<^const>\<open>storage_global\<close>/\<^const>\<open>declared_global\<close> bridge
  itself.\<close>

lemma scope_locations_canonical:
  assumes "location \<in> set (scope_locations p owner)"
  shows "location = location_of (declared_global p) (location_vname location)"
proof -
  obtain x where x: "location = location_of (declared_global p) x"
    using assms
    unfolding set_scope_locations storage_global_eq_declared_global
    by auto
  then show ?thesis by (simp add: location_of_def)
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

lemma eq_resolved_st_effective_support_gen:
  assumes "eq_resolved_st s t"
  shows "set (effective_support s) = set (effective_support t)"
proof -
  obtain dl dg ps where s: "s = (dl, dg, ps)" by (cases s) auto
  obtain el eg qs where t: "t = (el, eg, qs)" by (cases t) auto
  show ?thesis
    using assms unfolding s t by (rule eq_resolved_st_effective_support)
qed

subsection \<open>Support-growth algebra\<close>

text \<open>
  A location outside a state's effective support already carries that
  state's own default, whether or not it ever appeared in the raw override
  list.  Every growth bound below reduces to this one fact: showing a
  candidate bound covers the difference is the only thing that varies
  between \<^const>\<open>update_resolved_st\<close> and \<^const>\<open>merge_resolved_st\<close>.
\<close>

lemma lookup_resolved_st_outside_effective_support:
  "loc \<notin> set (effective_support s) \<Longrightarrow>
     lookup_resolved_st s loc = resolved_default s loc"
proof (cases "loc \<in> set (raw_support s)")
  case True
  assume "loc \<notin> set (effective_support s)"
  with True show ?thesis by (auto simp: set_effective_support)
next
  case False
  then show ?thesis by (rule lookup_resolved_st_eq_default)
qed

lemma effective_support_subsetI:
  assumes "\<And>loc. loc \<notin> bound \<Longrightarrow>
    lookup_resolved_st s loc = resolved_default s loc"
  shows "set (effective_support s) \<subseteq> bound"
proof
  fix loc assume "loc \<in> set (effective_support s)"
  then have "lookup_resolved_st s loc \<noteq> resolved_default s loc"
    by (simp add: set_effective_support)
  then show "loc \<in> bound" using assms by blast
qed

lemma resolved_default_update [simp]:
  "resolved_default (update_resolved_st s loc a) = resolved_default s"
proof (rule ext)
  fix x
  show "resolved_default (update_resolved_st s loc a) x = resolved_default s x"
    by (cases s; cases x; simp)
qed

lemma resolved_default_materialize_locations:
  "resolved_default (foldr (\<lambda>loc result.
      if placed (owner, loc)
      then update_resolved_st result loc (lookup_resolved_st s loc)
      else result)
    locations (bot, bot, [])) = (\<lambda>_. bot)"
proof (induction locations)
  case Nil
  show ?case
  proof (rule ext)
    fix loc
    show "resolved_default (foldr (\<lambda>loc result.
        if placed (owner, loc)
        then update_resolved_st result loc (lookup_resolved_st s loc)
        else result) [] (bot, bot, [])) loc = bot"
      by (cases loc) simp_all
  qed
next
  case (Cons loc locations)
  show ?case
  proof (cases "placed (owner, loc)")
    case True
    then show ?thesis using Cons.IH by simp
  next
    case False
    then show ?thesis using Cons.IH by simp
  qed
qed

lemma effective_support_update_resolved_st:
  "set (effective_support (update_resolved_st s loc a)) \<subseteq>
     insert loc (set (effective_support s))"
proof (rule effective_support_subsetI)
  fix loc' assume "loc' \<notin> insert loc (set (effective_support s))"
  then have neq: "loc' \<noteq> loc" and out: "loc' \<notin> set (effective_support s)"
    by simp_all
  have "lookup_resolved_st (update_resolved_st s loc a) loc' =
      lookup_resolved_st s loc'"
    using neq[symmetric] by (rule lookup_resolved_st_update_diff)
  also have "\<dots> = resolved_default s loc'"
    using out by (rule lookup_resolved_st_outside_effective_support)
  finally show "lookup_resolved_st (update_resolved_st s loc a) loc' =
      resolved_default (update_resolved_st s loc a) loc'"
    by simp
qed

lemma resolved_default_merge:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st"
  shows "resolved_default (merge_resolved_st s t) loc =
      resolved_default s loc \<squnion> resolved_default t loc"
  by (cases s; cases t; cases loc; simp)

lemma effective_support_merge_resolved_st:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st"
  shows "set (effective_support (merge_resolved_st s t)) \<subseteq>
     set (effective_support s) \<union> set (effective_support t)"
proof (rule effective_support_subsetI)
  fix loc
  assume "loc \<notin> set (effective_support s) \<union> set (effective_support t)"
  then have outs: "loc \<notin> set (effective_support s)"
    and outt: "loc \<notin> set (effective_support t)" by simp_all
  have "lookup_resolved_st (merge_resolved_st s t) loc =
      lookup_resolved_st s loc \<squnion> lookup_resolved_st t loc" by simp
  also have "\<dots> = resolved_default s loc \<squnion> resolved_default t loc"
    using outs outt
    by (simp add: lookup_resolved_st_outside_effective_support)
  finally show "lookup_resolved_st (merge_resolved_st s t) loc =
      resolved_default (merge_resolved_st s t) loc"
    by (simp add: resolved_default_merge)
qed

lemma effective_support_bot_resolved_st [simp]:
  "set (effective_support (bot, bot, [])) = {}"
  by (simp add: effective_support_def)

text \<open>
  Quotient-level growth: \<^const>\<open>effective_support\<close> is invariant under
  \<^const>\<open>eq_resolved_st\<close> (\<open>eq_resolved_st_effective_support\<close> above), so the
  raw growth bounds transport to \<^const>\<open>rep_resolved_st\<close> once the quotient
  operation's representative is related to the raw operation applied to the
  representative.  Lookup equality at every location settles that relation
  directly, without unfolding the quotient's transfer machinery.
\<close>

lemma eq_resolved_st_rep_update_resolved_st_q:
  "eq_resolved_st (rep_resolved_st (update_resolved_st_q s loc a))
     (update_resolved_st (rep_resolved_st s) loc a)"
  unfolding eq_resolved_st_def
proof (rule ext)
  fix loc'
  show "lookup_resolved_st (rep_resolved_st (update_resolved_st_q s loc a)) loc' =
      lookup_resolved_st (update_resolved_st (rep_resolved_st s) loc a) loc'"
  proof (cases "loc = loc'")
    case True
    then show ?thesis
      by (simp add: lookup_rep_resolved_st_q[symmetric])
  next
    case False
    then show ?thesis
      by (simp add: lookup_rep_resolved_st_q[symmetric])
  qed
qed

lemma effective_support_rep_update_resolved_st_q:
  "set (effective_support (rep_resolved_st (update_resolved_st_q s loc a))) \<subseteq>
     insert loc (set (effective_support (rep_resolved_st s)))"
proof -
  have "set (effective_support (rep_resolved_st (update_resolved_st_q s loc a))) =
      set (effective_support (update_resolved_st (rep_resolved_st s) loc a))"
    by (rule eq_resolved_st_effective_support_gen
      [OF eq_resolved_st_rep_update_resolved_st_q])
  also have "\<dots> \<subseteq> insert loc (set (effective_support (rep_resolved_st s)))"
    by (rule effective_support_update_resolved_st)
  finally show ?thesis .
qed

lemma eq_resolved_st_rep_sup_resolved_st_q:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  shows "eq_resolved_st (rep_resolved_st (s \<squnion> t))
     (merge_resolved_st (rep_resolved_st s) (rep_resolved_st t))"
  unfolding eq_resolved_st_def
proof (rule ext)
  fix loc
  have "lookup_resolved_st (rep_resolved_st (s \<squnion> t)) loc =
      lookup_resolved_st_q (s \<squnion> t) loc"
    by (simp add: lookup_rep_resolved_st_q)
  also have "\<dots> = lookup_resolved_st_q s loc \<squnion> lookup_resolved_st_q t loc"
    by simp
  also have "\<dots> = lookup_resolved_st (rep_resolved_st s) loc \<squnion>
      lookup_resolved_st (rep_resolved_st t) loc"
    by (simp add: lookup_rep_resolved_st_q)
  also have "\<dots> = lookup_resolved_st
      (merge_resolved_st (rep_resolved_st s) (rep_resolved_st t)) loc"
    by simp
  finally show "lookup_resolved_st (rep_resolved_st (s \<squnion> t)) loc =
      lookup_resolved_st
        (merge_resolved_st (rep_resolved_st s) (rep_resolved_st t)) loc" .
qed

lemma effective_support_rep_sup_resolved_st_q:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  shows "set (effective_support (rep_resolved_st (s \<squnion> t))) \<subseteq>
     set (effective_support (rep_resolved_st s)) \<union>
     set (effective_support (rep_resolved_st t))"
proof -
  have "set (effective_support (rep_resolved_st (s \<squnion> t))) =
      set (effective_support
        (merge_resolved_st (rep_resolved_st s) (rep_resolved_st t)))"
    by (rule eq_resolved_st_effective_support_gen
      [OF eq_resolved_st_rep_sup_resolved_st_q])
  also have "\<dots> \<subseteq> set (effective_support (rep_resolved_st s)) \<union>
      set (effective_support (rep_resolved_st t))"
    by (rule effective_support_merge_resolved_st)
  finally show ?thesis .
qed

lemma effective_support_rep_bot_resolved_st_q [simp]:
  "set (effective_support (rep_resolved_st
    (bot :: ('a::bounded_semilattice_sup_bot) resolved_st_q))) = {}"
proof -
  have bot_eq: "eq_resolved_st (rep_resolved_st (bot :: 'a resolved_st_q)) (bot, bot, [])"
    unfolding eq_resolved_st_def bot_resolved_st_q_def
    by (rule ext) (simp add: lookup_rep_resolved_st_q[symmetric])
  show ?thesis
    using eq_resolved_st_effective_support_gen[OF bot_eq] by simp
qed

text \<open>
  \<^const>\<open>combine_resolved_st\<close> keeps locals from its caller-side argument and
  globals from its callee-side argument (\<open>lookup_combine_resolved_st\<close>), so
  its support splits by location kind rather than unioning both arguments'
  supports outright: a callee-only local never survives into the combined
  result.
\<close>

lemma resolved_default_combine:
  fixes sc se :: "('a::bot) resolved_st"
  shows "resolved_default (combine_resolved_st sc se) loc =
    (case loc of
       Local_Location x => resolved_default sc loc
     | Global_Location x => resolved_default se loc)"
  by (cases sc; cases se; cases loc; simp add: combine_resolved_st_def)

lemma effective_support_combine_resolved_st:
  fixes sc se :: "('a::bot) resolved_st"
  shows "set (effective_support (combine_resolved_st sc se)) \<subseteq>
    {loc \<in> set (effective_support sc). location_is_local loc} \<union>
    {loc \<in> set (effective_support se). location_is_global loc}"
proof (rule effective_support_subsetI)
  fix loc
  assume out: "loc \<notin>
    {loc \<in> set (effective_support sc). location_is_local loc} \<union>
    {loc \<in> set (effective_support se). location_is_global loc}"
  show "lookup_resolved_st (combine_resolved_st sc se) loc =
      resolved_default (combine_resolved_st sc se) loc"
  proof (cases loc)
    case (Local_Location x)
    then have "loc \<notin> set (effective_support sc)" using out by auto
    then have "lookup_resolved_st sc loc = resolved_default sc loc"
      by (rule lookup_resolved_st_outside_effective_support)
    then show ?thesis using Local_Location by (simp add: resolved_default_combine)
  next
    case (Global_Location x)
    then have "loc \<notin> set (effective_support se)" using out by auto
    then have "lookup_resolved_st se loc = resolved_default se loc"
      by (rule lookup_resolved_st_outside_effective_support)
    then show ?thesis using Global_Location by (simp add: resolved_default_combine)
  qed
qed

lemma effective_support_combine_collect_resolved_for:
  fixes sc se :: "('a::bot) resolved_st"
  shows "set (effective_support (combine_collect_resolved_for gs dst sc se)) \<subseteq>
    {loc \<in> set (effective_support sc). location_is_local loc} \<union>
    {loc \<in> set (effective_support se). location_is_global loc} \<union>
    (case dst of None => {} | Some x => {location_of gs x})"
proof (cases dst)
  case None
  have eq: "combine_collect_resolved_for gs None sc se = combine_resolved_st sc se"
    unfolding combine_collect_resolved_for_def combine_assign_resolved_def
    by simp
  show ?thesis
    unfolding None eq
  proof -
    have "set (effective_support (combine_resolved_st sc se)) \<subseteq>
        {loc \<in> set (effective_support sc). location_is_local loc} \<union>
        {loc \<in> set (effective_support se). location_is_global loc}"
      by (rule effective_support_combine_resolved_st)
    then show "set (effective_support (combine_resolved_st sc se)) \<subseteq>
        {loc \<in> set (effective_support sc). location_is_local loc} \<union>
        {loc \<in> set (effective_support se). location_is_global loc} \<union>
        (case None of None \<Rightarrow> {} | Some x \<Rightarrow> {location_of gs x})"
      by auto
  qed
next
  case (Some x)
  have "set (effective_support (combine_collect_resolved_for gs dst sc se)) \<subseteq>
      insert (location_of gs x) (set (effective_support (combine_resolved_st sc se)))"
    unfolding combine_collect_resolved_for_def combine_assign_resolved_def Some
    by (simp add: effective_support_update_resolved_st)
  also have "\<dots> \<subseteq>
      {loc \<in> set (effective_support sc). location_is_local loc} \<union>
      {loc \<in> set (effective_support se). location_is_global loc} \<union>
      {location_of gs x}"
  proof -
    have "set (effective_support (combine_resolved_st sc se)) \<subseteq>
        {loc \<in> set (effective_support sc). location_is_local loc} \<union>
        {loc \<in> set (effective_support se). location_is_global loc}"
      by (rule effective_support_combine_resolved_st)
    then show "insert (location_of gs x) (set (effective_support (combine_resolved_st sc se))) \<subseteq>
        {loc \<in> set (effective_support sc). location_is_local loc} \<union>
        {loc \<in> set (effective_support se). location_is_global loc} \<union>
        {location_of gs x}"
      by auto
  qed
  finally show ?thesis using Some by simp
qed

lemma combine_collect_resolved_for_q_Abs:
  "combine_collect_resolved_for_q gs dst (Abs_resolved_st a) (Abs_resolved_st b) =
   Abs_resolved_st (combine_collect_resolved_for gs dst a b)"
  by (simp add: combine_collect_resolved_for_q.abs_eq)

lemma eq_resolved_st_rep_combine_collect_resolved_for_q:
  "eq_resolved_st (rep_resolved_st (combine_collect_resolved_for_q gs dst sc se))
     (combine_collect_resolved_for gs dst (rep_resolved_st sc) (rep_resolved_st se))"
proof -
  have "combine_collect_resolved_for_q gs dst sc se =
      combine_collect_resolved_for_q gs dst
        (Abs_resolved_st (rep_resolved_st sc)) (Abs_resolved_st (rep_resolved_st se))"
    by simp
  also have "\<dots> =
      Abs_resolved_st (combine_collect_resolved_for gs dst
        (rep_resolved_st sc) (rep_resolved_st se))"
    by (rule combine_collect_resolved_for_q_Abs)
  finally have eq: "combine_collect_resolved_for_q gs dst sc se =
      Abs_resolved_st (combine_collect_resolved_for gs dst
        (rep_resolved_st sc) (rep_resolved_st se))" .
  show ?thesis
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    have "lookup_resolved_st (rep_resolved_st
        (combine_collect_resolved_for_q gs dst sc se)) loc =
      lookup_resolved_st_q (combine_collect_resolved_for_q gs dst sc se) loc"
      by (simp add: lookup_rep_resolved_st_q)
    also have "\<dots> = lookup_resolved_st_q (Abs_resolved_st
        (combine_collect_resolved_for gs dst
          (rep_resolved_st sc) (rep_resolved_st se))) loc"
      by (simp add: eq)
    also have "\<dots> = lookup_resolved_st (combine_collect_resolved_for gs dst
        (rep_resolved_st sc) (rep_resolved_st se)) loc"
      by (rule lookup_Abs_resolved_st_q)
    finally show "lookup_resolved_st (rep_resolved_st
        (combine_collect_resolved_for_q gs dst sc se)) loc =
      lookup_resolved_st (combine_collect_resolved_for gs dst
        (rep_resolved_st sc) (rep_resolved_st se)) loc" .
  qed
qed

lemma effective_support_rep_combine_collect_resolved_for_q:
  "set (effective_support (rep_resolved_st
      (combine_collect_resolved_for_q gs dst sc se))) \<subseteq>
    {loc \<in> set (effective_support (rep_resolved_st sc)). location_is_local loc} \<union>
    {loc \<in> set (effective_support (rep_resolved_st se)). location_is_global loc} \<union>
    (case dst of None => {} | Some x => {location_of gs x})"
proof -
  have "set (effective_support (rep_resolved_st
      (combine_collect_resolved_for_q gs dst sc se))) =
      set (effective_support (combine_collect_resolved_for gs dst
        (rep_resolved_st sc) (rep_resolved_st se)))"
    using eq_resolved_st_effective_support_gen
      [OF eq_resolved_st_rep_combine_collect_resolved_for_q] .
  also have "\<dots> \<subseteq>
      {loc \<in> set (effective_support (rep_resolved_st sc)). location_is_local loc} \<union>
      {loc \<in> set (effective_support (rep_resolved_st se)). location_is_global loc} \<union>
      (case dst of None => {} | Some x => {location_of gs x})"
    by (rule effective_support_combine_collect_resolved_for)
  finally show ?thesis .
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

text \<open>
  \<^const>\<open>project_resolved_on\<close> is not a generalization of
  \<^const>\<open>restrict_local_resolved_q\<close>/\<^const>\<open>restrict_global_resolved_q\<close>
  (\<^theory>\<open>Voblint_Core.Exec_St\<close>). That pair preserves the source state's own
  per-location default over an unbounded location space; this projection
  optimizes for the opposite invariant, a bounded materialized support, and
  always re-seeds from \<^term>\<open>(bot, bot, [])\<close> before folding over
  \<^term>\<open>universe @ effective_support s\<close>. Anything not in that finite list is
  \<^term>\<open>bot\<close> in the result, regardless of what the source's own default said
  there. Concretely: for \<^term>\<open>s\<close> with \<^term>\<open>rep_resolved_st s = (top, bot, [])\<close>
  and \<^term>\<open>universe = []\<close>, \<^const>\<open>restrict_local_resolved_q\<close> reports
  \<^term>\<open>top\<close> at every local location, while \<^const>\<open>project_resolved_on\<close>
  reports \<^term>\<open>bot\<close> at every local location -- no choice of \<^term>\<open>universe\<close>
  closes this, since it is always finite and the disagreement is at every
  location outside it. The two constructions serve different representational
  contracts and both stay, permanently; see also the note at
  \<^const>\<open>restrict_local_resolved_q\<close>'s own definition.
\<close>

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

subsection \<open>Strict projection\<close>

text \<open>
  \<^const>\<open>project_resolved_on\<close> materializes \<open>universe @ effective_support s\<close>: a
  defensive escape hatch that reproduces an unplaced, unscoped source's actual
  support even when \<open>universe\<close> does not anticipate it.  That behavior is what
  the classic-equivalence lemmas above need (comparing a placed tree against
  an unplaced one whose own support is not bounded by any declared scope).
  A generated placement equation system has no such unplaced comparison to
  honor; its \<open>universe\<close> is the write node's own declared scope, and nothing
  outside it should ever survive projection.  \<open>project_resolved_on_strict\<close>
  drops the escape hatch, so its own support is bounded by \<open>universe\<close> alone,
  unconditionally --- no fact about the source state's support is needed.
\<close>

definition project_resolved_on_strict_raw ::
  "pname => location list => (scoped_location => bool) =>
   ('a::bot) resolved_st => 'a resolved_st" where
  "project_resolved_on_strict_raw owner universe placed s =
    foldr (\<lambda>loc result.
      if placed (owner, loc)
      then update_resolved_st result loc (lookup_resolved_st s loc)
      else result)
    (remdups universe) (bot, bot, [])"

lemma lookup_project_resolved_on_strict_raw:
  "lookup_resolved_st (project_resolved_on_strict_raw owner universe placed s) target =
    (if target \<in> set (remdups universe) \<and> placed (owner, target)
     then lookup_resolved_st s target else bot)"
  unfolding project_resolved_on_strict_raw_def
  by (rule lookup_materialize_locations)

lemma eq_resolved_st_project_resolved_on_strict_raw:
  assumes eq: "eq_resolved_st s t"
  shows "eq_resolved_st
    (project_resolved_on_strict_raw owner universe placed s)
    (project_resolved_on_strict_raw owner universe placed t)"
  unfolding eq_resolved_st_def
proof (rule ext)
  fix target
  have lookup: "lookup_resolved_st s = lookup_resolved_st t"
    using eq unfolding eq_resolved_st_def by simp
  show "lookup_resolved_st
      (project_resolved_on_strict_raw owner universe placed s) target =
    lookup_resolved_st
      (project_resolved_on_strict_raw owner universe placed t) target"
    using lookup by (simp add: lookup_project_resolved_on_strict_raw fun_eq_iff)
qed

lift_definition project_resolved_on_strict ::
  "pname => location list => (scoped_location => bool) =>
   ('a::bot) resolved_st_q => 'a resolved_st_q"
  is project_resolved_on_strict_raw
  by (rule eq_resolved_st_project_resolved_on_strict_raw)

lemma project_resolved_on_strict_Abs:
  "project_resolved_on_strict owner universe placed (Abs_resolved_st s) =
    Abs_resolved_st (project_resolved_on_strict_raw owner universe placed s)"
  by transfer (simp add: eq_resolved_st_def)

lemma lookup_project_resolved_on_strict_Abs:
  "lookup_resolved_st_q
    (project_resolved_on_strict owner universe placed (Abs_resolved_st s)) target =
    (if target \<in> set (remdups universe) \<and> placed (owner, target)
     then lookup_resolved_st s target else bot)"
  by (simp add: project_resolved_on_strict_Abs lookup_project_resolved_on_strict_raw)

lemma lookup_project_resolved_on_strict:
  "lookup_resolved_st_q
    (project_resolved_on_strict owner universe placed s) target =
    (if target \<in> set universe \<and> placed (owner, target)
     then lookup_resolved_st_q s target else bot)"
proof -
  have abs: "Abs_resolved_st (rep_resolved_st s) = s"
    by simp
  show ?thesis
    using lookup_project_resolved_on_strict_Abs[
      of owner universe placed "rep_resolved_st s" target]
    unfolding abs
    by (simp add: lookup_rep_resolved_st_q)
qed

lemma effective_support_project_resolved_on_strict_raw:
  "set (effective_support (project_resolved_on_strict_raw owner universe placed s)) \<subseteq>
     set universe"
proof (rule effective_support_subsetI)
  fix loc assume "loc \<notin> set universe"
  then have out: "loc \<notin> set (remdups universe)" by simp
  have lookup:
    "lookup_resolved_st (project_resolved_on_strict_raw owner universe placed s) loc = bot"
    using out by (simp add: lookup_project_resolved_on_strict_raw)
  have default:
    "resolved_default (project_resolved_on_strict_raw owner universe placed s) loc = bot"
    unfolding project_resolved_on_strict_raw_def
    by (simp add: resolved_default_materialize_locations)
  show "lookup_resolved_st (project_resolved_on_strict_raw owner universe placed s) loc =
      resolved_default (project_resolved_on_strict_raw owner universe placed s) loc"
    using lookup default by simp
qed

lemma eq_resolved_st_rep_project_resolved_on_strict:
  "eq_resolved_st (rep_resolved_st (project_resolved_on_strict owner universe placed s))
     (project_resolved_on_strict_raw owner universe placed (rep_resolved_st s))"
  unfolding eq_resolved_st_def
proof (rule ext)
  fix loc
  have lhs: "lookup_resolved_st (rep_resolved_st
      (project_resolved_on_strict owner universe placed s)) loc =
    lookup_resolved_st_q (project_resolved_on_strict owner universe placed s) loc"
    by (simp add: lookup_rep_resolved_st_q)
  have rhs: "lookup_resolved_st
      (project_resolved_on_strict_raw owner universe placed (rep_resolved_st s)) loc =
    (if loc \<in> set (remdups universe) \<and> placed (owner, loc)
     then lookup_resolved_st (rep_resolved_st s) loc else bot)"
    by (rule lookup_project_resolved_on_strict_raw)
  show "lookup_resolved_st (rep_resolved_st
      (project_resolved_on_strict owner universe placed s)) loc =
    lookup_resolved_st
      (project_resolved_on_strict_raw owner universe placed (rep_resolved_st s)) loc"
    unfolding lhs rhs
    using lookup_rep_resolved_st_q[of s loc]
    by (simp add: lookup_project_resolved_on_strict)
qed

lemma effective_support_rep_project_resolved_on_strict:
  "set (effective_support (rep_resolved_st
    (project_resolved_on_strict owner universe placed s))) \<subseteq> set universe"
proof -
  have "set (effective_support (rep_resolved_st
      (project_resolved_on_strict owner universe placed s))) =
      set (effective_support
        (project_resolved_on_strict_raw owner universe placed (rep_resolved_st s)))"
    by (rule eq_resolved_st_effective_support_gen
      [OF eq_resolved_st_rep_project_resolved_on_strict])
  also have "\<dots> \<subseteq> set universe"
    by (rule effective_support_project_resolved_on_strict_raw)
  finally show ?thesis .
qed

text \<open>
  A strict projection's own raw default is always \<open>bot\<close> (its materializing
  fold starts from \<open>(bot, bot, [])\<close>): its support bound plus its own
  bot-defaultedness are the two facts the generator-level transport needs to
  discharge the inequality-lifting lemma's outside-scope obligation without
  any solver-side induction.
\<close>

lemma eq_resolved_st_resolved_default_gen:
  assumes "eq_resolved_st s t"
  shows "resolved_default s = resolved_default t"
proof -
  obtain dl dg ps where s: "s = (dl, dg, ps)" by (cases s) auto
  obtain el eg qs where t: "t = (el, eg, qs)" by (cases t) auto
  have eq: "dl = el \<and> dg = eg"
    using assms unfolding s t by (rule eq_resolved_st_defaults)
  show ?thesis
    unfolding s t
  proof (rule ext)
    fix x show "resolved_default (dl, dg, ps) x = resolved_default (el, eg, qs) x"
      using eq by (cases x) simp_all
  qed
qed

lemma resolved_default_rep_project_resolved_on_strict:
  "resolved_default (rep_resolved_st (project_resolved_on_strict owner universe placed s)) =
    (\<lambda>_. bot)"
proof -
  have "resolved_default (rep_resolved_st (project_resolved_on_strict owner universe placed s)) =
      resolved_default (project_resolved_on_strict_raw owner universe placed (rep_resolved_st s))"
    by (rule eq_resolved_st_resolved_default_gen
      [OF eq_resolved_st_rep_project_resolved_on_strict])
  also have "\<dots> = (\<lambda>_. bot)"
    unfolding project_resolved_on_strict_raw_def
    by (rule resolved_default_materialize_locations)
  finally show ?thesis .
qed

lemma resolved_default_merge_sup:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st"
  shows "resolved_default (merge_resolved_st s t) loc =
    resolved_default s loc \<squnion> resolved_default t loc"
  by (cases s; cases t; cases loc; simp)

lemma resolved_default_rep_sup_resolved_st_q:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  shows "resolved_default (rep_resolved_st (s \<squnion> t)) loc =
    resolved_default (rep_resolved_st s) loc \<squnion> resolved_default (rep_resolved_st t) loc"
proof -
  have "resolved_default (rep_resolved_st (s \<squnion> t)) =
      resolved_default (merge_resolved_st (rep_resolved_st s) (rep_resolved_st t))"
    by (rule eq_resolved_st_resolved_default_gen[OF eq_resolved_st_rep_sup_resolved_st_q])
  then show ?thesis
    by (simp add: resolved_default_merge_sup)
qed

lemma resolved_default_rep_bot_resolved_st_q:
  "resolved_default (rep_resolved_st
    (bot :: ('a::bounded_semilattice_sup_bot) resolved_st_q)) = (\<lambda>_. bot)"
proof -
  have bot_eq: "eq_resolved_st (rep_resolved_st (bot :: 'a resolved_st_q)) (bot, bot, [])"
    unfolding eq_resolved_st_def bot_resolved_st_q_def
    by (rule ext) (simp add: lookup_rep_resolved_st_q[symmetric])
  have "resolved_default (rep_resolved_st (bot :: 'a resolved_st_q)) =
      resolved_default (bot, bot, [])"
    by (rule eq_resolved_st_resolved_default_gen[OF bot_eq])
  also have "resolved_default ((bot, bot, []) :: 'a resolved_st) = (\<lambda>_. bot)"
  proof (rule ext)
    fix x show "resolved_default ((bot, bot, []) :: 'a resolved_st) x = bot"
      by (cases x) simp_all
  qed
  finally show ?thesis .
qed

text \<open>
  A projected state's own support never exceeds what it was asked to
  materialize: the declared scope together with whatever the source state
  already carried.  This is the bound the hook-tree transport needs --
  \<^const>\<open>project_resolved_on\<close> already gates everything outside
  \<open>universe @ effective_support s\<close> to \<open>bot\<close>
  (\<open>lookup_project_resolved_on_raw\<close>), so no separate growth induction over
  the materializing fold is required here.
\<close>

lemma effective_support_project_resolved_on_raw:
  "set (effective_support (project_resolved_on_raw owner universe placed s)) \<subseteq>
     set universe \<union> set (effective_support s)"
proof (rule effective_support_subsetI)
  fix loc assume "loc \<notin> set universe \<union> set (effective_support s)"
  then have out: "loc \<notin> set (remdups (universe @ effective_support s))"
    by simp
  have lookup:
    "lookup_resolved_st (project_resolved_on_raw owner universe placed s) loc = bot"
    using out by (simp add: lookup_project_resolved_on_raw)
  have default:
    "resolved_default (project_resolved_on_raw owner universe placed s) loc = bot"
    unfolding project_resolved_on_raw_def
    by (simp add: resolved_default_materialize_locations)
  show "lookup_resolved_st (project_resolved_on_raw owner universe placed s) loc =
      resolved_default (project_resolved_on_raw owner universe placed s) loc"
    using lookup default by simp
qed

lemma eq_resolved_st_rep_project_resolved_on:
  "eq_resolved_st (rep_resolved_st (project_resolved_on owner universe placed s))
     (project_resolved_on_raw owner universe placed (rep_resolved_st s))"
  unfolding eq_resolved_st_def
proof (rule ext)
  fix loc
  have lhs: "lookup_resolved_st (rep_resolved_st
      (project_resolved_on owner universe placed s)) loc =
    lookup_resolved_st_q (project_resolved_on owner universe placed s) loc"
    by (simp add: lookup_rep_resolved_st_q)
  have rhs: "lookup_resolved_st
      (project_resolved_on_raw owner universe placed (rep_resolved_st s)) loc =
    (if loc \<in> set (remdups (universe @ effective_support (rep_resolved_st s))) \<and>
        placed (owner, loc)
     then lookup_resolved_st (rep_resolved_st s) loc else bot)"
    by (rule lookup_project_resolved_on_raw)
  show "lookup_resolved_st (rep_resolved_st
      (project_resolved_on owner universe placed s)) loc =
    lookup_resolved_st
      (project_resolved_on_raw owner universe placed (rep_resolved_st s)) loc"
    unfolding lhs rhs
    using lookup_rep_resolved_st_q[of s loc]
    by (simp add: lookup_project_resolved_on)
qed

lemma effective_support_rep_project_resolved_on:
  "set (effective_support (rep_resolved_st
    (project_resolved_on owner universe placed s))) \<subseteq>
     set universe \<union> set (effective_support (rep_resolved_st s))"
proof -
  have "set (effective_support (rep_resolved_st
      (project_resolved_on owner universe placed s))) =
      set (effective_support
        (project_resolved_on_raw owner universe placed (rep_resolved_st s)))"
    using eq_resolved_st_effective_support_gen
      [OF eq_resolved_st_rep_project_resolved_on] .
  also have "\<dots> \<subseteq> set universe \<union> set (effective_support (rep_resolved_st s))"
    by (rule effective_support_project_resolved_on_raw)
  finally show ?thesis .
qed

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

