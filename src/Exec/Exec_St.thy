theory Exec_St
  imports "Voblint_Domain.Abstract_Domain" "TD.Update_rules"
    "Voblint_Core.Transfer_Interface" "HOL-Library.AList"
begin

text \<open>
  \<open>sup_over_origins\<close> (vendored, \<^theory>\<open>TD.Update_rules\<close>) is PerOrigin's own read of a
  global: the join, across every write origin, of that origin's own contribution. Its
  closure under \<^const>\<open>normalized_lift\<close> needs no new induction over
  \<^const>\<open>Finite_Set.fold\<close>/\<open>Sup_fin\<close>: \<open>sup_over_origins_upper\<close> already gives every
  contributing origin's own value as a lower bound on the joined read, the same shape
  \<open>sup_ge1\<close>/\<open>sup_ge2\<close> gave \<open>normalized_lift_sup\<close> above, so one live origin keeps the
  joined read live by the identical \<open>mono\<close> argument -- a corollary, not a fresh proof.
\<close>

lemma normalized_lift_sup_over_origins:
  fixes a :: "'a::bounded_warrowing"
  assumes mono: "\<And>p q::'a. p \<le> q \<Longrightarrow> is_bot_pred q \<Longrightarrow> is_bot_pred p"
    and contrib: "rho_lookup (\<rho> state) g orig = Lifted a"
    and not_bot_a: "\<not> is_bot_pred a"
  shows "normalized_lift is_bot_pred (sup_over_origins state g)"
proof -
  have le: "Lifted a \<le> sup_over_origins state g"
    using contrib by (rule sup_over_origins_upper)
  show ?thesis
  proof (cases "sup_over_origins state g")
    case Bot
    then show ?thesis by simp
  next
    case (Lifted c)
    from le Lifted have "a \<le> c" by simp
    with mono not_bot_a have "\<not> is_bot_pred c" by blast
    with Lifted show ?thesis by simp
  qed
qed

section \<open>Classifier-independent executable abstract state\<close>

text \<open>
  \<open>'a resolved_st\<close> stores local and global defaults together with explicit
  location-keyed overrides.  \<open>'a resolved_st_q\<close> quotients this representation
  by equality of all location lookups, so list order and duplicate keys are
  unobservable.

  The location classifier is supplied only by the later location_of
  conversion.  The quotient operations are defined on explicit locations and do not
  depend on a fixed classifier.  Refinement to @{typ "'a abs_state"} is
  parameterized by the classifier.
\<close>



subsection \<open>Core operations\<close>
datatype location =
  Local_Location (location_vname: vname)
| Global_Location (location_vname: vname)

type_synonym 'a resolved_st =
  "'a \<times> 'a \<times> (location \<times> 'a) list"

fun remove_resolved_key ::
  "location => (location \<times> 'a) list => (location \<times> 'a) list" where
  "remove_resolved_key loc [] = []"
| "remove_resolved_key loc ((loc', a) # ps) =
     (if loc = loc' then remove_resolved_key loc ps
      else (loc', a) # remove_resolved_key loc ps)"

lemma remove_resolved_key_eq_delete:
  "remove_resolved_key loc ps = AList.delete loc ps"
  by (induction ps) (auto split: if_splits)

lemma map_of_remove_resolved_key:
  "map_of (remove_resolved_key loc ps) loc' =
     (if loc = loc' then None else map_of ps loc')"
  unfolding remove_resolved_key_eq_delete
  by (simp add: AList.delete_conv')

fun lookup_resolved_st ::
  "('a::bot) resolved_st => location => 'a" where
  "lookup_resolved_st (dl, dg, ps) loc =
     (case map_of ps loc of
        Some a => a
      | None => (case loc of
          Local_Location x => dl
        | Global_Location x => dg))"

definition eq_resolved_st ::
  "('a::bot) resolved_st => 'a resolved_st => bool"
where
  "eq_resolved_st s t \<longleftrightarrow>
     lookup_resolved_st s = lookup_resolved_st t"

lemma equivp_eq_resolved_st: "equivp eq_resolved_st"
  unfolding eq_resolved_st_def
  by (rule equivpI) (auto intro: reflpI sympI transpI)

definition le_resolved_st_code ::
  "('a::order_bot) resolved_st => 'a resolved_st => bool"
where
  "le_resolved_st_code s t =
     (case s of (dl, dg, ps) =>
      case t of (el, eg, qs) =>
        dl <= el \<and> dg <= eg \<and>
        list_all
          (\<lambda>loc. lookup_resolved_st (dl, dg, ps) loc <=
            lookup_resolved_st (el, eg, qs) loc)
          (map fst ps @ map fst qs))"

lemma map_of_resolved_none_iff:
  "map_of ps loc = None \<longleftrightarrow> loc \<notin> set (map fst ps)"
  by (induction ps) auto

lemma fresh_vname_notin:
  "\<exists>x::vname. x \<notin> location_vname ` set (map fst ps @ map fst qs)"
  by (rule ex_new_if_finite[OF infinite_literal]) simp

lemma location_vname_imageI:
  assumes "loc \<in> set xs"
  shows "location_vname loc \<in> location_vname ` set xs"
  by (rule imageI[OF assms])

lemma le_resolved_st_code_raw_iff:
  "le_resolved_st_code (dl, dg, ps) (el, eg, qs) \<longleftrightarrow>
    (\<forall>loc. lookup_resolved_st (dl, dg, ps) loc <=
      lookup_resolved_st (el, eg, qs) loc)"
proof
  assume le: "le_resolved_st_code (dl, dg, ps) (el, eg, qs)"
  have defaults: "dl <= el \<and> dg <= eg"
    using le unfolding le_resolved_st_code_def by simp
  have support:
    "list_all (\<lambda>loc. lookup_resolved_st (dl, dg, ps) loc <=
      lookup_resolved_st (el, eg, qs) loc) (map fst ps @ map fst qs)"
    using le unfolding le_resolved_st_code_def by simp
  show "\<forall>loc. lookup_resolved_st (dl, dg, ps) loc <=
      lookup_resolved_st (el, eg, qs) loc"
  proof
    fix loc
    show "lookup_resolved_st (dl, dg, ps) loc <=
        lookup_resolved_st (el, eg, qs) loc"
    proof (cases "loc \<in> set (map fst ps @ map fst qs)")
      case True
      with support show ?thesis by (simp add: list_all_iff)
    next
      case False
      have ps_none: "map_of ps loc = None"
        using False by (simp add: map_of_resolved_none_iff)
      have qs_none: "map_of qs loc = None"
        using False by (simp add: map_of_resolved_none_iff)
      show ?thesis
        using defaults ps_none qs_none
        by (cases loc) simp_all
    qed
  qed
next
  assume le: "\<forall>loc. lookup_resolved_st (dl, dg, ps) loc <=
      lookup_resolved_st (el, eg, qs) loc"
  obtain x where fresh:
    "x \<notin> location_vname ` set (map fst ps @ map fst qs)"
    using fresh_vname_notin[of ps qs] by blast
  have local_support:
    "Local_Location x \<notin> set (map fst ps @ map fst qs)"
  proof
    assume H: "Local_Location x \<in> set (map fst ps @ map fst qs)"
    have "location_vname (Local_Location x) \<in>
        location_vname ` set (map fst ps @ map fst qs)"
      by (rule location_vname_imageI[OF H])
    with fresh show False by simp
  qed
  have global_support:
    "Global_Location x \<notin> set (map fst ps @ map fst qs)"
  proof
    assume H: "Global_Location x \<in> set (map fst ps @ map fst qs)"
    have "location_vname (Global_Location x) \<in>
        location_vname ` set (map fst ps @ map fst qs)"
      by (rule location_vname_imageI[OF H])
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
  have dl_le: "dl <= el"
    using le[rule_format, of "Local_Location x"] local_ps local_qs by simp
  have dg_le: "dg <= eg"
    using le[rule_format, of "Global_Location x"] global_ps global_qs by simp
  show "le_resolved_st_code (dl, dg, ps) (el, eg, qs)"
    unfolding le_resolved_st_code_def
    using le dl_le dg_le by (simp add: list_all_iff)
qed









quotient_type 'a resolved_st_q =
  "('a::bot) resolved_st" / "eq_resolved_st"
  morphisms rep_resolved_st Abs_resolved_st
  by (rule equivp_eq_resolved_st)

lift_definition lookup_resolved_st_q ::
  "('a::bot) resolved_st_q => location => 'a"
  is lookup_resolved_st
  by (simp add: eq_resolved_st_def)

lemma lookup_Abs_resolved_st_q [simp]:
  "lookup_resolved_st_q (Abs_resolved_st s) loc =
     lookup_resolved_st s loc"
  by transfer simp

lemma Abs_resolved_st_rep_resolved_st [simp]:
  "Abs_resolved_st (rep_resolved_st s) = s"
  by (fact Lifting.Quotient_abs_rep [OF Quotient_resolved_st_q])

lemma lookup_rep_resolved_st_q:
  "lookup_resolved_st_q s loc =
     lookup_resolved_st (rep_resolved_st s) loc"
proof -
  have abs: "s = Abs_resolved_st (rep_resolved_st s)"
    by simp
  have lookup_abs:
    "lookup_resolved_st_q (Abs_resolved_st (rep_resolved_st s)) loc =
       lookup_resolved_st (rep_resolved_st s) loc"
    by (rule lookup_Abs_resolved_st_q)
  show ?thesis
    using abs lookup_abs by simp
qed

lemma resolved_st_q_eq_iff:
  "s = t \<longleftrightarrow>
     lookup_resolved_st_q s = lookup_resolved_st_q t"
  by transfer (simp add: eq_resolved_st_def)







instantiation resolved_st_q :: (bot) bot
begin
definition bot_resolved_st_q ::
  "('a::bot) resolved_st_q"
where
  "bot_resolved_st_q = Abs_resolved_st (bot, bot, [])"
instance ..
end

instantiation resolved_st_q :: (order_bot) ord
begin
lift_definition less_eq_resolved_st_q ::
  "('a::order_bot) resolved_st_q =>
   'a resolved_st_q => bool"
  is le_resolved_st_code
  by (auto simp: le_resolved_st_code_raw_iff eq_resolved_st_def)

definition less_resolved_st_q ::
  "('a::order_bot) resolved_st_q =>
   'a resolved_st_q => bool"
where
  "less_resolved_st_q s t \<longleftrightarrow>
     s \<le> t \<and> \<not> t \<le> s"

instance ..
end


lemma le_resolved_st_q_pointwise:
  fixes s t :: "('a::order_bot) resolved_st_q"
  shows "s \<le> t \<longleftrightarrow>
    (\<forall>loc. lookup_resolved_st_q s loc \<le>
      lookup_resolved_st_q t loc)"
proof -
  have code:
    "(s \<le> t) =
       le_resolved_st_code (rep_resolved_st s) (rep_resolved_st t)"
    by (rule less_eq_resolved_st_q.rep_eq)
  have raw:
    "le_resolved_st_code (rep_resolved_st s) (rep_resolved_st t) \<longleftrightarrow>
       (\<forall>loc. lookup_resolved_st (rep_resolved_st s) loc \<le>
         lookup_resolved_st (rep_resolved_st t) loc)"
  proof -
    obtain dl dg ps where s_rep:
      "rep_resolved_st s = (dl, dg, ps)"
      by (cases "rep_resolved_st s") auto
    obtain el eg qs where t_rep:
      "rep_resolved_st t = (el, eg, qs)"
      by (cases "rep_resolved_st t") auto
    show ?thesis
      unfolding s_rep t_rep
      by (rule le_resolved_st_code_raw_iff)
  qed
  show ?thesis
    using code raw by (simp add: lookup_rep_resolved_st_q)
qed


instance resolved_st_q :: (order_bot) order
proof intro_classes
  fix s t u :: "('a::order_bot) resolved_st_q"
  show "(s < t) \<longleftrightarrow> (s \<le> t \<and> \<not> t \<le> s)"
    by (simp add: less_resolved_st_q_def)

  show "s \<le> s"
    by (simp add: le_resolved_st_q_pointwise)
  show "s \<le> t \<Longrightarrow> t \<le> u \<Longrightarrow> s \<le> u"
    by (auto simp: le_resolved_st_q_pointwise intro: order_trans)
  show "s \<le> t \<Longrightarrow> t \<le> s \<Longrightarrow> s = t"
    by (auto simp: le_resolved_st_q_pointwise
      resolved_st_q_eq_iff fun_eq_iff intro: order_antisym)
qed

lemma le_resolved_st_q_iff:
  "s \<le> t \<longleftrightarrow>
     (\<forall>loc. lookup_resolved_st_q s loc \<le>
       lookup_resolved_st_q t loc)"
  by (simp add: le_resolved_st_q_pointwise)

lemma lookup_bot_resolved_st_q [simp]:
  "lookup_resolved_st_q (bot :: ('a::bot) resolved_st_q) loc = bot"
  unfolding bot_resolved_st_q_def
  by transfer (simp split: location.splits)

instantiation resolved_st_q :: ("{order_bot,equal}") equal
begin
definition equal_resolved_st_q ::
  "('a::{order_bot,equal}) resolved_st_q =>
   'a resolved_st_q => bool"
where
  "equal_resolved_st_q s t = (s \<le> t \<and> t \<le> s)"
instance
  by standard (auto simp: equal_resolved_st_q_def intro: order_antisym)
end

fun update_resolved_st ::
  "('a::bot) resolved_st => location => 'a => 'a resolved_st" where
  "update_resolved_st (dl, dg, ps) loc a =
     (dl, dg, (loc, a) # remove_resolved_key loc ps)"


lemma lookup_resolved_st_update_same [simp]:
  "lookup_resolved_st (update_resolved_st s loc a) loc = a"
  by (cases s) (simp add: map_of_remove_resolved_key)

lemma lookup_resolved_st_update_diff [simp]:
  "loc \<noteq> loc' \<Longrightarrow>
     lookup_resolved_st (update_resolved_st s loc a) loc' =
       lookup_resolved_st s loc'"
  by (cases s) (simp add: map_of_remove_resolved_key)

lemma eq_resolved_st_update:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (update_resolved_st s loc a)
      (update_resolved_st t loc a)"
proof -
  have h: "lookup_resolved_st s = lookup_resolved_st t"
    using assms unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (update_resolved_st s loc a)
      (update_resolved_st t loc a)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc'
    show "lookup_resolved_st (update_resolved_st s loc a) loc' =
        lookup_resolved_st (update_resolved_st t loc a) loc'"
      by (cases "loc = loc'")
         (simp_all add: h[unfolded fun_eq_iff])
  qed  qed

lift_definition update_resolved_st_q ::
  "('a::bot) resolved_st_q => location => 'a => 'a resolved_st_q"
  is update_resolved_st
  by (rule eq_resolved_st_update)

lemma lookup_resolved_st_q_update_same [simp]:
  "lookup_resolved_st_q (update_resolved_st_q s loc a) loc = a"
  by transfer simp

lemma lookup_resolved_st_q_update_diff [simp]:
  "loc \<noteq> loc' \<Longrightarrow>
     lookup_resolved_st_q (update_resolved_st_q s loc a) loc' =
       lookup_resolved_st_q s loc'"
  by transfer simp

definition location_of ::
  "(vname => bool) => vname => location" where
  "location_of gs x =
     (if gs x then Global_Location x else Local_Location x)"

definition fun_of_resolved_st_for ::
  "(vname => bool) => ('a::bot) resolved_st => vname => 'a" where
  "fun_of_resolved_st_for gs s x =
     lookup_resolved_st s (location_of gs x)"

lemma fun_of_resolved_st_for_update:
  "fun_of_resolved_st_for gs
      (update_resolved_st s loc a) x =
     (if location_of gs x = loc then a
      else fun_of_resolved_st_for gs s x)"
  unfolding fun_of_resolved_st_for_def
  by (cases "location_of gs x = loc")
     (simp_all add: lookup_resolved_st_update_diff)

lemma fun_of_resolved_st_for_update_location [simp]:
  "fun_of_resolved_st_for gs
      (update_resolved_st s (location_of gs x) a) =
   (fun_of_resolved_st_for gs s)(x := a)"
proof (rule ext)
  fix y
  show "fun_of_resolved_st_for gs
      (update_resolved_st s (location_of gs x) a) y =
    ((fun_of_resolved_st_for gs s)(x := a)) y"
    unfolding fun_of_resolved_st_for_def    by (cases "x = y"; cases "gs x"; cases "gs y";
        simp_all add: location_of_def)
qed



subsection \<open>Executable witness-bottom detection\<close>

text \<open>
  A finite, executable sufficient condition for @{const is_bot_state} on the state a
  resolved_st represents. Two disjuncts: the local default already bottom (covers
  every unoverridden local); or some explicit override is bottom at a location gs
  itself would actually produce for its own vname (ruling out an override at a
  location no vname under this gs maps to, which would say nothing about
  @{const is_bot_state}). The global default is deliberately not checked: unlike
  locals, a @{term declared_global} classifier's true set is always finite for a
  real program, so no generic (ps-independent) argument can guarantee a fresh
  global escapes any given override list the way a fresh local's existence does;
  only the ps branch can safely observe a global.
\<close>

definition resolved_st_is_bot ::
  "(vname => bool) => ('a::computable_domain) resolved_st => bool" where
  "resolved_st_is_bot gs s =
     (case s of (dl, dg, ps) =>
       is_bot dl \<or>
       (\<exists>loc \<in> set (map fst ps). is_bot (lookup_resolved_st s loc)
          \<and> location_of gs (location_vname loc) = loc))"

text \<open>
  Soundness needs gs to leave infinitely many vnames local, so that some local
  witness always escapes any given (finite) override list -- true for any
  @{term declared_global} of a real program, which only ever declares finitely
  many globals while @{typ vname} is infinite.
\<close>
lemma resolved_st_is_bot_sound:
  assumes bot: "resolved_st_is_bot gs s"
    and infinite_local: "infinite {x. \<not> gs x}"
  shows "is_bot_state (fun_of_resolved_st_for gs s)"
proof -
  obtain dl dg ps where s_eq: "s = (dl, dg, ps)" by (cases s)
  from bot consider
      (dl) "is_bot dl"
    | (ps) loc where "loc \<in> set (map fst ps)" "is_bot (lookup_resolved_st s loc)"
        "location_of gs (location_vname loc) = loc"
    unfolding resolved_st_is_bot_def s_eq by auto
  then show ?thesis
  proof cases
    case dl
    obtain x :: vname where not_gs: "\<not> gs x"
        and fresh: "x \<notin> location_vname ` set (map fst ps)"
      using infinite_local
      by (metis (mono_tags, lifting) finite_surj list.set_finite
          mem_Collect_eq subset_eq)
    have local_ps: "Local_Location x \<notin> set (map fst ps)"
    proof
      assume "Local_Location x \<in> set (map fst ps)"
      then have "location_vname (Local_Location x) \<in> location_vname ` set (map fst ps)"
        by (rule location_vname_imageI)
      with fresh show False by simp
    qed
    have mo_l: "map_of ps (Local_Location x) = None"
      using local_ps by (simp add: map_of_resolved_none_iff)
    have "lookup_resolved_st s (Local_Location x) = dl"
      unfolding s_eq by (simp add: mo_l)
    then have "is_bot (fun_of_resolved_st_for gs s x)"
      unfolding fun_of_resolved_st_for_def location_of_def
      using dl not_gs by simp
    then show ?thesis by (rule is_bot_stateI)
  next
    case ps
    let ?x = "location_vname loc"
    have loc_eq: "location_of gs ?x = loc" by (rule ps(3))
    have "fun_of_resolved_st_for gs s ?x = lookup_resolved_st s loc"
      unfolding fun_of_resolved_st_for_def loc_eq by (rule refl)
    then have "is_bot (fun_of_resolved_st_for gs s ?x)"
      using ps(2) by simp
    then show ?thesis by (rule is_bot_stateI)
  qed
qed

text \<open>
  \<^const>\<open>resolved_st_is_bot\<close> deliberately leaves the global default unchecked
  because an opaque classifier gives no way to enumerate the (finite) globally
  classified vnames. A concrete program's classifier is always backed by an
  explicit finite list (@{term declared_global_vars}), and enumerating exactly
  that list closes the gap: every globally classified vname is checked
  directly, so the global branch needs no override witness. This makes the
  combined check an exact (not merely sound) characterization of
  @{const is_bot_state}, with no side condition on \<open>gs\<close> beyond \<open>globals\<close>
  actually listing its true set -- unlike @{thm resolved_st_is_bot_sound},
  which still needs infinitely many locals to exist.
\<close>

definition resolved_st_is_bot_for ::
  "vname list => (vname => bool) => ('a::computable_domain) resolved_st => bool" where
  "resolved_st_is_bot_for globals gs s =
     ((\<exists>x \<in> set globals. is_bot (lookup_resolved_st s (location_of gs x))) \<or>
      resolved_st_is_bot gs s)"

lemma resolved_st_is_bot_for_iff:
  fixes s :: "'a::sound_domain resolved_st"
  assumes globals: "\<And>x. gs x = (x \<in> set globals)"
  shows "resolved_st_is_bot_for globals gs s \<longleftrightarrow> is_bot_state (fun_of_resolved_st_for gs s)"
proof -
  have infinite_local: "infinite {x::vname. \<not> gs x}"
  proof
    assume fin: "finite {x::vname. \<not> gs x}"
    have "finite (UNIV :: vname set)"
    proof -
      have "(UNIV :: vname set) = {x. \<not> gs x} \<union> set globals" using globals by auto
      then show ?thesis using fin
        by (metis finite_Un list.set_finite)
    qed
    then show False using infinite_literal by simp
  qed
  show ?thesis
  proof
    assume "resolved_st_is_bot_for globals gs s"
    then show "is_bot_state (fun_of_resolved_st_for gs s)"
      unfolding resolved_st_is_bot_for_def
    proof (elim disjE)
      assume "\<exists>x \<in> set globals. is_bot (lookup_resolved_st s (location_of gs x))"
      then obtain x where "is_bot (lookup_resolved_st s (location_of gs x))" by blast
      then have "is_bot (fun_of_resolved_st_for gs s x)"
        unfolding fun_of_resolved_st_for_def by simp
      then show ?thesis by (rule is_bot_stateI)
    next
      assume bot: "resolved_st_is_bot gs s"
      show ?thesis by (rule resolved_st_is_bot_sound[OF bot infinite_local])
    qed
  next
    assume "is_bot_state (fun_of_resolved_st_for gs s)"
    then obtain x where x: "is_bot (fun_of_resolved_st_for gs s x)" by (rule is_bot_stateE)
    show "resolved_st_is_bot_for globals gs s"
    proof (cases "gs x")
      case True
      then have "x \<in> set globals" using globals by simp
      moreover have "fun_of_resolved_st_for gs s x = lookup_resolved_st s (location_of gs x)"
        unfolding fun_of_resolved_st_for_def by (rule refl)
      ultimately have "\<exists>y \<in> set globals. is_bot (lookup_resolved_st s (location_of gs y))"
        using x by auto
      then show ?thesis unfolding resolved_st_is_bot_for_def by (rule disjI1)
    next
      case False
      have loc_eq: "location_of gs x = Local_Location x"
        using False unfolding location_of_def by simp
      have lookup_eq: "lookup_resolved_st s (Local_Location x) = fun_of_resolved_st_for gs s x"
        unfolding fun_of_resolved_st_for_def loc_eq by (rule refl)
      obtain dl dg ps where s_eq: "s = (dl, dg, ps)" by (cases s)
      have "resolved_st_is_bot gs s"
      proof (cases "Local_Location x \<in> set (map fst ps)")
        case True
        have loc_vname_eq: "location_of gs (location_vname (Local_Location x)) = Local_Location x"
          using loc_eq by simp
        show ?thesis
          unfolding resolved_st_is_bot_def
          using True lookup_eq x loc_vname_eq s_eq
          by (metis (mono_tags, lifting) case_prod_conv)
      next
        case False
        then have mo: "map_of ps (Local_Location x) = None"
          by (simp add: map_of_resolved_none_iff)
        have "lookup_resolved_st s (Local_Location x) = dl"
          unfolding s_eq using mo by simp
        with lookup_eq x have "is_bot dl" by simp
        then show ?thesis
          unfolding resolved_st_is_bot_def using s_eq by auto
      qed
      then show ?thesis unfolding resolved_st_is_bot_for_def by (rule disjI2)
    qed
  qed
qed


fun location_is_local :: "location => bool" where
  "location_is_local (Local_Location x) = True"
| "location_is_local (Global_Location x) = False"

fun location_is_global :: "location => bool" where
  "location_is_global (Local_Location x) = False"
| "location_is_global (Global_Location x) = True"

definition restrict_local_resolved ::
  "('a::bot) resolved_st => 'a resolved_st" where
  "restrict_local_resolved s =
     (case s of (dl, dg, ps) =>
       (dl, bot, filter (%p. location_is_local (fst p)) ps))"

definition restrict_global_resolved ::
  "('a::bot) resolved_st => 'a resolved_st" where
  "restrict_global_resolved s =
     (case s of (dl, dg, ps) =>
       (bot, dg, filter (%p. location_is_global (fst p)) ps))"


definition combine_resolved_st ::
  "('a::bot) resolved_st => 'a resolved_st => 'a resolved_st"
where
  "combine_resolved_st sc se =
     (case sc of (dlc, dgc, psc) =>
      case se of (dle, dge, pse) =>
        (dlc, dge,
         filter (%p. location_is_local (fst p)) psc @
         filter (%p. location_is_global (fst p)) pse))"

definition enter_frame_D_resolved ::
  "'a => ('a::bot) resolved_st => 'a resolved_st"
where
  "enter_frame_D_resolved top_val s =
     (case s of (dl, dg, ps) =>
       (top_val, dg, filter (%p. location_is_global (fst p)) ps))"

definition combine_assign_resolved ::
  "(vname => bool) => vname option => 'a => ('a::bot) resolved_st
   => 'a resolved_st"
where
  "combine_assign_resolved gs dst v s =
     (case dst of None => s
      | Some x => update_resolved_st s (location_of gs x) v)"

lemma eq_resolved_st_combine_assign:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (combine_assign_resolved gs dst v s)
      (combine_assign_resolved gs dst v t)"
  by (unfold combine_assign_resolved_def; cases dst;
      simp_all add: assms eq_resolved_st_update)

lift_definition combine_assign_resolved_q ::
  "(vname => bool) => vname option => 'a => ('a::bot) resolved_st_q
   => 'a resolved_st_q"
  is combine_assign_resolved
  by (rule eq_resolved_st_combine_assign)

lemma lookup_combine_assign_resolved_q [simp]:
  "lookup_resolved_st_q (combine_assign_resolved_q gs dst v s) loc =
     (case dst of
        None => lookup_resolved_st_q s loc
      | Some x =>
          if location_of gs x = loc then v
          else lookup_resolved_st_q s loc)"
  by transfer (auto simp add:combine_assign_resolved_def split:option.splits)
 
definition bind_formals_resolved ::
  "(vname => bool) => vname list => 'a list => ('a::bot) resolved_st
   => 'a resolved_st"
where
  "bind_formals_resolved gs xs avs s =
     fold (%(x, a) t. update_resolved_st t (location_of gs x) a)
       (zip xs avs) s"

lemma eq_resolved_st_fold_update:
  "eq_resolved_st s t \<Longrightarrow>
     eq_resolved_st
       (fold (%(x, a) t. update_resolved_st t (location_of gs x) a) ps s)
       (fold (%(x, a) t. update_resolved_st t (location_of gs x) a) ps t)"
proof (induction ps arbitrary: s t)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case
    by (cases p) (simp_all add: eq_resolved_st_update)
qed

lemma eq_resolved_st_bind_formals:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (bind_formals_resolved gs xs avs s)
      (bind_formals_resolved gs xs avs t)"
  unfolding bind_formals_resolved_def
  using assms by (rule eq_resolved_st_fold_update)

lift_definition bind_formals_resolved_q ::
  "(vname => bool) => vname list => 'a list => ('a::bot) resolved_st_q
   => 'a resolved_st_q"
  is bind_formals_resolved
  by (rule eq_resolved_st_bind_formals)

text \<open>A single-formal call binds exactly one location, so its reduction is a
  plain \<^const>\<open>update_resolved_st_q\<close>. Every placement instance with a
  one-argument procedure call cites this directly instead of unfolding
  \<^const>\<open>bind_formals_resolved_q\<close>'s fold.\<close>

lemma bind_formals_resolved_q_singleton:
  "bind_formals_resolved_q gs [x] [a] s = update_resolved_st_q s (location_of gs x) a"
  by transfer (simp add: bind_formals_resolved_def eq_resolved_st_def)

definition enter_resolved_for ::
  "(vname => bool) => 'a => (exp => 'a abs_state => 'a)
   => vname list => exp list => ('a::bot) resolved_st => 'a resolved_st"
where
  "enter_resolved_for gs top_val aval_abs xs es s =
     bind_formals_resolved gs xs
       (map (%e. aval_abs e (fun_of_resolved_st_for gs s)) es)
       (enter_frame_D_resolved top_val s)"

definition combine_collect_resolved_for ::
  "(vname => bool) => vname option => ('a::bot) resolved_st
   => 'a resolved_st => 'a resolved_st"
where
  "combine_collect_resolved_for gs dst sc se =
     combine_assign_resolved gs dst
       (lookup_resolved_st se (location_of gs ret_var))
       (combine_resolved_st sc se)"





lemma map_of_filter_key:
  "map_of (filter (\<lambda>(k, _). P k) xs) k = (if P k then map_of xs k else None)"
  by (induction xs) auto

lemma filter_fst_eq_restrict:
  fixes P :: "location => bool"
  shows "filter (%p. P (fst p)) xs = AList.restrict {k. P k} xs"
  unfolding AList.restrict_eq
  by (induction xs) auto

lemma map_of_filter_fst:
  fixes P :: "location => bool"
    and xs :: "(location \<times> 'a) list"
    and k :: location
  shows "map_of (filter (%p. P (fst p)) xs) k =
     (if P k then map_of xs k else None)"
  by (simp add: filter_fst_eq_restrict AList.restr_conv')

lemma map_of_filter_global_local:
  "map_of (filter (%p. location_is_global (fst p)) ps)
      (Local_Location x) = None"
  by (simp add: map_of_filter_fst)

lemma map_of_filter_local_global:
  "map_of (filter (%p. location_is_local (fst p)) ps)
      (Global_Location x) = None"
  by (simp add: map_of_filter_fst)

lemma map_of_filter_local_local:
  "map_of (filter (%p. location_is_local (fst p)) ps)
      (Local_Location x) =
     map_of ps (Local_Location x)"
  by (simp add: map_of_filter_fst)

lemma map_of_filter_global_global:
  "map_of (filter (%p. location_is_global (fst p)) ps)
      (Global_Location x) =
     map_of ps (Global_Location x)"
  by (simp add: map_of_filter_fst)

lemma lookup_combine_resolved_st [simp]:
  "lookup_resolved_st (combine_resolved_st sc se) loc =
   (case loc of
      Local_Location x => lookup_resolved_st sc loc
    | Global_Location x => lookup_resolved_st se loc)"
by (cases sc; cases se; cases loc)
     (simp_all add: combine_resolved_st_def map_add_def
       map_of_filter_global_local map_of_filter_local_local
       map_of_filter_global_global map_of_filter_local_global
       split: option.splits)

lemma eq_resolved_st_combine:
  assumes "eq_resolved_st sc1 sc2"
    and "eq_resolved_st se1 se2"
  shows "eq_resolved_st (combine_resolved_st sc1 se1)
      (combine_resolved_st sc2 se2)"
proof -
  have hc: "lookup_resolved_st sc1 = lookup_resolved_st sc2"
    using assms(1) unfolding eq_resolved_st_def by simp
  have he: "lookup_resolved_st se1 = lookup_resolved_st se2"
    using assms(2) unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (combine_resolved_st sc1 se1)
      (combine_resolved_st sc2 se2)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    show "lookup_resolved_st (combine_resolved_st sc1 se1) loc =
        lookup_resolved_st (combine_resolved_st sc2 se2) loc"
      by (cases loc)
         (simp_all add: lookup_combine_resolved_st
           hc[unfolded fun_eq_iff] he[unfolded fun_eq_iff])
  qed
qed

lemma eq_resolved_st_combine_collect:
  assumes "eq_resolved_st sc1 sc2"
    and "eq_resolved_st se1 se2"
  shows "eq_resolved_st
      (combine_collect_resolved_for gs dst sc1 se1)
      (combine_collect_resolved_for gs dst sc2 se2)"
  unfolding combine_collect_resolved_for_def eq_resolved_st_def
  using assms
  by (metis eq_resolved_st_combine eq_resolved_st_combine_assign
      eq_resolved_st_def)

lift_definition combine_collect_resolved_for_q ::
  "(vname => bool) => vname option => ('a::bot) resolved_st_q
   => 'a resolved_st_q => 'a resolved_st_q"
  is combine_collect_resolved_for
  by (rule eq_resolved_st_combine_collect)


lift_definition combine_resolved_st_q ::
  "('a::bot) resolved_st_q => 'a resolved_st_q => 'a resolved_st_q"
  is combine_resolved_st
  by (rule eq_resolved_st_combine)

lemma lookup_combine_resolved_st_q [simp]:
  "lookup_resolved_st_q (combine_resolved_st_q sc se) loc =
     (case loc of
        Local_Location x => lookup_resolved_st_q sc loc
      | Global_Location x => lookup_resolved_st_q se loc)"
  by transfer (rule lookup_combine_resolved_st)

text \<open>
  \<^const>\<open>map_of\<close> over an append is already characterized by
  \<^theory>\<open>HOL.Map\<close>'s @{thm [source] map_of_append}, so no bespoke append lemma
  is needed here.
\<close>

lemma map_of_eq_None_map_fst:
  "x \<notin> set (map fst ps) \<Longrightarrow> map_of ps x = None"
  by (simp add: Map.map_of_eq_None_iff)

fun merge_resolved_st ::
  "('a::bounded_semilattice_sup_bot) resolved_st =>
   'a resolved_st => 'a resolved_st"
where
  "merge_resolved_st (dl1, dg1, ps1) (dl2, dg2, ps2) =
     (dl1 \<squnion> dl2, dg1 \<squnion> dg2,
      map (%(loc, _). (loc,
        lookup_resolved_st (dl1, dg1, ps1) loc \<squnion>
        lookup_resolved_st (dl2, dg2, ps2) loc))
        (ps1 @ ps2))"

lemma map_of_map_fst_lookup:
  "map_of (map (%(loc, _). (loc, f loc)) ps) x =
     (case map_of ps x of None => None | Some a => Some (f x))"
  by (induction ps) (auto split: option.splits)

lemma map_of_map_fst_lookup_append:
  fixes ps1 ps2 :: "(location \<times> 'a) list"
    and f :: "location => 'b"
  shows
    "map_of (map (%(loc, _). (loc, f loc)) (ps1 @ ps2)) x =
     (case map_of ps1 x of
        Some a => Some (f x)
      | None =>
          (case map_of ps2 x of
             Some a => Some (f x)
           | None => None))"
  by (induction ps1)
     (auto simp add: map_of_map_fst_lookup split: option.splits)

lemma lookup_merge_resolved_st [simp]:
  "lookup_resolved_st (merge_resolved_st s t) loc =
     lookup_resolved_st s loc \<squnion> lookup_resolved_st t loc"
  by (cases s; cases t; cases loc)
     (auto simp add: map_add_def map_of_map_fst_lookup_append
       map_of_map_fst_lookup
       split: option.splits if_splits)

lemma eq_resolved_st_merge:
  assumes "eq_resolved_st s1 s2"
    and "eq_resolved_st t1 t2"
  shows "eq_resolved_st (merge_resolved_st s1 t1)
      (merge_resolved_st s2 t2)"
proof -
  have hs: "lookup_resolved_st s1 = lookup_resolved_st s2"
    using assms(1) unfolding eq_resolved_st_def by simp
  have ht: "lookup_resolved_st t1 = lookup_resolved_st t2"
    using assms(2) unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (merge_resolved_st s1 t1)
      (merge_resolved_st s2 t2)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    show "lookup_resolved_st (merge_resolved_st s1 t1) loc =
        lookup_resolved_st (merge_resolved_st s2 t2) loc"
      by (simp add: lookup_merge_resolved_st
        hs[unfolded fun_eq_iff] ht[unfolded fun_eq_iff])
  qed
qed

instantiation resolved_st_q ::
  (bounded_semilattice_sup_bot) sup
begin
lift_definition sup_resolved_st_q ::
  "('a::bounded_semilattice_sup_bot) resolved_st_q =>
   'a resolved_st_q => 'a resolved_st_q"
  is merge_resolved_st
  by (rule eq_resolved_st_merge)
instance ..
end

lemma lookup_sup_resolved_st_q [simp]:
  "lookup_resolved_st_q (s \<squnion> t) loc =
     lookup_resolved_st_q s loc \<squnion> lookup_resolved_st_q t loc"
  by transfer (rule lookup_merge_resolved_st)

lemma bot_le_resolved_st_q:
  "(bot :: ('a::order_bot) resolved_st_q) \<le> s"
  by (simp add: le_resolved_st_q_iff)

fun widen_resolved_st ::
  "('a::bounded_warrowing) resolved_st =>
   'a resolved_st => 'a resolved_st"
where
  "widen_resolved_st (dl1, dg1, ps1) (dl2, dg2, ps2) =
     (dl1 \<nabla> dl2, dg1 \<nabla> dg2,
      map (%(loc, _). (loc,
        lookup_resolved_st (dl1, dg1, ps1) loc \<nabla>
        lookup_resolved_st (dl2, dg2, ps2) loc))
        (ps1 @ ps2))"

lemma lookup_widen_resolved_st [simp]:
  "lookup_resolved_st (widen_resolved_st s t) loc =
     lookup_resolved_st s loc \<nabla> lookup_resolved_st t loc"
  by (cases s; cases t; cases loc)
     (auto simp add: map_add_def map_of_map_fst_lookup_append
      map_of_map_fst_lookup
       split: option.splits if_splits)

lemma eq_resolved_st_widen:
  assumes "eq_resolved_st s1 s2"
    and "eq_resolved_st t1 t2"
  shows "eq_resolved_st (widen_resolved_st s1 t1)
      (widen_resolved_st s2 t2)"
proof -
  have hs: "lookup_resolved_st s1 = lookup_resolved_st s2"
    using assms(1) unfolding eq_resolved_st_def by simp
  have ht: "lookup_resolved_st t1 = lookup_resolved_st t2"
    using assms(2) unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (widen_resolved_st s1 t1)
      (widen_resolved_st s2 t2)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    show "lookup_resolved_st (widen_resolved_st s1 t1) loc =
        lookup_resolved_st (widen_resolved_st s2 t2) loc"
      by (simp add: hs[unfolded fun_eq_iff] ht[unfolded fun_eq_iff])
  qed
qed

lift_definition widen_on_resolved_st_q ::
  "('a::bounded_warrowing) resolved_st_q =>
   'a resolved_st_q => 'a resolved_st_q"
  is widen_resolved_st
  by (rule eq_resolved_st_widen)

lemma lookup_widen_on_resolved_st_q [simp]:
  "lookup_resolved_st_q (widen_on_resolved_st_q s t) loc =
     lookup_resolved_st_q s loc \<nabla> lookup_resolved_st_q t loc"
  by transfer (rule lookup_widen_resolved_st)

instantiation resolved_st_q :: (bounded_warrowing) widening
begin
definition widen_resolved_st_q ::
  "('a::bounded_warrowing) resolved_st_q =>
   'a resolved_st_q => 'a resolved_st_q"
where
  "widen_resolved_st_q s t = widen_on_resolved_st_q s t"
instance
proof
  fix a b :: "('a::bounded_warrowing) resolved_st_q"
  show "a \<le> widen a b"
    by (simp add: le_resolved_st_q_iff widen_resolved_st_q_def widen_ge1)
  show "b \<le> widen a b"
    by (simp add: le_resolved_st_q_iff widen_resolved_st_q_def widen_ge2)
qed
end

lemma lookup_widen_resolved_st_q [simp]:
  "lookup_resolved_st_q (s \<nabla> t) loc =
     lookup_resolved_st_q s loc \<nabla> lookup_resolved_st_q t loc"
  by (simp add: widen_resolved_st_q_def)

fun narrow_resolved_st ::
  "('a::bounded_warrowing) resolved_st =>
   'a resolved_st => 'a resolved_st"
where
  "narrow_resolved_st (dl1, dg1, ps1) (dl2, dg2, ps2) =
     (dl1 \<Delta> dl2, dg1 \<Delta> dg2,
      map (%(loc, _). (loc,
        lookup_resolved_st (dl1, dg1, ps1) loc \<Delta>
        lookup_resolved_st (dl2, dg2, ps2) loc))
        (ps1 @ ps2))"

lemma lookup_narrow_resolved_st [simp]:
  "lookup_resolved_st (narrow_resolved_st s t) loc =
     lookup_resolved_st s loc \<Delta> lookup_resolved_st t loc"
  by (cases s; cases t; cases loc)
     (auto simp add: map_add_def map_of_map_fst_lookup_append
      map_of_map_fst_lookup
       split: option.splits if_splits)

lemma eq_resolved_st_narrow:
  assumes "eq_resolved_st s1 s2"
    and "eq_resolved_st t1 t2"
  shows "eq_resolved_st (narrow_resolved_st s1 t1)
      (narrow_resolved_st s2 t2)"
proof -
  have hs: "lookup_resolved_st s1 = lookup_resolved_st s2"
    using assms(1) unfolding eq_resolved_st_def by simp
  have ht: "lookup_resolved_st t1 = lookup_resolved_st t2"
    using assms(2) unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (narrow_resolved_st s1 t1)
      (narrow_resolved_st s2 t2)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    show "lookup_resolved_st (narrow_resolved_st s1 t1) loc =
        lookup_resolved_st (narrow_resolved_st s2 t2) loc"
      by (simp add: hs[unfolded fun_eq_iff] ht[unfolded fun_eq_iff])
  qed
qed

lift_definition narrow_on_resolved_st_q ::
  "('a::bounded_warrowing) resolved_st_q =>
   'a resolved_st_q => 'a resolved_st_q"
  is narrow_resolved_st
  by (rule eq_resolved_st_narrow)

lemma lookup_narrow_on_resolved_st_q [simp]:
  "lookup_resolved_st_q (narrow_on_resolved_st_q s t) loc =
     lookup_resolved_st_q s loc \<Delta> lookup_resolved_st_q t loc"
  by transfer (rule lookup_narrow_resolved_st)

instantiation resolved_st_q :: (bounded_warrowing) narrowing
begin
definition narrow_resolved_st_q ::
  "('a::bounded_warrowing) resolved_st_q =>
   'a resolved_st_q => 'a resolved_st_q"
where
  "narrow_resolved_st_q s t = narrow_on_resolved_st_q s t"
instance
  by standard
     (auto simp add: le_resolved_st_q_iff narrow_resolved_st_q_def
       intro: narrow_ge narrow_le)
end

instance resolved_st_q :: (bounded_warrowing) warrowing ..



instance resolved_st_q :: (order_bot) order_bot
  by standard (rule bot_le_resolved_st_q)

instance resolved_st_q ::
  (bounded_semilattice_sup_bot) semilattice_sup
proof intro_classes
  fix s t u :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  show "s \<le> s \<squnion> t"
    by (simp add: le_resolved_st_q_iff)
  show "t \<le> s \<squnion> t"
    by (simp add: le_resolved_st_q_iff)
  show "s \<le> u \<Longrightarrow> t \<le> u \<Longrightarrow> s \<squnion> t \<le> u"
    by (simp add: le_resolved_st_q_iff)
qed

instance resolved_st_q ::
  (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

instance resolved_st_q :: (bounded_warrowing) bounded_warrowing ..



lemma fun_of_resolved_st_for_combine_resolved [simp]:
  "fun_of_resolved_st_for gs (combine_resolved_st sc se) =
   combine_env gs (fun_of_resolved_st_for gs sc)
     (fun_of_resolved_st_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_for gs (combine_resolved_st sc se) x =
      combine_env gs (fun_of_resolved_st_for gs sc)
        (fun_of_resolved_st_for gs se) x"
    unfolding fun_of_resolved_st_for_def combine_env_def location_of_def
    by (cases "gs x") simp_all
qed

lemma lookup_enter_frame_D_resolved [simp]:
  "lookup_resolved_st (enter_frame_D_resolved top_val s) loc =
   (case loc of
      Local_Location x => top_val
    | Global_Location x => lookup_resolved_st s loc)"
by (cases s; cases loc)
     (simp_all add: enter_frame_D_resolved_def
       map_of_filter_global_local map_of_filter_global_global
       split: option.splits)

lemma eq_resolved_st_enter_frame_D:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (enter_frame_D_resolved top_val s)
      (enter_frame_D_resolved top_val t)"
proof -
  have h: "lookup_resolved_st s = lookup_resolved_st t"
    using assms unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (enter_frame_D_resolved top_val s)
      (enter_frame_D_resolved top_val t)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    show "lookup_resolved_st (enter_frame_D_resolved top_val s) loc =
        lookup_resolved_st (enter_frame_D_resolved top_val t) loc"
      by (cases loc)
         (simp_all add: lookup_enter_frame_D_resolved
           h[unfolded fun_eq_iff])
  qed
qed

lift_definition enter_frame_D_resolved_q ::
  "'a => ('a::bot) resolved_st_q => 'a resolved_st_q"
  is enter_frame_D_resolved
  by (rule eq_resolved_st_enter_frame_D)

lemma lookup_enter_frame_D_resolved_q [simp]:
  "lookup_resolved_st_q (enter_frame_D_resolved_q top_val s) loc =
     (case loc of
        Local_Location x => top_val
      | Global_Location x => lookup_resolved_st_q s loc)"
  by transfer (rule lookup_enter_frame_D_resolved)

lemma eq_resolved_st_enter_resolved_for:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st
      (enter_resolved_for gs top_val aval_abs xs es s)
      (enter_resolved_for gs top_val aval_abs xs es t)"
proof -
  have hlookup: "lookup_resolved_st s = lookup_resolved_st t"
    using assms unfolding eq_resolved_st_def by simp
  have hfun: "fun_of_resolved_st_for gs s =
      fun_of_resolved_st_for gs t"
    unfolding fun_of_resolved_st_for_def
    by (simp add: hlookup)
  have hargs:
      "map (%e. aval_abs e (fun_of_resolved_st_for gs s)) es =
       map (%e. aval_abs e (fun_of_resolved_st_for gs t)) es"
    by (simp add: hfun)
  show "eq_resolved_st
      (enter_resolved_for gs top_val aval_abs xs es s)
      (enter_resolved_for gs top_val aval_abs xs es t)"
    unfolding enter_resolved_for_def
    by (simp only: hargs;
        rule eq_resolved_st_bind_formals;
        rule eq_resolved_st_enter_frame_D;
        rule assms)
qed

lift_definition enter_resolved_for_q ::
  "(vname => bool) => 'a => (exp => 'a abs_state => 'a)
   => vname list => exp list => ('a::bot) resolved_st_q
   => 'a resolved_st_q"
  is enter_resolved_for
  by (rule eq_resolved_st_enter_resolved_for)

lemma fun_of_st_enter_frame_D_resolved [simp]:
  "fun_of_resolved_st_for gs (enter_frame_D_resolved top_val s) =
   enter_frame gs top_val (fun_of_resolved_st_for gs s)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_for gs (enter_frame_D_resolved top_val s) x =
      enter_frame gs top_val (fun_of_resolved_st_for gs s) x"
    unfolding enter_frame_def fun_of_resolved_st_for_def location_of_def
    by (cases "gs x") simp_all
qed

lemma fun_of_resolved_st_for_combine_assign [simp]:
  "fun_of_resolved_st_for gs
      (combine_assign_resolved gs dst v s) =
   combine_assign dst v (fun_of_resolved_st_for gs s)"
by (cases dst)
   (simp_all add: combine_assign_resolved_def)

lemma fun_of_resolved_st_for_fold_update:
  "fun_of_resolved_st_for gs
      (fold (%(x, a) t. update_resolved_st t (location_of gs x) a) ps s) =
   fold (%(x, a) t. t(x := a)) ps
      (fun_of_resolved_st_for gs s)"
by (induction ps arbitrary: s)
   (simp_all split: prod.splits)

lemma fun_of_resolved_st_for_bind_formals [simp]:
  "fun_of_resolved_st_for gs
      (bind_formals_resolved gs xs avs s) =
   bind_formals xs avs (fun_of_resolved_st_for gs s)"
unfolding bind_formals_resolved_def
by (rule fun_of_resolved_st_for_fold_update)

lemma fun_of_resolved_st_for_enter_resolved [simp]:
  "fun_of_resolved_st_for gs
      (enter_resolved_for gs top_val aval_abs xs es s) =
   enter_D gs top_val aval_abs xs es (fun_of_resolved_st_for gs s)"
unfolding enter_resolved_for_def enter_D_def
by simp

lemma fun_of_resolved_st_for_combine_collect [simp]:
  "fun_of_resolved_st_for gs
      (combine_collect_resolved_for gs dst sc se) =
   combine\<^sup># gs dst
      (fun_of_resolved_st_for gs sc) (fun_of_resolved_st_for gs se)"
unfolding combine_collect_resolved_for_def combine_collect_abs_def
by (simp add: fun_of_resolved_st_for_def)



lemma lookup_restrict_local_resolved:
  "lookup_resolved_st (restrict_local_resolved s) loc =
     (case loc of
        Local_Location x => lookup_resolved_st s loc
      | Global_Location x => bot)"
  by (cases s; cases loc)
     (simp_all add: restrict_local_resolved_def map_of_filter_fst
       split: location.splits option.splits)

lemma lookup_restrict_global_resolved:
  "lookup_resolved_st (restrict_global_resolved s) loc =
     (case loc of
        Local_Location x => bot
      | Global_Location x => lookup_resolved_st s loc)"
  by (cases s; cases loc)
     (simp_all add: restrict_global_resolved_def map_of_filter_fst
       split: location.splits option.splits)

lemma eq_resolved_st_restrict_local:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (restrict_local_resolved s)
      (restrict_local_resolved t)"
proof -
  have h: "lookup_resolved_st s = lookup_resolved_st t"
    using assms unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (restrict_local_resolved s)
      (restrict_local_resolved t)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    show "lookup_resolved_st (restrict_local_resolved s) loc =
        lookup_resolved_st (restrict_local_resolved t) loc"
      by (cases loc)
         (simp_all add: lookup_restrict_local_resolved h[unfolded fun_eq_iff])
  qed
qed

lemma eq_resolved_st_restrict_global:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (restrict_global_resolved s)
      (restrict_global_resolved t)"
proof -
  have h: "lookup_resolved_st s = lookup_resolved_st t"
    using assms unfolding eq_resolved_st_def by simp
  show "eq_resolved_st (restrict_global_resolved s)
      (restrict_global_resolved t)"
    unfolding eq_resolved_st_def
  proof (rule ext)
    fix loc
    show "lookup_resolved_st (restrict_global_resolved s) loc =
        lookup_resolved_st (restrict_global_resolved t) loc"
      by (cases loc)
         (simp_all add: lookup_restrict_global_resolved h[unfolded fun_eq_iff])
  qed
qed

lift_definition restrict_local_resolved_q ::
  "('a::bot) resolved_st_q => 'a resolved_st_q"
  is restrict_local_resolved
  by (rule eq_resolved_st_restrict_local)

lift_definition restrict_global_resolved_q ::
  "('a::bot) resolved_st_q => 'a resolved_st_q"
  is restrict_global_resolved
  by (rule eq_resolved_st_restrict_global)

text \<open>
  \<^const>\<open>restrict_local_resolved_q\<close>/\<^const>\<open>restrict_global_resolved_q\<close>
  preserve the caller's semantic default over the (potentially infinite)
  location space: the kept side carries over its input's own per-location
  default verbatim (\<^term>\<open>dl\<close>/\<^term>\<open>dg\<close>, which need not be \<^term>\<open>bot\<close>), and
  only the dropped side is forced to \<^term>\<open>bot\<close>. The scope-parametric
  \<open>project_resolved_on\<close> family is not a generalization of this pair: it
  optimizes for a different invariant, a bounded materialized support, and
  the two disagree outside that bound. See the comparison note at
  \<open>project_resolved_on\<close>'s own definition for the argument and a
  counterexample; both constructions stay, permanently.
\<close>

lemma lookup_restrict_local_resolved_q [simp]:
  "lookup_resolved_st_q (restrict_local_resolved_q s) loc =
     (case loc of
        Local_Location x => lookup_resolved_st_q s loc
      | Global_Location x => bot)"
  by transfer (rule lookup_restrict_local_resolved)

lemma lookup_restrict_global_resolved_q [simp]:
  "lookup_resolved_st_q (restrict_global_resolved_q s) loc =
     (case loc of
        Local_Location x => bot
      | Global_Location x => lookup_resolved_st_q s loc)"
  by transfer (rule lookup_restrict_global_resolved)

lemma fun_of_resolved_st_for_restrict_local:
  "fun_of_resolved_st_for gs (restrict_local_resolved s) x =
     (if gs x then bot else fun_of_resolved_st_for gs s x)"
  unfolding fun_of_resolved_st_for_def location_of_def
  by (simp add: lookup_restrict_local_resolved)

lemma fun_of_resolved_st_for_restrict_global:
  "fun_of_resolved_st_for gs (restrict_global_resolved s) x =
     (if gs x then fun_of_resolved_st_for gs s x else bot)"
  unfolding fun_of_resolved_st_for_def location_of_def
  by (simp add: lookup_restrict_global_resolved)


definition resolved_st_refines_for ::
  "(vname => bool) => ('a::bot) resolved_st => 'a abs_state => bool"
where
  "resolved_st_refines_for gs s sigma =
     (fun_of_resolved_st_for gs s = sigma)"

locale resolved_st_refinement =
  fixes gs :: "vname => bool"
begin

lemma refines_update:
  assumes "resolved_st_refines_for gs s sigma"
  shows "resolved_st_refines_for gs
      (update_resolved_st s (location_of gs x) a) (sigma(x := a))"
  using assms
  unfolding resolved_st_refines_for_def
  by simp

lemma refines_restrict_local:
  assumes "resolved_st_refines_for gs s sigma"
  shows "resolved_st_refines_for gs (restrict_local_resolved s)
      (%x. if gs x then bot else sigma x)"
  using assms
  unfolding resolved_st_refines_for_def
  by (simp add: fun_eq_iff fun_of_resolved_st_for_restrict_local)

lemma refines_restrict_global:
  assumes "resolved_st_refines_for gs s sigma"
  shows "resolved_st_refines_for gs (restrict_global_resolved s)
      (%x. if gs x then sigma x else bot)"
  using assms
  unfolding resolved_st_refines_for_def
  by (simp add: fun_eq_iff fun_of_resolved_st_for_restrict_global)

lemma refines_combine:
  assumes sc: "resolved_st_refines_for gs sc sigma_c"
    and se: "resolved_st_refines_for gs se sigma_e"
  shows "resolved_st_refines_for gs (combine_resolved_st sc se)
      (combine_env gs sigma_c sigma_e)"
  using sc se
  unfolding resolved_st_refines_for_def
  by simp

lemma refines_enter:
  assumes "resolved_st_refines_for gs s sigma"
  shows "resolved_st_refines_for gs
      (enter_resolved_for gs top_val aval_abs xs es s)
      (enter_D gs top_val aval_abs xs es sigma)"
  using assms
  unfolding resolved_st_refines_for_def
  by simp

lemma refines_combine_collect:
  assumes sc: "resolved_st_refines_for gs sc sigma_c"
    and se: "resolved_st_refines_for gs se sigma_e"
  shows "resolved_st_refines_for gs
      (combine_collect_resolved_for gs dst sc se)
      (combine\<^sup># gs dst sigma_c sigma_e)"
  using sc se
  unfolding resolved_st_refines_for_def
  by simp

end

definition fun_of_resolved_st_q_for ::
  "(vname => bool) => ('a::bot) resolved_st_q => vname => 'a"
where
  "fun_of_resolved_st_q_for gs s x =
     lookup_resolved_st_q s (location_of gs x)"


lemma fun_of_resolved_st_q_for_bot [simp]:
  "fun_of_resolved_st_q_for gs (bot :: ('a::order_bot) resolved_st_q) = bot"
  by (rule ext) (simp add: fun_of_resolved_st_q_for_def)

text \<open>
  The quotient-level projection agrees with the raw one at \<open>s\<close>'s own chosen
  representative -- so any raw-level fact about @{const fun_of_resolved_st_for}
  transports directly to @{const fun_of_resolved_st_q_for} through
  @{const rep_resolved_st}, with no separate quotient-respectfulness argument
  needed: @{const rep_resolved_st} is a genuine function of \<open>s\<close>, so anything
  defined through it is automatically well-defined on the quotient.
\<close>

lemma fun_of_resolved_st_q_for_rep:
  "fun_of_resolved_st_q_for gs s = fun_of_resolved_st_for gs (rep_resolved_st s)"
  unfolding fun_of_resolved_st_q_for_def fun_of_resolved_st_for_def
  by (rule ext) (simp add: lookup_rep_resolved_st_q)

text \<open>
  Defaults are themselves an eq_resolved_st invariant: any resolved_st extensionally
  equal to \<open>s\<close> agrees with \<open>s\<close>'s own defaults, witnessed by a location the finite
  override lists of both representatives leave untouched.
\<close>
lemma eq_resolved_st_defaults:
  assumes "eq_resolved_st (dl, dg, ps) (dl', dg', qs)"
  shows "dl = dl'" and "dg = dg'"
proof -
  obtain x :: vname where fresh: "x \<notin> location_vname ` set (map fst ps @ map fst qs)"
    using fresh_vname_notin[of ps qs] by auto
  have local_notin: "Local_Location x \<notin> set (map fst ps @ map fst qs)"
  proof
    assume "Local_Location x \<in> set (map fst ps @ map fst qs)"
    then have "location_vname (Local_Location x) \<in> location_vname ` set (map fst ps @ map fst qs)"
      by (rule location_vname_imageI)
    with fresh show False by simp
  qed
  have global_notin: "Global_Location x \<notin> set (map fst ps @ map fst qs)"
  proof
    assume "Global_Location x \<in> set (map fst ps @ map fst qs)"
    then have "location_vname (Global_Location x) \<in> location_vname ` set (map fst ps @ map fst qs)"
      by (rule location_vname_imageI)
    with fresh show False by simp
  qed
  have lookup_eq: "lookup_resolved_st (dl, dg, ps) = lookup_resolved_st (dl', dg', qs)"
    using assms unfolding eq_resolved_st_def by simp
  have local_split: "Local_Location x \<notin> set (map fst ps)" "Local_Location x \<notin> set (map fst qs)"
    using local_notin by auto
  have global_split: "Global_Location x \<notin> set (map fst ps)" "Global_Location x \<notin> set (map fst qs)"
    using global_notin by auto
  have dl_pointwise: "lookup_resolved_st (dl, dg, ps) (Local_Location x)
      = lookup_resolved_st (dl', dg', qs) (Local_Location x)"
    using lookup_eq by (rule fun_cong)
  have mo_l_ps: "map_of ps (Local_Location x) = None"
    using local_split(1) by (simp add: map_of_resolved_none_iff)
  have mo_l_qs: "map_of qs (Local_Location x) = None"
    using local_split(2) by (simp add: map_of_resolved_none_iff)
  show "dl = dl'"
    using dl_pointwise by (simp add: mo_l_ps mo_l_qs)
  have dg_pointwise: "lookup_resolved_st (dl, dg, ps) (Global_Location x)
      = lookup_resolved_st (dl', dg', qs) (Global_Location x)"
    using lookup_eq by (rule fun_cong)
  have mo_g_ps: "map_of ps (Global_Location x) = None"
    using global_split(1) by (simp add: map_of_resolved_none_iff)
  have mo_g_qs: "map_of qs (Global_Location x) = None"
    using global_split(2) by (simp add: map_of_resolved_none_iff)
  show "dg = dg'"
    using dg_pointwise by (simp add: mo_g_ps mo_g_qs)
qed

text \<open>
  \<open>resolved_st_is_bot_for\<close> as written takes \<open>gs\<close> as a free parameter, which makes it
  \<open>eq_resolved_st\<close>-respectful only when \<open>gs\<close> actually agrees with \<open>globals\<close> (a mismatched
  pair can pick out a witness through one representative's override list that another,
  extensionally equal, representative encodes via its defaults instead). Every real caller
  already supplies exactly the matching pair (\<open>resolved_st_q_is_bot_for (declared_global_vars
  p) (declared_global p)\<close>), so fixing \<open>gs\<close> to \<open>%x. x : set globals\<close> internally loses nothing
  and restores unconditional respectfulness: the explicit \<open>globals\<close> scan then catches every
  global witness a differing override encoding could produce, and \<open>eq_resolved_st_defaults\<close>
  pins the two representatives' \<open>dl\<close>/\<open>dg\<close> together for the local case. This is what makes
  \<open>resolved_st_q_is_bot_for\<close> below liftable to the quotient at all.
\<close>

lemma eq_resolved_st_is_bot_for_mono:
  assumes eq: "eq_resolved_st s t"
    and bot: "resolved_st_is_bot_for globals (%x. x : set globals) s"
  shows "resolved_st_is_bot_for globals (%x. x : set globals) t"
proof -
  obtain dl dg ps where s_eq: "s = (dl, dg, ps)" by (cases s)
  obtain dl' dg' qs where t_eq: "t = (dl', dg', qs)" by (cases t)
  have eq_pat: "eq_resolved_st (dl, dg, ps) (dl', dg', qs)"
    using eq unfolding s_eq t_eq .
  have dl_eq: "dl = dl'" using eq_resolved_st_defaults(1)[OF eq_pat] .
  have lookup_eq: "lookup_resolved_st s = lookup_resolved_st t"
    using eq unfolding eq_resolved_st_def by simp
  show ?thesis
  proof (cases "EX x : set globals. is_bot (lookup_resolved_st s (location_of (%x. x : set globals) x))")
    case True
    then show ?thesis
      unfolding resolved_st_is_bot_for_def using lookup_eq by auto
  next
    case False
    then have rb: "resolved_st_is_bot (%x. x : set globals) s"
      using bot unfolding resolved_st_is_bot_for_def by blast
    then consider (dlc) "is_bot dl"
      | (psc) loc0 where "loc0 : set (map fst ps)" "is_bot (lookup_resolved_st s loc0)"
          "location_of (%x. x : set globals) (location_vname loc0) = loc0"
      unfolding resolved_st_is_bot_def s_eq by auto
    then show ?thesis
    proof cases
      case dlc
      have "is_bot dl'" using dlc dl_eq by simp
      then have "resolved_st_is_bot (%x. x : set globals) t"
        unfolding resolved_st_is_bot_def t_eq by auto
      then show ?thesis unfolding resolved_st_is_bot_for_def by blast
    next
      case (psc loc0)
      have lookup_t_loc0: "lookup_resolved_st t loc0 = lookup_resolved_st s loc0"
        using lookup_eq by simp
      then have bot_t_loc0: "is_bot (lookup_resolved_st t loc0)"
        using psc(2) by simp
      show ?thesis
      proof (cases "map_of qs loc0")
        case (Some a)
        then have loc0_in_qs: "loc0 : set (map fst qs)"
          by (force dest: map_of_SomeD)
        have bot_t_loc0': "is_bot (lookup_resolved_st (dl', dg', qs) loc0)"
          using bot_t_loc0 unfolding t_eq .
        have "resolved_st_is_bot (%x. x : set globals) t"
          unfolding resolved_st_is_bot_def t_eq
          using bot_t_loc0' psc(3) loc0_in_qs by auto
        then show ?thesis unfolding resolved_st_is_bot_for_def by blast
      next
        case None
        then have default_val:
          "lookup_resolved_st t loc0 =
             (case loc0 of Local_Location x => dl' | Global_Location x => dg')"
          unfolding t_eq by simp
        show ?thesis
        proof (cases loc0)
          case (Local_Location y)
          then have "is_bot dl'"
            using default_val bot_t_loc0 by simp
          then have "resolved_st_is_bot (%x. x : set globals) t"
            unfolding resolved_st_is_bot_def t_eq by auto
          then show ?thesis unfolding resolved_st_is_bot_for_def by blast
        next
          case (Global_Location y)
          then have gs_y: "y : set globals"
            using psc(3) unfolding location_of_def by (auto split: if_splits)
          have "is_bot (lookup_resolved_st t (location_of (%x. x : set globals) y))"
            using default_val bot_t_loc0 Global_Location gs_y
            unfolding location_of_def by simp
          then show ?thesis
            unfolding resolved_st_is_bot_for_def using gs_y by blast
        qed
      qed
    qed
  qed
qed

lemma eq_resolved_st_is_bot_for:
  assumes eq: "eq_resolved_st s t"
  shows "resolved_st_is_bot_for globals (%x. x : set globals) s
       = resolved_st_is_bot_for globals (%x. x : set globals) t"
proof
  assume "resolved_st_is_bot_for globals (%x. x : set globals) s"
  then show "resolved_st_is_bot_for globals (%x. x : set globals) t"
    using eq_resolved_st_is_bot_for_mono[OF eq] by blast
next
  have eq': "eq_resolved_st t s"
    using eq unfolding eq_resolved_st_def by simp
  assume "resolved_st_is_bot_for globals (%x. x : set globals) t"
  then show "resolved_st_is_bot_for globals (%x. x : set globals) s"
    using eq_resolved_st_is_bot_for_mono[OF eq'] by blast
qed

text \<open>
  The exec-bridge exact witness-bottom check (@{thm resolved_st_is_bot_for_iff}),
  transported to the quotient through @{const rep_resolved_st}. This is the
  predicate the executable side trees are built against: unlike
  @{const is_bot_state} composed with @{const fun_of_resolved_st_q_for}, it has
  a genuine \<open>[code]\<close> equation, since it never quantifies over all of
  @{typ vname}.
\<close>

text \<open>
  \<open>gs\<close> is deliberately not a parameter of the raw witness below (it always agrees with
  \<open>%x. x : set globals\<close> at every real call site, per @{thm resolved_st_is_bot_for_iff}'s own
  hypothesis) -- fixing it internally this way, rather than accepting a caller-supplied \<open>gs\<close>,
  is exactly what makes @{thm eq_resolved_st_is_bot_for} apply unconditionally and this
  definition liftable at all. Every real caller already recomputes the same \<open>gs\<close> from
  \<open>globals\<close> at the call site, so dropping the redundant parameter loses nothing.
\<close>

lift_definition resolved_st_q_is_bot_for ::
  "vname list => ('a::computable_domain) resolved_st_q => bool"
  is "%globals s. resolved_st_is_bot_for globals (%x. x : set globals) s"
  by (rule eq_resolved_st_is_bot_for)

lemma resolved_st_q_is_bot_for_alt:
  "resolved_st_q_is_bot_for globals s =
     resolved_st_is_bot_for globals (%x. x : set globals) (rep_resolved_st s)"
  by (rule resolved_st_q_is_bot_for.rep_eq)

lemma resolved_st_q_is_bot_for_iff:
  assumes globals: "\<And>x. gs x = (x \<in> set globals)"
  shows "resolved_st_q_is_bot_for globals s \<longleftrightarrow> is_bot_state (fun_of_resolved_st_q_for gs s)"
proof -
  have gs_eq: "gs = (%x. x : set globals)"
    using globals by (rule ext)
  have step1: "resolved_st_q_is_bot_for globals s =
                 resolved_st_is_bot_for globals (%x. x : set globals) (rep_resolved_st s)"
    by (rule resolved_st_q_is_bot_for_alt)
  have step2: "resolved_st_is_bot_for globals (%x. x : set globals) (rep_resolved_st s) =
                 resolved_st_is_bot_for globals gs (rep_resolved_st s)"
    using gs_eq by simp
  have step3: "resolved_st_is_bot_for globals gs (rep_resolved_st s) =
                 is_bot_state (fun_of_resolved_st_for gs (rep_resolved_st s))"
    by (rule resolved_st_is_bot_for_iff[OF globals])
  show ?thesis
    using step1 step2 step3 fun_of_resolved_st_q_for_rep[of gs s] by simp
qed

text \<open>
  \<open>resolved_st_q_is_bot_for\<close>'s lifted counterpart: a solver-level \<open>Bot\<close> local
  unknown is \<open>True\<close> outright, without inspecting any \<open>resolved_st_q\<close> payload at
  all, matching \<^const>\<open>is_bot_state_lift\<close>'s own \<open>Bot\<close> case. This is the
  executable predicate the report layer needs at the point where it currently
  case-splits \<open>Bot\<close>/\<open>Lifted\<close> and discards which branch fired.
\<close>

fun resolved_st_q_lifted_is_bot_for ::
  "vname list \<Rightarrow> ('a::computable_domain) resolved_st_q lifted \<Rightarrow> bool" where
  "resolved_st_q_lifted_is_bot_for globals Bot = True"
| "resolved_st_q_lifted_is_bot_for globals (Lifted s) = resolved_st_q_is_bot_for globals s"

lemma resolved_st_q_lifted_is_bot_for_iff:
  assumes globals: "\<And>x. gs x = (x \<in> set globals)"
  shows "resolved_st_q_lifted_is_bot_for globals s
       \<longleftrightarrow> is_bot_state_lift (map_lift (fun_of_resolved_st_q_for gs) s)"
  by (cases s) (simp_all add: resolved_st_q_is_bot_for_iff[OF globals])




lemma fun_of_resolved_st_q_for_mono:
  assumes "s \<le> t"
  shows "fun_of_resolved_st_q_for gs s \<le> fun_of_resolved_st_q_for gs t"
  using assms
  unfolding fun_of_resolved_st_q_for_def le_fun_def
  by (simp add: le_resolved_st_q_iff)


lemma fun_of_resolved_st_q_for_enter_frame [simp]:
  "fun_of_resolved_st_q_for gs
      (enter_frame_D_resolved_q top_val s) =
   enter_frame gs top_val (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  apply transfer
  by (metis (no_types, lifting) ext fun_of_resolved_st_for_def
      fun_of_st_enter_frame_D_resolved)

lemma fun_of_resolved_st_q_for_bind_formals [simp]:
  "fun_of_resolved_st_q_for gs
      (bind_formals_resolved_q gs xs avs s) =
   bind_formals xs avs (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  apply transfer
  by (metis (no_types, lifting) ext fun_of_resolved_st_for_def
      fun_of_resolved_st_for_bind_formals)
definition resolved_st_q_refines_for ::
  "(vname => bool) => ('a::bot) resolved_st_q => 'a abs_state => bool"
where
  "resolved_st_q_refines_for gs s sigma =
     (fun_of_resolved_st_q_for gs s = sigma)"

lemma fun_of_resolved_st_q_for_combine_assign [simp]:
  "fun_of_resolved_st_q_for gs
      (combine_assign_resolved_q gs dst v s) =
   combine_assign dst v (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  apply transfer
  by (metis (no_types, lifting) ext fun_of_resolved_st_for_def
      fun_of_resolved_st_for_combine_assign)

lemma fun_of_resolved_st_q_for_update [simp]:
  "fun_of_resolved_st_q_for gs
      (update_resolved_st_q s (location_of gs x) a) =
   (fun_of_resolved_st_q_for gs s)(x := a)"
proof (rule ext)
  fix y
  show "fun_of_resolved_st_q_for gs
      (update_resolved_st_q s (location_of gs x) a) y =
    ((fun_of_resolved_st_q_for gs s)(x := a)) y"
    unfolding fun_of_resolved_st_q_for_def
    by (cases "x = y"; cases "gs x"; cases "gs y";
        simp_all add: location_of_def)
qed

subsection \<open>Structural reachability lift for the resolved-state quotient\<close>

definition live_resolved_st_q ::
  "(vname => bool) => ('a::sound_domain) resolved_st_q => bool"
where
  "live_resolved_st_q gs s = (~ is_bot_state (fun_of_resolved_st_q_for gs s))"

lemma live_resolved_st_qI:
  "(!!x. ~ is_bot (fun_of_resolved_st_q_for gs s x)) ==> live_resolved_st_q gs s"
  unfolding live_resolved_st_q_def is_bot_state_def by blast

lemma live_resolved_st_qE:
  assumes "live_resolved_st_q gs s"
  shows "~ is_bot (fun_of_resolved_st_q_for gs s x)"
  using assms unfolding live_resolved_st_q_def is_bot_state_def by blast

text \<open>
  \<open>is_bot_state\<close> on \<open>fun_of_resolved_st_q_for gs s\<close> is an infinite existential over
  \<open>vname\<close>, not executable on a quotient value.  \<open>update_resolved_st_q_lift\<close> tracks it
  incrementally instead: given a @{const live_resolved_st_q} input and the single
  freshly computed element, the result is witness-bottom iff that element is
  \<open>is_bot\<close> -- every other location is provably unchanged
  (@{thm fun_of_resolved_st_q_for_update}), so it cannot newly become bottom.  This
  mirrors Goblint's per-analysis \<open>Deadcode\<close> raise while staying generic: it lives at
  the shared update primitive, not in each domain's own transfer code.
\<close>

definition update_resolved_st_q_lift ::
  "('a::sound_domain) resolved_st_q lifted => location => 'a => 'a resolved_st_q lifted"
where
  "update_resolved_st_q_lift x loc a = do {
     s <- x;
     if is_bot a then Bot else Lifted (update_resolved_st_q s loc a)
   }"

lemma update_resolved_st_q_lift_Bot [simp]:
  "update_resolved_st_q_lift Bot loc a = Bot"
  unfolding update_resolved_st_q_lift_def by simp

lemma update_resolved_st_q_lift_Lifted:
  "update_resolved_st_q_lift (Lifted s) loc a =
     (if is_bot a then Bot else Lifted (update_resolved_st_q s loc a))"
  unfolding update_resolved_st_q_lift_def by simp

text \<open>
  The completeness theorem the location-scoped check relies on: from a live input,
  the lifted update exactly tracks the spec-level normalized result.  Only the
  freshly written variable's element needs checking -- every other variable's
  \<open>abs_state\<close> component provably survives unchanged
  (@{thm fun_of_resolved_st_q_for_update}), so it cannot be the source of a new
  witness-bottom.
\<close>
lemma update_resolved_st_q_lift_correct:
  fixes s :: "'a::sound_domain resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (update_resolved_st_q_lift (Lifted s) (location_of gs x) a) =
         normalize_lift is_bot_state ((fun_of_resolved_st_q_for gs s)(x := a))"
proof (cases "is_bot a")
  case True
  have "is_bot_state ((fun_of_resolved_st_q_for gs s)(x := a))"
    by (rule is_bot_stateI[of _ x]) (simp add: True)
  with True show ?thesis
    by (simp add: update_resolved_st_q_lift_Lifted)
next
  case False
  have not_bot: "~ is_bot_state ((fun_of_resolved_st_q_for gs s)(x := a))"
  proof
    assume "is_bot_state ((fun_of_resolved_st_q_for gs s)(x := a))"
    then obtain y where y: "is_bot (((fun_of_resolved_st_q_for gs s)(x := a)) y)"
      by (rule is_bot_stateE)
    show False
    proof (cases "y = x")
      case True
      with y False show ?thesis by simp
    next
      case False
      with y have "is_bot (fun_of_resolved_st_q_for gs s y)" by simp
      with live show ?thesis using live_resolved_st_qE by blast
    qed
  qed
  from False not_bot show ?thesis
    by (simp add: update_resolved_st_q_lift_Lifted fun_of_resolved_st_q_for_update)
qed

text \<open>
  \<open>bind_formals\<close>'s fold-of-updates is pointwise characterizable by \<open>map_of\<close> once
  the formal names are distinct: no formal's binding is later overwritten by
  another, so lookup at any location reduces to a single \<open>map_of\<close> probe.
\<close>
lemma fold_fun_upd_notin:
  "x \<notin> set (map fst ps) ==> fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) ps sigma x = sigma x"
proof (induction ps arbitrary: sigma)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain y b where p: "p = (y, b)" by (cases p)
  have neq: "x \<noteq> y" and notin: "x \<notin> set (map fst ps)" using Cons.prems p by auto
  have "fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (p # ps) sigma x =
          fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) ps (sigma(y := b)) x"
    using p by simp
  also have "... = (sigma(y := b)) x"
    using Cons.IH[OF notin, of "sigma(y := b)"] .
  also have "... = sigma x" using neq by simp
  finally show ?case .
qed

lemma fold_fun_upd_apply:
  assumes "distinct (map fst ps)"
  shows "fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) ps sigma y =
           (case map_of ps y of Some a => a | None => sigma y)"
  using assms
proof (induction ps arbitrary: sigma)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain x a where p: "p = (x, a)" by (cases p)
  show ?case
  proof (cases "y = x")
    case True
    have notin: "x \<notin> set (map fst ps)" using Cons.prems p by simp
    have "fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (p # ps) sigma y =
            fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) ps (sigma(x := a)) x"
      using p True by simp
    also have "... = (sigma(x := a)) x"
      using fold_fun_upd_notin[OF notin] .
    also have "... = a" by simp
    also have "... = (case map_of (p # ps) y of Some b => b | None => sigma y)"
      using p True by simp
    finally show ?thesis .
  next
    case False
    have dist: "distinct (map fst ps)" using Cons.prems p by simp
    have "fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (p # ps) sigma y =
            fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) ps (sigma(x := a)) y"
      using p by simp
    also have "... = (case map_of ps y of Some b => b | None => (sigma(x := a)) y)"
      using Cons.IH[OF dist, of "sigma(x := a)"] .
    also have "... = (case map_of ps y of Some b => b | None => sigma y)"
      using False by (cases "map_of ps y") simp_all
    also have "... = (case map_of (p # ps) y of Some b => b | None => sigma y)"
      using p False by simp
    finally show ?thesis .
  qed
qed

text \<open>
  A formals list names only finitely many locals, and (per Voblint's CFG
  well-formedness) every classifier \<open>gs\<close> leaves infinitely many vnames local: this
  is the same premise \<open>resolved_st_is_bot_sound\<close> relies on, needed here to
  obtain a local vname the formals list does not shadow.
\<close>
lemma is_bot_state_bind_formals_abs_enter_frame:
  fixes top_val :: "'a::sound_domain" and sigma :: "'a abs_state"
  assumes live: "~ is_bot_state sigma"
    and top_ok: "~ is_bot top_val"
    and dist: "distinct xs"
    and len: "length xs = length avs"
    and infinite_local: "infinite {x. ~ gs x}"
  shows "is_bot_state (bind_formals xs avs (enter_frame gs top_val sigma))
       \<longleftrightarrow> is_bot top_val \<or> (\<exists>v \<in> set avs. is_bot v)"
proof -
  have dist': "distinct (map fst (zip xs avs))"
    using dist len by (simp add: map_fst_zip)
  show ?thesis
  proof
    assume "is_bot_state (bind_formals xs avs (enter_frame gs top_val sigma))"
    then obtain y where y:
      "is_bot (bind_formals xs avs (enter_frame gs top_val sigma) y)"
      by (rule is_bot_stateE)
    show "is_bot top_val \<or> (\<exists>v \<in> set avs. is_bot v)"
    proof (cases "map_of (zip xs avs) y")
      case None
      then have "bind_formals xs avs (enter_frame gs top_val sigma) y =
                   enter_frame gs top_val sigma y"
        unfolding fold_fun_upd_apply[OF dist'] by simp
      with y have "is_bot (enter_frame gs top_val sigma y)" by simp
      then have "is_bot top_val \<or> is_bot (sigma y)"
        unfolding enter_frame_def by (cases "gs y") simp_all
      with live show ?thesis by (auto simp: is_bot_state_def)
    next
      case (Some v)
      then have "bind_formals xs avs (enter_frame gs top_val sigma) y = v"
        unfolding fold_fun_upd_apply[OF dist'] by simp
      with y have "is_bot v" by simp
      moreover have "v \<in> set avs" using Some by (rule map_of_SomeD[THEN set_zip_rightD])
      ultimately show ?thesis by blast
    qed
  next
    assume disj: "is_bot top_val \<or> (\<exists>v \<in> set avs. is_bot v)"
    show "is_bot_state (bind_formals xs avs (enter_frame gs top_val sigma))"
    proof (cases "\<exists>v \<in> set avs. is_bot v")
      case True
      then obtain v where v: "v \<in> set avs" "is_bot v" by blast
      then obtain i where i: "i < length avs" "avs ! i = v" by (metis in_set_conv_nth)
      then have i': "i < length xs" using len by simp
      have len_zip: "i < length (zip xs avs)" using i' i(1) by simp
      have mem: "(xs ! i, avs ! i) \<in> set (zip xs avs)"
        using nth_mem[OF len_zip] nth_zip[OF i' i(1)] by simp
      have "map_of (zip xs avs) (xs ! i) = Some v"
        using dist' mem i by (simp add: map_of_eq_Some_iff)
      then have "bind_formals xs avs (enter_frame gs top_val sigma) (xs ! i) = v"
        unfolding fold_fun_upd_apply[OF dist'] by simp
      then show ?thesis using v by (metis is_bot_stateI)
    next
      case False
      with disj have top_bot: "is_bot top_val" by blast
      have "finite (set xs)" by (rule finite_set)
      then have "infinite ({x. ~ gs x} - set xs)"
        using infinite_local by (rule Diff_infinite_finite)
      then obtain z where z: "~ gs z" "z \<notin> set xs"
        using infinite_imp_nonempty by blast
      have "fst ` set (zip xs avs) \<subseteq> set xs"
        using set_zip_leftD by fastforce
      with z(2) have "z \<notin> fst ` set (zip xs avs)" by blast
      then have "map_of (zip xs avs) z = None"
        by (simp add: map_of_eq_None_iff)
      then have "bind_formals xs avs (enter_frame gs top_val sigma) z =
                   enter_frame gs top_val sigma z"
        unfolding fold_fun_upd_apply[OF dist'] by simp
      also have "... = top_val" using z unfolding enter_frame_def by simp
      finally show ?thesis using top_bot by (metis is_bot_stateI)
    qed
  qed
qed

text \<open>
  \<open>enter_resolved_st_q_lift\<close> is the exec analog of @{const update_resolved_st_q_lift}:
  input-strict on \<open>Bot\<close>, and normalizes to \<open>Bot\<close> exactly when the fresh frame or one
  of the freshly computed formal values is \<open>is_bot\<close> -- both finite, decidable checks,
  never a scan of the resolved state itself.
\<close>
definition enter_resolved_st_q_lift ::
  "(vname => bool) => 'a::sound_domain resolved_st_q lifted
   => 'a => vname list => 'a list => 'a resolved_st_q lifted"
where
  "enter_resolved_st_q_lift gs x top_val xs avs = do {
     s <- x;
     if is_bot top_val \<or> list_ex is_bot avs then Bot
     else Lifted (bind_formals_resolved_q gs xs avs (enter_frame_D_resolved_q top_val s))
   }"

lemma enter_resolved_st_q_lift_Bot [simp]:
  "enter_resolved_st_q_lift gs Bot top_val xs avs = Bot"
  unfolding enter_resolved_st_q_lift_def by simp

lemma enter_resolved_st_q_lift_correct:
  fixes s :: "'a::sound_domain resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
    and dist: "distinct xs" and len: "length xs = length avs"
    and infinite_local: "infinite {x. ~ gs x}"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (enter_resolved_st_q_lift gs (Lifted s) top_val xs avs) =
        normalize_lift is_bot_state
          (bind_formals xs avs (enter_frame gs top_val (fun_of_resolved_st_q_for gs s)))"
proof -
  have key: "is_bot_state
      (bind_formals xs avs (enter_frame gs top_val (fun_of_resolved_st_q_for gs s)))
    \<longleftrightarrow> is_bot top_val \<or> list_ex is_bot avs"
  proof (cases "is_bot top_val")
    case True
    have dist': "distinct (map fst (zip xs avs))"
      using dist len by (simp add: map_fst_zip)
    have "finite (set xs)" by (rule finite_set)
    then have "infinite ({x. ~ gs x} - set xs)"
      using infinite_local by (rule Diff_infinite_finite)
    then obtain z where z: "~ gs z" "z \<notin> set xs"
      by (metis (mono_tags, lifting) Collect_mem_eq Collect_mono_iff
          infinite_local list.set_finite rev_finite_subset)
    have "fst ` set (zip xs avs) \<subseteq> set xs"
      using set_zip_leftD by fastforce
    with z(2) have "z \<notin> fst ` set (zip xs avs)" by blast
    then have "map_of (zip xs avs) z = None"
      by (simp add: map_of_eq_None_iff)
    then have "bind_formals xs avs
                 (enter_frame gs top_val (fun_of_resolved_st_q_for gs s)) z =
               enter_frame gs top_val (fun_of_resolved_st_q_for gs s) z"
      unfolding fold_fun_upd_apply[OF dist'] by simp
    also have "... = top_val" using z unfolding enter_frame_def by simp
    finally have "is_bot (bind_formals xs avs
                    (enter_frame gs top_val (fun_of_resolved_st_q_for gs s)) z)"
      using True by simp
    then have "is_bot_state
        (bind_formals xs avs (enter_frame gs top_val (fun_of_resolved_st_q_for gs s)))"
      by (rule is_bot_stateI)
    with True show ?thesis by simp
  next
    case False
    show ?thesis
      using is_bot_state_bind_formals_abs_enter_frame
              [OF live[unfolded live_resolved_st_q_def] False dist len infinite_local]
      by (simp add: list_ex_iff)
  qed
  show ?thesis
    unfolding enter_resolved_st_q_lift_def normalize_lift_def
    by (simp add: key)
qed




lemma fun_of_resolved_st_q_for_restrict_local [simp]:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) x =
     (if gs x then bot else fun_of_resolved_st_q_for gs s x)"
  unfolding fun_of_resolved_st_q_for_def location_of_def
  by (cases "gs x") simp_all

lemma fun_of_resolved_st_q_for_restrict_global [simp]:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) x =
     (if gs x then fun_of_resolved_st_q_for gs s x else bot)"
  unfolding fun_of_resolved_st_q_for_def location_of_def
  by (cases "gs x") simp_all

lemma fun_of_resolved_st_q_for_combine [simp]:
  "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) =
   combine_env gs (fun_of_resolved_st_q_for gs sc)
     (fun_of_resolved_st_q_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) x =
      combine_env gs (fun_of_resolved_st_q_for gs sc)
        (fun_of_resolved_st_q_for gs se) x"
    unfolding fun_of_resolved_st_q_for_def combine_env_def location_of_def
    by (cases "gs x") simp_all
qed

text \<open>
  \<open>combine_env\<close> is a pointwise selector (@{thm combine_env_def}), not a join:
  every location's result is exactly the caller's or the callee-exit's own value, so
  two live operands can never combine into a witness-bottom result.  The combine
  lift is therefore purely input-strict, with no output-side check at all.
\<close>
definition combine_resolved_st_q_lift ::
  "'a::sound_domain resolved_st_q lifted => 'a resolved_st_q lifted
   => 'a resolved_st_q lifted"
where
  "combine_resolved_st_q_lift x y = do {
     sc <- x;
     se <- y;
     Lifted (combine_resolved_st_q sc se)
   }"

lemma combine_resolved_st_q_lift_Bot_left [simp]:
  "combine_resolved_st_q_lift Bot y = Bot"
  unfolding combine_resolved_st_q_lift_def by simp

lemma combine_resolved_st_q_lift_Bot_right [simp]:
  "combine_resolved_st_q_lift (Lifted sc) Bot = Bot"
  unfolding combine_resolved_st_q_lift_def by simp

lemma combine_resolved_st_q_lift_Lifted [simp]:
  "combine_resolved_st_q_lift (Lifted sc) (Lifted se) =
     Lifted (combine_resolved_st_q sc se)"
  unfolding combine_resolved_st_q_lift_def by simp

lemma combine_resolved_st_q_lift_correct:
  fixes sc se :: "'a::sound_domain resolved_st_q"
  assumes live_c: "live_resolved_st_q gs sc" and live_e: "live_resolved_st_q gs se"
  shows "~ is_bot_state (fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se))"
  unfolding fun_of_resolved_st_q_for_combine
proof (rule notI)
  assume "is_bot_state (combine_env gs (fun_of_resolved_st_q_for gs sc)
                                        (fun_of_resolved_st_q_for gs se))"
  then obtain y where y:
    "is_bot (combine_env gs (fun_of_resolved_st_q_for gs sc)
                              (fun_of_resolved_st_q_for gs se) y)"
    by (rule is_bot_stateE)
  show False
    using y live_c live_e
    unfolding combine_env_def
    by (cases "gs y") (auto simp: live_resolved_st_qE)
qed


lemma fun_of_resolved_st_q_for_sup [simp]:
  "fun_of_resolved_st_q_for gs (s \<squnion> t) =
   fun_of_resolved_st_q_for gs s \<squnion> fun_of_resolved_st_q_for gs t"
  by (rule ext) (simp add: fun_of_resolved_st_q_for_def sup_fun_def)

lemma fun_of_resolved_st_q_for_enter [simp]:
  "fun_of_resolved_st_q_for gs
      (enter_resolved_for_q gs top_val aval_abs xs es s) =
   enter_D gs top_val aval_abs xs es
      (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  apply transfer
  by (metis (no_types, lifting) ext fun_of_resolved_st_for_def
      fun_of_resolved_st_for_enter_resolved)

lemma fun_of_resolved_st_q_for_combine_collect [simp]:
  "fun_of_resolved_st_q_for gs
      (combine_collect_resolved_for_q gs dst sc se) =
   combine\<^sup># gs dst
      (fun_of_resolved_st_q_for gs sc)
      (fun_of_resolved_st_q_for gs se)"
  unfolding fun_of_resolved_st_q_for_def
  apply transfer
  by (metis (no_types, lifting) ext fun_of_resolved_st_for_combine_collect
      fun_of_resolved_st_for_def)

locale resolved_st_q_refinement =
  fixes gs :: "vname => bool"
begin

lemma refines_update_q:
  assumes "resolved_st_q_refines_for gs s sigma"
  shows "resolved_st_q_refines_for gs
      (update_resolved_st_q s (location_of gs x) a) (sigma(x := a))"
  using assms
  unfolding resolved_st_q_refines_for_def
  by simp

lemma refines_restrict_local_q:
  assumes "resolved_st_q_refines_for gs s sigma"
  shows "resolved_st_q_refines_for gs (restrict_local_resolved_q s)
      (%x. if gs x then bot else sigma x)"
  using assms
  unfolding resolved_st_q_refines_for_def
  by (simp add: fun_eq_iff)

lemma refines_restrict_global_q:
  assumes "resolved_st_q_refines_for gs s sigma"
  shows "resolved_st_q_refines_for gs (restrict_global_resolved_q s)
      (%x. if gs x then sigma x else bot)"
  using assms
  unfolding resolved_st_q_refines_for_def
  by (simp add: fun_eq_iff)

lemma refines_combine_q:
  assumes sc: "resolved_st_q_refines_for gs sc sigma_c"
    and se: "resolved_st_q_refines_for gs se sigma_e"
  shows "resolved_st_q_refines_for gs (combine_resolved_st_q sc se)
      (combine_env gs sigma_c sigma_e)"
  using sc se
  unfolding resolved_st_q_refines_for_def
  by simp

lemma refines_enter_q:
  assumes "resolved_st_q_refines_for gs s sigma"
  shows "resolved_st_q_refines_for gs
      (enter_resolved_for_q gs top_val aval_abs xs es s)
      (enter_D gs top_val aval_abs xs es sigma)"
  using assms
  unfolding resolved_st_q_refines_for_def
  by simp

lemma refines_combine_collect_q:
  assumes sc: "resolved_st_q_refines_for gs sc sigma_c"
    and se: "resolved_st_q_refines_for gs se sigma_e"
  shows "resolved_st_q_refines_for gs
      (combine_collect_resolved_for_q gs dst sc se)
      (combine\<^sup># gs dst sigma_c sigma_e)"
  using sc se
  unfolding resolved_st_q_refines_for_def
  by simp

end


end

                                           





