theory Exec_St
  imports Abstract_Domain "TD.Update_rules"
    Constraint_System
begin

class bounded_widening = bounded_semilattice_sup_bot + widening
class bounded_narrowing = bounded_semilattice_sup_bot + narrowing
class bounded_warrowing = bounded_semilattice_sup_bot + warrowing

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

lemma map_of_remove_resolved_key:
  "map_of (remove_resolved_key loc ps) loc' =
     (if loc = loc' then None else map_of ps loc')"
  by (induction ps arbitrary: loc') auto

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
  by (rule ex_new_if_finite[OF List.infinite_UNIV_listI]) simp

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
  "(vname => bool) => 'a => (aexp => 'a abs_state => 'a)
   => vname list => aexp list => ('a::bot) resolved_st => 'a resolved_st"
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
lemma map_of_filter_fst:
  fixes P :: "location => bool"
    and xs :: "(location \<times> 'a) list"
    and k :: location
  shows "map_of (filter (%p. P (fst p)) xs) k =
     (if P k then map_of xs k else None)"
  by (induction xs) auto

lemma map_of_filter_global_local:
  "map_of (filter (%p. location_is_global (fst p)) ps)
      (Local_Location x) = None"
  by (induction ps) (auto split: location.splits)

lemma map_of_filter_local_global:
  "map_of (filter (%p. location_is_local (fst p)) ps)
      (Global_Location x) = None"
  by (induction ps) (auto split: location.splits)

lemma map_of_filter_local_local:
  "map_of (filter (%p. location_is_local (fst p)) ps)
      (Local_Location x) =
     map_of ps (Local_Location x)"
  by (induction ps) (auto split: location.splits)

lemma map_of_filter_global_global:
  "map_of (filter (%p. location_is_global (fst p)) ps)
      (Global_Location x) =
     map_of ps (Global_Location x)"
  by (induction ps) (auto split: location.splits)

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

lemma map_of_merge_pair:
  "map_of (ps1 @ ps2) x =
   (case map_of ps1 x of Some a => Some a | None => map_of ps2 x)"
  by (induction ps1) auto

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
       map_of_map_fst_lookup map_of_merge_pair
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
       map_of_map_fst_lookup map_of_merge_pair
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
       map_of_map_fst_lookup map_of_merge_pair
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
   combine_abs gs (fun_of_resolved_st_for gs sc)
     (fun_of_resolved_st_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_for gs (combine_resolved_st sc se) x =
      combine_abs gs (fun_of_resolved_st_for gs sc)
        (fun_of_resolved_st_for gs se) x"
    unfolding fun_of_resolved_st_for_def combine_abs_def location_of_def
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
  "(vname => bool) => 'a => (aexp => 'a abs_state => 'a)
   => vname list => aexp list => ('a::bot) resolved_st_q
   => 'a resolved_st_q"
  is enter_resolved_for
  by (rule eq_resolved_st_enter_resolved_for)

lemma fun_of_st_enter_frame_D_resolved [simp]:
  "fun_of_resolved_st_for gs (enter_frame_D_resolved top_val s) =
   enter_frame_D gs top_val (fun_of_resolved_st_for gs s)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_for gs (enter_frame_D_resolved top_val s) x =
      enter_frame_D gs top_val (fun_of_resolved_st_for gs s) x"
    unfolding enter_frame_D_def fun_of_resolved_st_for_def location_of_def
    by (cases "gs x") simp_all
qed

lemma fun_of_resolved_st_for_combine_assign [simp]:
  "fun_of_resolved_st_for gs
      (combine_assign_resolved gs dst v s) =
   combine_assign_abs dst v (fun_of_resolved_st_for gs s)"
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
   bind_formals_abs xs avs (fun_of_resolved_st_for gs s)"
unfolding bind_formals_resolved_def bind_formals_abs_def
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
   combine_collect_abs gs dst
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
      (combine_abs gs sigma_c sigma_e)"
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
      (combine_collect_abs gs dst sigma_c sigma_e)"
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

lemma fun_of_resolved_st_q_for_mono:
  assumes "s \<le> t"
  shows "fun_of_resolved_st_q_for gs s \<le> fun_of_resolved_st_q_for gs t"
  using assms
  unfolding fun_of_resolved_st_q_for_def le_fun_def
  by (simp add: le_resolved_st_q_iff)


lemma fun_of_resolved_st_q_for_enter_frame [simp]:
  "fun_of_resolved_st_q_for gs
      (enter_frame_D_resolved_q top_val s) =
   enter_frame_D gs top_val (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  apply transfer
  by (metis (no_types, lifting) ext fun_of_resolved_st_for_def
      fun_of_st_enter_frame_D_resolved)

lemma fun_of_resolved_st_q_for_bind_formals [simp]:
  "fun_of_resolved_st_q_for gs
      (bind_formals_resolved_q gs xs avs s) =
   bind_formals_abs xs avs (fun_of_resolved_st_q_for gs s)"
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
   combine_assign_abs dst v (fun_of_resolved_st_q_for gs s)"
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
   combine_abs gs (fun_of_resolved_st_q_for gs sc)
     (fun_of_resolved_st_q_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) x =
      combine_abs gs (fun_of_resolved_st_q_for gs sc)
        (fun_of_resolved_st_q_for gs se) x"
    unfolding fun_of_resolved_st_q_for_def combine_abs_def location_of_def
    by (cases "gs x") simp_all
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
   combine_collect_abs gs dst
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
      (combine_abs gs sigma_c sigma_e)"
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
      (combine_collect_abs gs dst sigma_c sigma_e)"
  using sc se
  unfolding resolved_st_q_refines_for_def
  by simp

end


end

                                           





