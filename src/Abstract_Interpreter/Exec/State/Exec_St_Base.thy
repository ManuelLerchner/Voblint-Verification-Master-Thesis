theory Exec_St_Base
  imports "Voblint_VIMP.VIMP_Syntax" "HOL-Library.AList"
begin

section \<open>Finite default-map representation\<close>

text \<open>
  An abstract state has to be a finite thing before a solver can run on it. A
  \<open>resolved_st\<close> is that finite thing: two default values -- one for local names,
  one for global ones -- and a list of explicitly stored location values.
  Reading a location returns its stored value if it has one and the matching
  default otherwise. Nothing forces a stored value to differ from its default.

  Two such lists can describe the same reading, so the type is quotiented by
  agreement of all lookups. That identifies list order and redundant duplicate
  entries only where they do not affect the reading: \<^const>\<open>map_of\<close> answers
  with the first match, so reordering entries that disagree on a key is a
  genuine change and the quotient keeps it.

  This theory settles the representation, that quotient, and the order,
  equality and point update defined on it. It does not decide which variable
  names are local and which are global -- a \<open>location\<close> records a
  classification this theory never makes. That classifier arrives only in
  \<open>Exec_St_Transfer\<close>, which is built on this.
\<close>

text \<open>
  \<^bold>\<open>Why two defaults, rather than a sparse map over a fixed \<open>top\<close>.\<close>
  Nipkow's \<open>Abs_State\<close> stores only the variables it has heard of and reads
  every other one as \<open>top\<close>. That is the smaller representation, and it makes
  the order and the join shorter to state, so the extra pair of defaults here
  needs a reason. Three, in fact, and each is load-bearing on its own.

  \<^item> \<^bold>\<open>C zero-initialization.\<close> Every domain's entry state gives globals a
    non-\<open>top\<close> value and locals \<open>top\<close> --- \<open>(STop, SZero, [])\<close> for Sign, and the
    parity, interval and product analyses match it. It over-approximates
    \<open>cinit_stores gs = {s. \<forall>x. gs x \<longrightarrow> s x = 0}\<close>, which quantifies over
    \<^emph>\<open>all\<close> names the classifier calls global, for an arbitrary classifier and
    with no finiteness hypothesis. A fixed-\<open>top\<close> map can only express that by
    materializing every global, which makes the entry state a function of the
    program's declaration list and pushes that dependency into every soundness
    statement that mentions it.

  \<^item> \<^bold>\<open>The ownership split needs \<open>bot\<close> on the discarded side.\<close> Publishing a
    state's global half to a shared unknown sends locals to \<open>bot\<close>, and \<open>bot\<close> is
    what makes that half a unit for the join that combines publications from
    every call site. \<open>top\<close> there would not be a unit. These half-states are not
    transient: they are stored in solver unknowns and compared against the
    solution.

  \<^item> \<^bold>\<open>The solver needs a least element on this type.\<close> The ownership-split
    specification types both its local and global unknowns at this carrier and
    demands \<open>bounded_semilattice_sup_bot\<close> of it, so unknowns can start at
    \<open>bot\<close>. That element is the everywhere-\<open>bot\<close> state, which a sparse map over a
    fixed \<open>top\<close> cannot represent at all.

  What the defaults cost is visible throughout this theory: the order has to
  compare them, extensional equality has to pin them, and the emptiness test in
  \<open>Exec_St_Reachability\<close> has to reason about them. That cost is the price of the
  three points above, not an accident of the first representation tried.
\<close>

subsection \<open>Locations and raw lookup\<close>
datatype location =
  Local_Location (location_vname: vname)
| Global_Location (location_vname: vname)

type_synonym 'a resolved_st =
  "'a \<times> 'a \<times> (location \<times> 'a) list"

lemma map_of_resolved_delete:
  "map_of (AList.delete loc ps) loc' =
     (if loc = loc' then None else map_of ps loc')"
  by (simp add: AList.delete_conv')

fun lookup_resolved_st ::
  "('a::bot) resolved_st => location => 'a" where
  "lookup_resolved_st (dl, dg, ps) loc =
     (case map_of ps loc of
        Some a => a
      | None => (case loc of
          Local_Location x => dl
        | Global_Location x => dg))"

subsection \<open>Extensional equality\<close>
definition eq_resolved_st ::
  "('a::bot) resolved_st => 'a resolved_st => bool"
where
  "eq_resolved_st s t \<longleftrightarrow>
     lookup_resolved_st s = lookup_resolved_st t"

lemma equivp_eq_resolved_st: "equivp eq_resolved_st"
  unfolding eq_resolved_st_def
  by (rule equivpI) (auto intro: reflpI sympI transpI)

text \<open>
  The two rules every congruence proof below goes through: a raw operation
  respects \<^const>\<open>eq_resolved_st\<close> exactly when its lookup equation says the
  result depends on the arguments only through their lookups.  Stating that
  once keeps the individual congruence proofs down to their own lookup rules.
\<close>

lemma eq_resolved_stI [intro]:
  assumes "\<And>loc. lookup_resolved_st s loc = lookup_resolved_st t loc"
  shows "eq_resolved_st s t"
  unfolding eq_resolved_st_def fun_eq_iff using assms by blast

lemma eq_resolved_stD:
  assumes "eq_resolved_st s t"
  shows "lookup_resolved_st s loc = lookup_resolved_st t loc"
  using assms unfolding eq_resolved_st_def fun_eq_iff by blast

subsection \<open>Executable pointwise order\<close>
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

text \<open>
  A vname escaping a finite list of locations, drawn from any infinite supply.
  Neither of its locations is overridden, which is what makes it reveal both
  defaults at once.  Consumers instantiate the supply with all vnames, or with
  the ones a classifier leaves local; keeping it abstract here is what lets the
  lemma sit below the classification boundary.
\<close>

lemma obtain_fresh_location:
  assumes "infinite A"
  obtains x where "x \<in> A"
    and "Local_Location x \<notin> set locs"
    and "Global_Location x \<notin> set locs"
proof -
  have "infinite (A - location_vname ` set locs)"
    by (rule Diff_infinite_finite[OF _ assms]) simp
  then obtain x where "x \<in> A - location_vname ` set locs"
    using infinite_imp_nonempty by blast
  then have "x \<in> A" "Local_Location x \<notin> set locs"
      "Global_Location x \<notin> set locs"
    by force+
  then show thesis by (rule that)
qed

lemma le_resolved_st_code_raw_iff:
  "le_resolved_st_code (dl, dg, ps) (el, eg, qs) \<longleftrightarrow>
    (\<forall>loc. lookup_resolved_st (dl, dg, ps) loc <=
      lookup_resolved_st (el, eg, qs) loc)"
proof
  assume le: "le_resolved_st_code (dl, dg, ps) (el, eg, qs)"
  show "\<forall>loc. lookup_resolved_st (dl, dg, ps) loc \<le>
      lookup_resolved_st (el, eg, qs) loc"
  proof
    fix loc
    show "lookup_resolved_st (dl, dg, ps) loc \<le>
        lookup_resolved_st (el, eg, qs) loc"
    proof (cases "loc \<in> set (map fst ps @ map fst qs)")
      case True
      with le show ?thesis
        unfolding le_resolved_st_code_def by (simp add: list_all_iff)
    next
      case False
      with le show ?thesis
        unfolding le_resolved_st_code_def
        by (simp add: location.case_eq_if
          map_of_resolved_none_iff[THEN iffD2])
    qed
  qed
next
  assume le: "\<forall>loc. lookup_resolved_st (dl, dg, ps) loc \<le>
      lookup_resolved_st (el, eg, qs) loc"
  obtain x :: vname where fresh: "x \<in> UNIV"
      "Local_Location x \<notin> set (map fst ps @ map fst qs)"
      "Global_Location x \<notin> set (map fst ps @ map fst qs)"
    by (rule obtain_fresh_location[OF infinite_literal])
  have "dl \<le> el" "dg \<le> eg"
    using le[rule_format, of "Local_Location x"]
      le[rule_format, of "Global_Location x"] fresh
    by (simp_all add: map_of_resolved_none_iff[THEN iffD2])
  then show "le_resolved_st_code (dl, dg, ps) (el, eg, qs)"
    unfolding le_resolved_st_code_def using le by (simp add: list_all_iff)
qed

text \<open>
  The same characterization without the tuple pattern, so that quotient-level
  statements can be discharged by \<open>transfer\<close> alone instead of re-opening both
  representatives.
\<close>

lemma le_resolved_st_code_iff:
  "le_resolved_st_code s t \<longleftrightarrow>
    (\<forall>loc. lookup_resolved_st s loc \<le> lookup_resolved_st t loc)"
  by (cases s rule: prod_cases3, cases t rule: prod_cases3)
    (simp add: le_resolved_st_code_raw_iff)


subsection \<open>The extensional quotient\<close>
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
  by (simp add: lookup_resolved_st_q.rep_eq)

lemma resolved_st_q_eq_iff:
  "s = t \<longleftrightarrow>
     lookup_resolved_st_q s = lookup_resolved_st_q t"
  by transfer (simp add: eq_resolved_st_def)

text \<open>
  The quotient-level counterpart of @{thm [source] eq_resolved_stI}: two
  quotient states are equal as soon as they look the same everywhere.  Left
  untagged -- as an \<open>[intro]\<close> rule it would attack every equation at this type
  by extensionality, which is rarely what a goal about a concrete state wants.
\<close>

lemma resolved_st_q_eqI:
  assumes "\<And>loc. lookup_resolved_st_q s loc = lookup_resolved_st_q t loc"
  shows "s = t"
  using assms by (simp add: resolved_st_q_eq_iff fun_eq_iff)


subsection \<open>Order, bottom and executable equality\<close>

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


lemma le_resolved_st_q_iff:
  fixes s t :: "('a::order_bot) resolved_st_q"
  shows "s \<le> t \<longleftrightarrow>
    (\<forall>loc. lookup_resolved_st_q s loc \<le>
      lookup_resolved_st_q t loc)"
  by transfer (rule le_resolved_st_code_iff)


instance resolved_st_q :: (order_bot) order
proof intro_classes
  fix s t u :: "('a::order_bot) resolved_st_q"
  show "(s < t) \<longleftrightarrow> (s \<le> t \<and> \<not> t \<le> s)"
    by (simp add: less_resolved_st_q_def)

  show "s \<le> s"
    by (simp add: le_resolved_st_q_iff)
  show "s \<le> t \<Longrightarrow> t \<le> u \<Longrightarrow> s \<le> u"
    by (auto simp: le_resolved_st_q_iff intro: order_trans)
  show "s \<le> t \<Longrightarrow> t \<le> s \<Longrightarrow> s = t"
    by (auto simp: le_resolved_st_q_iff
      resolved_st_q_eq_iff fun_eq_iff intro: order_antisym)
qed

lemma lookup_bot_resolved_st_q [simp]:
  "lookup_resolved_st_q (bot :: ('a::bot) resolved_st_q) loc = bot"
  unfolding bot_resolved_st_q_def
  by transfer (simp split: location.splits)


lemma bot_le_resolved_st_q:
  "(bot :: ('a::order_bot) resolved_st_q) \<le> s"
  by (simp add: le_resolved_st_q_iff)

instance resolved_st_q :: (order_bot) order_bot
  by standard (rule bot_le_resolved_st_q)
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

subsection \<open>Point updates\<close>
fun update_resolved_st ::
  "('a::bot) resolved_st => location => 'a => 'a resolved_st" where
  "update_resolved_st (dl, dg, ps) loc a =
     (dl, dg, (loc, a) # AList.delete loc ps)"

text \<open>
  One lookup equation for the update, rather than a same/different pair: the
  conditional is what a caller has to reason about anyway, and the two special
  cases fall out of it by \<^term>\<open>simp\<close>.
\<close>

lemma lookup_resolved_st_update [simp]:
  "lookup_resolved_st (update_resolved_st s loc a) loc' =
     (if loc = loc' then a else lookup_resolved_st s loc')"
  by (cases s) (simp add: map_of_resolved_delete)


lemma eq_resolved_st_update:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (update_resolved_st s loc a)
      (update_resolved_st t loc a)"
  by (rule eq_resolved_stI) (simp add: eq_resolved_stD[OF assms])

lift_definition update_resolved_st_q ::
  "('a::bot) resolved_st_q => location => 'a => 'a resolved_st_q"
  is update_resolved_st
  by (rule eq_resolved_st_update)

lemma lookup_resolved_st_q_update [simp]:
  "lookup_resolved_st_q (update_resolved_st_q s loc a) loc' =
     (if loc = loc' then a else lookup_resolved_st_q s loc')"
  by transfer simp

end
