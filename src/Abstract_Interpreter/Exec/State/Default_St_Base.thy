theory Default_St_Base
  imports "Voblint_VIMP.VIMP_Syntax" "HOL-Library.AList"
begin

section \<open>Finite default-map representation\<close>

text \<open>
  An abstract state has to be a finite thing before a solver can run on it. A
  \<open>default_dict\<close> is a finite dictionary that answers every name it does not
  list with a default. A \<open>default_st_rep\<close> is two of them, one per partition:
  a local dictionary and a global one. Reading a location consults the
  dictionary of its partition. Nothing forces a stored value to differ from
  its default.

  Two such pairs can describe the same reading, so the type is quotiented by
  agreement of all lookups. That identifies list order and redundant duplicate
  entries only where they do not affect the reading: \<^const>\<open>map_of\<close> answers
  with the first match, so reordering entries that disagree on a key is a
  genuine change and the quotient keeps it.

  This theory settles the representation, that quotient, and the order,
  equality and point update defined on it. It does not decide which variable
  names are local and which are global -- a \<open>location\<close> records a
  classification this theory never makes. That classifier arrives only in
  \<open>Default_St_Transfer\<close>, which is built on this.
\<close>

text \<open>
  \<^bold>\<open>Why two defaults, rather than a sparse map over a fixed \<open>top\<close>.\<close>
  Nipkow's \<open>Abs_State\<close> stores only the variables it has heard of and reads
  every other one as \<open>top\<close>. That is the smaller representation, and it makes
  the order and the join shorter to state, so the extra pair of defaults here
  needs a reason. Three, in fact, and each is load-bearing on its own.

  \<^item> \<^bold>\<open>C zero-initialization.\<close> Every domain's entry state gives globals a
    non-\<open>top\<close> value and locals \<open>top\<close> --- \<open>\<llangle>(STop, []), (SZero, [])\<rrangle>\<close> for
    Sign, and the parity, interval and product analyses match it. It
    over-approximates \<open>cinit_stores \<G> = {s. \<forall>x. \<G> x \<longrightarrow> s x = 0}\<close>, which
    quantifies over \<^emph>\<open>all\<close> names the classifier calls global, for an arbitrary
    classifier and with no finiteness hypothesis. A fixed-\<open>top\<close> map can only
    express that by materializing every global, which makes the entry state a
    function of the program's declaration list and pushes that dependency into
    every soundness statement that mentions it.

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
  \<open>Default_St_Reachability\<close> has to reason about them. That cost is the price of the
  three points above, not an accident of the first representation tried.
\<close>

subsection \<open>Default dictionaries\<close>

type_synonym 'a default_dict = "'a \<times> (vname \<times> 'a) list"

fun default_dict_get :: "'a default_dict => vname => 'a" where
  "default_dict_get (d, ps) x = (case map_of ps x of Some a => a | None => d)"

fun default_dict_set :: "'a default_dict => vname => 'a => 'a default_dict" where
  "default_dict_set (d, ps) x a = (d, (x, a) # AList.delete x ps)"

lemma map_of_resolved_delete:
  "map_of (AList.delete k ps) k' =
     (if k = k' then None else map_of ps k')"
  by (simp add: AList.delete_conv')

lemma map_of_resolved_none_iff:
  "map_of ps k = None \<longleftrightarrow> k \<notin> set (map fst ps)"
  by (induction ps) auto

lemma default_dict_get_set [simp]:
  "default_dict_get (default_dict_set m x a) y =
     (if x = y then a else default_dict_get m y)"
  by (cases m) (simp add: map_of_resolved_delete)

text \<open>
  A name escaping a finite list, drawn from any infinite supply. It is not
  listed, so a dictionary answers it with its default. Consumers instantiate
  the supply with all vnames, or with the ones a classifier leaves local.
\<close>

lemma obtain_fresh_vname:
  assumes "infinite A"
  obtains x where "x \<in> A" and "x \<notin> set xs"
proof -
  have "infinite (A - set xs)"
    by (rule Diff_infinite_finite[OF _ assms]) simp
  then obtain x where "x \<in> A - set xs"
    using infinite_imp_nonempty by blast
  then have "x \<in> A" "x \<notin> set xs" by simp_all
  then show thesis by (rule that)
qed

text \<open>
  The order on one dictionary compares the defaults and the finitely many
  listed names. An unlisted name reads the default on both sides, so this
  decides the pointwise order over all names.
\<close>

fun le_default_dict :: "('a::order) default_dict => 'a default_dict => bool" where
  "le_default_dict (d, ps) (e, qs) \<longleftrightarrow>
     d \<le> e \<and>
     list_all (\<lambda>x. default_dict_get (d, ps) x \<le> default_dict_get (e, qs) x)
       (map fst ps @ map fst qs)"

lemma le_default_dict_iff:
  "le_default_dict m n \<longleftrightarrow> (\<forall>x. default_dict_get m x \<le> default_dict_get n x)"
proof -
  obtain d ps where m: "m = (d, ps)" by (cases m)
  obtain e qs where n: "n = (e, qs)" by (cases n)
  show ?thesis
  proof
    assume le: "le_default_dict m n"
    show "\<forall>x. default_dict_get m x \<le> default_dict_get n x"
    proof
      fix x
      show "default_dict_get m x \<le> default_dict_get n x"
      proof (cases "x \<in> set (map fst ps @ map fst qs)")
        case True
        with le show ?thesis unfolding m n
          by (auto simp: list_all_iff simp del: default_dict_get.simps)
      next
        case False
        then have "map_of ps x = None" "map_of qs x = None"
          by (simp_all add: map_of_resolved_none_iff)
        with le show ?thesis unfolding m n by simp
      qed
    qed
  next
    assume le: "\<forall>x. default_dict_get m x \<le> default_dict_get n x"
    obtain y :: vname where "y \<in> UNIV" and fresh: "y \<notin> set (map fst ps @ map fst qs)"
      by (rule obtain_fresh_vname[OF infinite_literal])
    then have "map_of ps y = None" "map_of qs y = None"
      by (simp_all add: map_of_resolved_none_iff)
    with le[rule_format, of y] have "d \<le> e" unfolding m n by simp
    with le show "le_default_dict m n" unfolding m n by (simp add: list_all_iff)
  qed
qed

subsection \<open>Locations and raw lookup\<close>

text \<open>
  A \<open>location\<close> names a local or a global variable, and a raw state is a
  pair of dictionaries read by \<open>default_st_rep_get\<close>.
\<close>

datatype location =
  Local_Location (location_vname: vname)
| Global_Location (location_vname: vname)

lemma all_location_iff:
  "(\<forall>loc. P loc) \<longleftrightarrow> (\<forall>x. P (Local_Location x)) \<and> (\<forall>x. P (Global_Location x))"
  by (metis location.exhaust)

text \<open>The local dictionary comes first, the global one second.\<close>

type_synonym 'a default_st_rep = "'a default_dict \<times> 'a default_dict"

fun default_st_rep_get ::
  "('a::bot) default_st_rep => location => 'a" where
  "default_st_rep_get (l, g) (Local_Location x) = default_dict_get l x"
| "default_st_rep_get (l, g) (Global_Location x) = default_dict_get g x"

subsection \<open>Extensional equality\<close>

text \<open>
  Two raw states are equal when they agree on every location's lookup, whatever
  their dictionaries look like; \<open>eq_default_st_rep\<close> is an equivalence.
\<close>

definition eq_default_st_rep ::
  "('a::bot) default_st_rep => 'a default_st_rep => bool"
where
  "eq_default_st_rep s t \<longleftrightarrow>
     default_st_rep_get s = default_st_rep_get t"

lemma equivp_eq_default_st_rep: "equivp eq_default_st_rep"
  unfolding eq_default_st_rep_def
  by (rule equivpI) (auto intro: reflpI sympI transpI)

text \<open>
  The two rules every congruence proof below goes through: a raw operation
  respects \<^const>\<open>eq_default_st_rep\<close> exactly when its lookup equation says the
  result depends on the arguments only through their lookups.  Stating that
  once keeps the individual congruence proofs down to their own lookup rules.
\<close>

lemma eq_default_st_repI [intro]:
  assumes "\<And>loc. default_st_rep_get s loc = default_st_rep_get t loc"
  shows "eq_default_st_rep s t"
  unfolding eq_default_st_rep_def fun_eq_iff using assms by blast

lemma eq_default_st_repD:
  assumes "eq_default_st_rep s t"
  shows "default_st_rep_get s loc = default_st_rep_get t loc"
  using assms unfolding eq_default_st_rep_def fun_eq_iff by blast

subsection \<open>Executable pointwise order\<close>

text \<open>
  \<open>le_default_st_rep_code\<close> compares both dictionaries with
  \<open>le_default_dict\<close> and is shown equal to the pointwise order on lookups.
\<close>

fun le_default_st_rep_code ::
  "('a::order_bot) default_st_rep => 'a default_st_rep => bool"
where
  "le_default_st_rep_code (l1, g1) (l2, g2) \<longleftrightarrow>
     le_default_dict l1 l2 \<and> le_default_dict g1 g2"

lemma le_default_st_rep_code_raw_iff:
  "le_default_st_rep_code (l1, g1) (l2, g2) \<longleftrightarrow>
    (\<forall>loc. default_st_rep_get (l1, g1) loc \<le>
      default_st_rep_get (l2, g2) loc)"
  by (simp add: all_location_iff le_default_dict_iff)

text \<open>
  The same characterization without the pair pattern, so that quotient-level
  statements can be discharged by \<open>transfer\<close> alone instead of re-opening both
  representatives.
\<close>

lemma le_default_st_rep_code_iff:
  "le_default_st_rep_code s t \<longleftrightarrow>
    (\<forall>loc. default_st_rep_get s loc \<le> default_st_rep_get t loc)"
  by (cases s; cases t) (simp add: all_location_iff le_default_dict_iff)


subsection \<open>The extensional quotient, lookup and point update\<close>

text \<open>
  \<open>default_st\<close> is the quotient of raw states by extensional equality.
  Lookup and point update lift to it because both respect the equivalence.
\<close>

quotient_type 'a default_st =
  "('a::bot) default_st_rep" / "eq_default_st_rep"
  morphisms rep_default_st Abs_default_st
  by (rule equivp_eq_default_st_rep)

lift_definition default_st_get ::
  "('a::bot) default_st => location => 'a"
  is default_st_rep_get
  by (simp add: eq_default_st_rep_def)

fun default_st_rep_set ::
  "('a::bot) default_st_rep => location => 'a => 'a default_st_rep" where
  "default_st_rep_set (l, g) (Local_Location x) a = (default_dict_set l x a, g)"
| "default_st_rep_set (l, g) (Global_Location x) a = (l, default_dict_set g x a)"

lemma default_st_rep_get_set [simp]:
  "default_st_rep_get (default_st_rep_set s loc a) loc' =
     (if loc = loc' then a else default_st_rep_get s loc')"
  by (cases s; cases loc; cases loc') simp_all

lemma eq_default_st_rep_set:
  assumes "eq_default_st_rep s t"
  shows "eq_default_st_rep (default_st_rep_set s loc a)
      (default_st_rep_set t loc a)"
  by (rule eq_default_st_repI) (simp add: eq_default_st_repD[OF assms])

lift_definition default_st_set ::
  "('a::bot) default_st => location => 'a => 'a default_st"
  is default_st_rep_set
  by (rule eq_default_st_rep_set)

text \<open>
  Lookup is written \<open>s\<langle>l\<rangle>\<close> and point update \<open>s\<langle>l := a\<rangle>\<close>. The notation is a
  bundle: every theory that uses it opens it after \<open>begin\<close> and closes it with
  \<open>unbundle no\<close> before \<open>end\<close>, so it never reaches an importing theory and
  never changes a term.
  Both forms bind tighter than application, so \<open>f s\<langle>l\<rangle>\<close> reads
  \<open>f (s\<langle>l\<rangle>)\<close> and updates chain as \<open>s\<langle>l := a\<rangle>\<langle>l'\<rangle>\<close>.
  The state with local dictionary \<open>(dl, ls)\<close> and global dictionary
  \<open>(dg, gs)\<close> is written \<open>\<llangle>(dl, ls), (dg, gs)\<rrangle>\<close>.
  Theories past \<open>default_st_to_fun\<close> open \<open>default_st_syntax\<close>,
  which adds the notation for the function a state represents to this bundle.
\<close>

abbreviation default_st_mk ::
  "('a::bot) default_dict => 'a default_dict => 'a default_st" where
  "default_st_mk l g \<equiv> Abs_default_st (l, g)"

bundle default_st_carrier_syntax
begin
notation default_st_get ("_\<langle>_\<rangle>" [1000, 0] 1000)
notation default_st_set ("_\<langle>_ :=/ _\<rangle>" [1000, 0, 0] 1000)
notation default_st_mk ("\<llangle>_,/ _\<rrangle>")
end

unbundle default_st_carrier_syntax

lemma default_st_get_Abs [simp]:
  "(Abs_default_st s)\<langle>loc\<rangle> = default_st_rep_get s loc"
  by transfer simp

lemma default_st_get_mk:
  "\<llangle>l, g\<rrangle>\<langle>loc\<rangle> =
     (case loc of
        Local_Location x => default_dict_get l x
      | Global_Location x => default_dict_get g x)"
  by (cases loc) simp_all

lemma Abs_default_st_rep_default_st [simp]:
  "Abs_default_st (rep_default_st s) = s"
  by (fact Lifting.Quotient_abs_rep [OF Quotient_default_st])

lemma default_st_get_rep:
  "s\<langle>loc\<rangle> = default_st_rep_get (rep_default_st s) loc"
  by (simp add: default_st_get.rep_eq)

text \<open>
  One lookup equation for the update, rather than a same/different pair: the
  conditional is what a caller has to reason about anyway, and the two special
  cases fall out of it by \<^term>\<open>simp\<close>.
\<close>

lemma default_st_get_set [simp]:
  "s\<langle>loc := a\<rangle>\<langle>loc'\<rangle> = (if loc = loc' then a else s\<langle>loc'\<rangle>)"
  by transfer simp

lemma default_st_eq_iff:
  "s = t \<longleftrightarrow>
     default_st_get s = default_st_get t"
  by transfer (simp add: eq_default_st_rep_def)

text \<open>
  The quotient-level counterpart of @{thm [source] eq_default_st_repI}: two
  quotient states are equal as soon as they look the same everywhere.  Left
  untagged -- as an \<open>[intro]\<close> rule it would attack every equation at this type
  by extensionality, which is rarely what a goal about a concrete state wants.
\<close>

lemma default_st_eqI:
  assumes "\<And>loc. s\<langle>loc\<rangle> = t\<langle>loc\<rangle>"
  shows "s = t"
  using assms by (simp add: default_st_eq_iff fun_eq_iff)


subsection \<open>Order, bottom and executable equality\<close>

text \<open>
  Bottom is the pair of empty dictionaries with bottom defaults; the order lifts
  \<open>le_default_st_rep_code\<close>, which also yields an executable equality.
\<close>

instantiation default_st :: (bot) bot
begin
definition bot_default_st ::
  "('a::bot) default_st"
where
  "bot_default_st = \<llangle>(bot, []), (bot, [])\<rrangle>"
instance ..
end

instantiation default_st :: (order_bot) ord
begin
lift_definition less_eq_default_st ::
  "('a::order_bot) default_st =>
   'a default_st => bool"
  is le_default_st_rep_code
  by (auto simp: le_default_st_rep_code_iff eq_default_st_rep_def)

definition less_default_st ::
  "('a::order_bot) default_st =>
   'a default_st => bool"
where
  "less_default_st s t \<longleftrightarrow>
     s \<le> t \<and> \<not> t \<le> s"

instance ..
end


lemma le_default_st_iff:
  fixes s t :: "('a::order_bot) default_st"
  shows "s \<le> t \<longleftrightarrow> (\<forall>loc. s\<langle>loc\<rangle> \<le> t\<langle>loc\<rangle>)"
  by transfer (rule le_default_st_rep_code_iff)


instance default_st :: (order_bot) order
proof intro_classes
  fix s t u :: "('a::order_bot) default_st"
  show "(s < t) \<longleftrightarrow> (s \<le> t \<and> \<not> t \<le> s)"
    by (simp add: less_default_st_def)

  show "s \<le> s"
    by (simp add: le_default_st_iff)
  show "s \<le> t \<Longrightarrow> t \<le> u \<Longrightarrow> s \<le> u"
    by (auto simp: le_default_st_iff intro: order_trans)
  show "s \<le> t \<Longrightarrow> t \<le> s \<Longrightarrow> s = t"
    by (auto simp: le_default_st_iff
      default_st_eq_iff fun_eq_iff intro: order_antisym)
qed

context
  includes lattice_syntax
begin

lemma default_st_get_bot [simp]:
  "(\<bottom> :: ('a::bot) default_st)\<langle>loc\<rangle> = \<bottom>"
  unfolding bot_default_st_def by (cases loc) simp_all

end


lemma bot_le_default_st:
  "(bot :: ('a::order_bot) default_st) \<le> s"
  by (simp add: le_default_st_iff)

instance default_st :: (order_bot) order_bot
  by standard (rule bot_le_default_st)
instantiation default_st :: ("{order_bot,equal}") equal
begin
definition equal_default_st ::
  "('a::{order_bot,equal}) default_st =>
   'a default_st => bool"
where
  "equal_default_st s t = (s \<le> t \<and> t \<le> s)"
instance
  by standard (auto simp: equal_default_st_def intro: order_antisym)
end

unbundle no default_st_carrier_syntax

end
