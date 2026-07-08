theory Origin_State
  imports Exec_St
begin

section \<open>Origin-indexed abstract state\<close>

text \<open>
  \<open>('a, 'b) origin_st\<close> stores one abstract value (type \<open>'b\<close>) per \<^emph>\<open>origin\<close> (type \<open>'a\<close>)
  --- the site that produced a contribution to a shared slot.  It is the data structure
  behind \<^emph>\<open>per-origin widening\<close>: instead of merging every contribution into one cell and
  widening the merge (which climbs unbounded on a monotone recursion), each origin keeps
  its own cell, widening acts pointwise per origin, and a read collapses the cells with
  \<open>\<squnion>\<close>.

  The representation mirrors \<^typ>\<open>'a st\<close> (association list with an implicit default),
  but the default is fixed to \<^term>\<open>\<bottom>\<close>: an origin never written holds \<^term>\<open>\<bottom>\<close>,
  so the observable value is a finite join over the written origins and the order needs
  no infinitude side condition.  The value type \<open>'b\<close> is the second parameter so that the
  alphabetically-ordered class arities (\<open>(type, \<dots>)\<close>) constrain it.  The type is kept
  completely independent of the solver: a plain abstract domain with the same instance
  stack as \<^typ>\<open>'a st\<close>.
\<close>

lemma narrow_bot_bot: "(\<bottom>::'a::bounded_warrowing) \<Delta> \<bottom> = \<bottom>"
  by (metis narrow_le order.antisym order_refl bot.extremum)

subsection \<open>Representation: association list with implicit bottom default\<close>

type_synonym ('a, 'b) origin_rep = "('a \<times> 'b) list"

fun fun_rep_origin :: "('a \<times> 'b::bot) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "fun_rep_origin ps = (\<lambda>k. case map_of ps k of Some a \<Rightarrow> a | None \<Rightarrow> \<bottom>)"

lemma fun_rep_origin_notin [simp]:
  "k \<notin> set (map fst ps) \<Longrightarrow> fun_rep_origin ps k = \<bottom>"
proof -
  assume "k \<notin> set (map fst ps)"
  then have "map_of ps k = None" by (simp add: map_of_eq_None_iff)
  then show ?thesis by simp
qed

definition eq_origin :: "('a \<times> 'b::bot) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" where
  "eq_origin s1 s2 \<longleftrightarrow> fun_rep_origin s1 = fun_rep_origin s2"

lemma equivp_eq_origin: "equivp eq_origin"
  unfolding eq_origin_def by (rule equivpI) (auto intro: reflpI sympI transpI)

declare [[typedef_overloaded]]
quotient_type ('a, 'b) origin_st = "('a \<times> 'b::bot) list" / "eq_origin"
  morphisms rep_origin Abs_origin
  by (rule equivp_eq_origin)

subsection \<open>Lookup, single-origin update, and the empty map\<close>

lift_definition lookup_origin :: "('a, 'b::bot) origin_st \<Rightarrow> 'a \<Rightarrow> 'b"
  is fun_rep_origin by (simp add: eq_origin_def)

lift_definition update_origin :: "('a, 'b::bot) origin_st \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) origin_st"
  is "\<lambda>ps k a. (k, a) # ps"
  by (auto simp: eq_origin_def fun_eq_iff)

text \<open>A nullary constant cannot be lifted inside an \<^theory_text>\<open>instantiation\<close> block for this
  two-parameter quotient, so the empty map is lifted here and \<open>\<bottom>\<close> is defined from it.\<close>
lift_definition empty_origin :: "('a, 'b::bot) origin_st" is "[] :: ('a \<times> 'b) list" .

lemma lookup_update_origin_same [simp]: "lookup_origin (update_origin s k a) k = a"
  by transfer simp

lemma lookup_update_origin_diff [simp]:
  "k \<noteq> j \<Longrightarrow> lookup_origin (update_origin s k a) j = lookup_origin s j"
  by transfer simp

lemma lookup_empty_origin [simp]: "lookup_origin empty_origin k = \<bottom>"
  by transfer simp

subsection \<open>Bottom\<close>

instantiation origin_st :: (type, bot) bot begin
definition bot_origin_st_def: "bot = empty_origin"
instance ..
end

lemma lookup_bot_origin [simp]: "lookup_origin (\<bottom> :: ('a, 'b::bot) origin_st) k = \<bottom>"
  unfolding bot_origin_st_def by simp

subsection \<open>Order\<close>

fun less_eq_origin_rep :: "('a \<times> 'b::order_bot) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" where
  "less_eq_origin_rep ps1 ps2 \<longleftrightarrow>
     (\<forall>k \<in> set (map fst ps1) \<union> set (map fst ps2).
        fun_rep_origin ps1 k \<le> fun_rep_origin ps2 k)"

lemma less_eq_origin_rep_iff:
  "less_eq_origin_rep ps1 ps2 \<longleftrightarrow> (\<forall>k. fun_rep_origin ps1 k \<le> fun_rep_origin ps2 k)"
proof
  assume H: "less_eq_origin_rep ps1 ps2"
  show "\<forall>k. fun_rep_origin ps1 k \<le> fun_rep_origin ps2 k"
  proof
    fix k show "fun_rep_origin ps1 k \<le> fun_rep_origin ps2 k"
    proof (cases "k \<in> set (map fst ps1) \<union> set (map fst ps2)")
      case True then show ?thesis using H by auto
    next
      case False
      then have "map_of ps1 k = None" "map_of ps2 k = None" by (auto simp: map_of_eq_None_iff)
      then show ?thesis by simp
    qed
  qed
qed auto

instantiation origin_st :: (type, order_bot) ord begin
lift_definition less_eq_origin_st :: "('a, 'b) origin_st \<Rightarrow> ('a, 'b) origin_st \<Rightarrow> bool"
  is less_eq_origin_rep
  by (simp add: eq_origin_def less_eq_origin_rep_iff del: less_eq_origin_rep.simps)
definition less_origin_st_def: "(s :: ('a, 'b) origin_st) < t \<longleftrightarrow> s \<le> t \<and> \<not> t \<le> s"
instance ..
end

lemma le_origin_iff: "(s \<le> t) \<longleftrightarrow> (\<forall>k. lookup_origin s k \<le> lookup_origin t k)"
  by transfer (rule less_eq_origin_rep_iff)

lemma origin_eqI:
  assumes "\<And>k. lookup_origin s k = lookup_origin t k"
  shows "s = t"
  using assms by transfer (simp add: eq_origin_def fun_eq_iff)

instance origin_st :: (type, order_bot) order
proof
  fix s t u :: "('a, 'b::order_bot) origin_st"
  show "(s < t) \<longleftrightarrow> (s \<le> t \<and> \<not> t \<le> s)" by (simp add: less_origin_st_def)
  show "s \<le> s" by (simp add: le_origin_iff)
  show "s \<le> t \<Longrightarrow> t \<le> u \<Longrightarrow> s \<le> u" by (auto simp: le_origin_iff intro: order_trans)
  show "s \<le> t \<Longrightarrow> t \<le> s \<Longrightarrow> s = t"
    by (metis le_origin_iff origin_eqI order_antisym)
qed

lemma bot_le_origin: "(\<bottom> :: ('a, 'b::order_bot) origin_st) \<le> s"
  by (simp add: le_origin_iff)

instance origin_st :: (type, order_bot) order_bot
  by standard (rule bot_le_origin)

subsection \<open>Join\<close>

fun merge_origin_rep ::
  "('a \<times> 'b::bounded_semilattice_sup_bot) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "merge_origin_rep ps1 ps2 =
     map (\<lambda>(k, _). (k, fun_rep_origin ps1 k \<squnion> fun_rep_origin ps2 k)) (ps1 @ ps2)"

lemma fun_rep_merge_origin_rep [simp]:
  "fun_rep_origin (merge_origin_rep ps1 ps2) =
   (\<lambda>k. fun_rep_origin ps1 k \<squnion> fun_rep_origin ps2 k)"
proof (rule ext)
  fix k
  show "fun_rep_origin (merge_origin_rep ps1 ps2) k
        = fun_rep_origin ps1 k \<squnion> fun_rep_origin ps2 k"
  proof (cases "k \<in> set (map fst ps1) \<union> set (map fst ps2)")
    case True then show ?thesis by (simp add: map_of_merge_pair)
  next
    case False
    then have "map_of ps1 k = None" "map_of ps2 k = None" by (auto simp: map_of_eq_None_iff)
    with False show ?thesis by (simp add: map_of_merge_pair split: if_splits)
  qed
qed

instantiation origin_st :: (type, bounded_semilattice_sup_bot) sup begin
lift_definition sup_origin_st ::
  "('a, 'b) origin_st \<Rightarrow> ('a, 'b) origin_st \<Rightarrow> ('a, 'b) origin_st"
  is merge_origin_rep
  by (simp add: eq_origin_def del: fun_rep_origin.simps merge_origin_rep.simps)
instance ..
end

lemma lookup_sup_origin [simp]:
  "lookup_origin (s \<squnion> t) k = lookup_origin s k \<squnion> lookup_origin t k"
  by transfer (simp del: fun_rep_origin.simps merge_origin_rep.simps)

instance origin_st :: (type, bounded_semilattice_sup_bot) semilattice_sup
proof
  fix s t u :: "('a, 'b::bounded_semilattice_sup_bot) origin_st"
  show "s \<le> s \<squnion> t" by (simp add: le_origin_iff)
  show "t \<le> s \<squnion> t" by (simp add: le_origin_iff)
  show "s \<le> u \<Longrightarrow> t \<le> u \<Longrightarrow> s \<squnion> t \<le> u" by (simp add: le_origin_iff)
qed

instance origin_st :: (type, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

subsection \<open>Equality via antisymmetry (executable)\<close>

instantiation origin_st :: (type, bounded_semilattice_sup_bot) equal begin
definition equal_origin_st_def:
  "equal_class.equal (s :: ('a, 'b) origin_st) t \<longleftrightarrow> s \<le> t \<and> t \<le> s"
instance
proof
  fix s t :: "('a, 'b) origin_st"
  show "equal_class.equal s t \<longleftrightarrow> (s = t)"
    unfolding equal_origin_st_def by (meson antisym order_refl)
qed
end

subsection \<open>Pointwise narrowing\<close>

fun narrow_origin_rep ::
  "('a \<times> 'b::bounded_warrowing) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "narrow_origin_rep ps1 ps2 =
     map (\<lambda>(k, _). (k, fun_rep_origin ps1 k \<Delta> fun_rep_origin ps2 k)) (ps1 @ ps2)"

lemma fun_rep_narrow_origin_rep:
  "fun_rep_origin (narrow_origin_rep ps1 ps2) =
   (\<lambda>k. fun_rep_origin ps1 k \<Delta> fun_rep_origin ps2 k)"
proof (rule ext)
  fix k
  show "fun_rep_origin (narrow_origin_rep ps1 ps2) k
        = fun_rep_origin ps1 k \<Delta> fun_rep_origin ps2 k"
  proof (cases "k \<in> set (map fst ps1) \<union> set (map fst ps2)")
    case True then show ?thesis by (simp add: map_of_merge_pair)
  next
    case False
    then have "map_of ps1 k = None" "map_of ps2 k = None" by (auto simp: map_of_eq_None_iff)
    with False show ?thesis by (simp add: map_of_merge_pair narrow_bot_bot split: if_splits)
  qed
qed

subsection \<open>Widening, guarded so an all-bottom cell stays bottom\<close>

text \<open>
  Pointwise widening is only well defined on the quotient if an origin that is
  \<^term>\<open>\<bottom>\<close> in both operands stays \<^term>\<open>\<bottom>\<close> (two equal maps may list different explicit
  \<^term>\<open>\<bottom>\<close> cells, and \<open>\<bottom> \<nabla> \<bottom>\<close> need not be \<open>\<bottom>\<close>).  So the widen only touches origins
  that are non-bottom in at least one operand; on those the ordinary domain widening
  runs.  Termination is unaffected: the active-origin set is finite and only grows.
\<close>

lemma map_of_map_key:
  "map_of (map (\<lambda>k. (k, g k)) ks) x = (if x \<in> set ks then Some (g x) else None)"
  by (induction ks) auto

fun widen_origin_rep ::
  "('a \<times> 'b::bounded_warrowing) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "widen_origin_rep ps1 ps2 =
     map (\<lambda>k. (k, fun_rep_origin ps1 k \<nabla> fun_rep_origin ps2 k))
         (filter (\<lambda>k. fun_rep_origin ps1 k \<noteq> \<bottom> \<or> fun_rep_origin ps2 k \<noteq> \<bottom>)
                 (remdups (map fst ps1 @ map fst ps2)))"

lemma fun_rep_widen_origin_rep:
  "fun_rep_origin (widen_origin_rep ps1 ps2) k =
   (if fun_rep_origin ps1 k = \<bottom> \<and> fun_rep_origin ps2 k = \<bottom> then \<bottom>
    else fun_rep_origin ps1 k \<nabla> fun_rep_origin ps2 k)"
proof -
  let ?P = "\<lambda>k. fun_rep_origin ps1 k \<noteq> \<bottom> \<or> fun_rep_origin ps2 k \<noteq> \<bottom>"
  let ?ks = "filter ?P (remdups (map fst ps1 @ map fst ps2))"
  have mem: "k \<in> set ?ks \<longleftrightarrow> ?P k"
  proof
    assume "?P k"
    then have "k \<in> set (map fst ps1 @ map fst ps2)" using fun_rep_origin_notin by fastforce
    with \<open>?P k\<close> show "k \<in> set ?ks" by simp
  qed simp
  have "fun_rep_origin (widen_origin_rep ps1 ps2) k
        = (if k \<in> set ?ks then fun_rep_origin ps1 k \<nabla> fun_rep_origin ps2 k else \<bottom>)"
    by (simp add: map_of_map_key)
  then show ?thesis using mem by auto
qed

lift_definition widen_on_origin ::
  "('a, 'b::bounded_warrowing) origin_st \<Rightarrow> ('a, 'b) origin_st \<Rightarrow> ('a, 'b) origin_st"
  is widen_origin_rep
  by (simp add: eq_origin_def fun_rep_widen_origin_rep fun_eq_iff
           del: fun_rep_origin.simps widen_origin_rep.simps)

lift_definition narrow_on_origin ::
  "('a, 'b::bounded_warrowing) origin_st \<Rightarrow> ('a, 'b) origin_st \<Rightarrow> ('a, 'b) origin_st"
  is narrow_origin_rep
  by (simp add: eq_origin_def fun_rep_narrow_origin_rep fun_eq_iff
           del: fun_rep_origin.simps narrow_origin_rep.simps)

lemma lookup_widen_on_origin:
  "lookup_origin (widen_on_origin s t) k =
   (if lookup_origin s k = \<bottom> \<and> lookup_origin t k = \<bottom> then \<bottom>
    else lookup_origin s k \<nabla> lookup_origin t k)"
  by transfer (rule fun_rep_widen_origin_rep)

lemma lookup_narrow_on_origin [simp]:
  "lookup_origin (narrow_on_origin s t) k = lookup_origin s k \<Delta> lookup_origin t k"
  by transfer (simp add: fun_rep_narrow_origin_rep del: fun_rep_origin.simps narrow_origin_rep.simps)

instantiation origin_st :: (type, bounded_warrowing) widening begin
definition widen_origin_st_def: "widen (s :: ('a, 'b) origin_st) t = widen_on_origin s t"
instance
proof
  fix a b :: "('a, 'b::bounded_warrowing) origin_st"
  show "a \<le> widen a b"
    unfolding widen_origin_st_def le_origin_iff
    by (auto simp: lookup_widen_on_origin intro: widen_ge1)
  show "b \<le> widen a b"
    unfolding widen_origin_st_def le_origin_iff
    by (auto simp: lookup_widen_on_origin intro: widen_ge2)
qed
end

instantiation origin_st :: (type, bounded_warrowing) narrowing begin
definition narrow_origin_st_def: "narrow (s :: ('a, 'b) origin_st) t = narrow_on_origin s t"
instance
proof
  fix a b :: "('a, 'b::bounded_warrowing) origin_st"
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b"
    unfolding narrow_origin_st_def le_origin_iff
    by (auto intro: narrow_ge simp: le_origin_iff)
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a"
    unfolding narrow_origin_st_def le_origin_iff
    by (auto intro: narrow_le simp: le_origin_iff)
qed
end

lemma lookup_narrow_origin [simp]:
  "lookup_origin (s \<Delta> t) k = lookup_origin s k \<Delta> lookup_origin t k"
  unfolding narrow_origin_st_def by simp

instance origin_st :: (type, bounded_warrowing) warrowing ..

subsection \<open>Collapse: the observable value is the join over all origins\<close>

text \<open>
  \<open>collapse_origins\<close> is the join of every origin cell.  Because an unwritten origin
  holds \<^term>\<open>\<bottom>\<close>, it is a finite fold over the written cells, evaluated through
  \<^const>\<open>fun_rep_origin\<close> so that shadowed duplicate keys never inflate the result ---
  which is what makes it well defined on the quotient.
\<close>

definition sup_list :: "'b::bounded_semilattice_sup_bot list \<Rightarrow> 'b" where
  "sup_list xs = foldr (\<squnion>) xs \<bottom>"

lemma sup_list_ge: "x \<in> set xs \<Longrightarrow> x \<le> sup_list xs"
  unfolding sup_list_def
  by (induction xs) (auto intro: le_supI1 le_supI2)

lemma sup_list_le: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<le> z) \<Longrightarrow> sup_list xs \<le> z"
  unfolding sup_list_def
  by (induction xs) auto

definition collapse_origin_rep :: "('a \<times> 'b::bounded_semilattice_sup_bot) list \<Rightarrow> 'b" where
  "collapse_origin_rep ps = sup_list (map (fun_rep_origin ps) (map fst ps))"

lemma fun_rep_le_collapse_rep:
  "fun_rep_origin ps k \<le> collapse_origin_rep ps"
proof (cases "k \<in> set (map fst ps)")
  case True
  then have "fun_rep_origin ps k \<in> set (map (fun_rep_origin ps) (map fst ps))" by auto
  then show ?thesis unfolding collapse_origin_rep_def by (rule sup_list_ge)
next
  case False
  then have "map_of ps k = None" by (simp add: map_of_eq_None_iff)
  then show ?thesis by simp
qed

lemma collapse_rep_le:
  "(\<And>k. fun_rep_origin ps k \<le> z) \<Longrightarrow> collapse_origin_rep ps \<le> z"
  unfolding collapse_origin_rep_def by (rule sup_list_le) auto

lemma collapse_origin_rep_cong:
  "eq_origin ps1 ps2 \<Longrightarrow> collapse_origin_rep ps1 = collapse_origin_rep ps2"
  unfolding eq_origin_def
  by (metis (no_types, lifting) fun_rep_le_collapse_rep collapse_rep_le order_antisym)

lift_definition collapse_origins ::
  "('a, 'b::bounded_semilattice_sup_bot) origin_st \<Rightarrow> 'b"
  is collapse_origin_rep
  by (rule collapse_origin_rep_cong)

lemma lookup_le_collapse: "lookup_origin s k \<le> collapse_origins s"
  by transfer (rule fun_rep_le_collapse_rep)

lemma collapse_least: "(\<And>k. lookup_origin s k \<le> z) \<Longrightarrow> collapse_origins s \<le> z"
  by transfer (rule collapse_rep_le)

subsection \<open>Stage 2 algebra: the properties per-origin widening relies on\<close>

lemma collapse_bot [simp]:
  "collapse_origins (\<bottom> :: ('a, 'b::bounded_semilattice_sup_bot) origin_st) = \<bottom>"
  by (rule antisym[OF collapse_least]) (simp_all add: lookup_le_collapse)

text \<open>Collapse is monotone: a larger origin map has a larger observable value.\<close>
lemma collapse_mono: "s \<le> t \<Longrightarrow> collapse_origins s \<le> collapse_origins t"
  by (rule collapse_least) (meson le_origin_iff lookup_le_collapse order_trans)

text \<open>Collapse is a join homomorphism.\<close>
lemma collapse_sup: "collapse_origins (s \<squnion> t) = collapse_origins s \<squnion> collapse_origins t"
proof (rule antisym)
  show "collapse_origins (s \<squnion> t) \<le> collapse_origins s \<squnion> collapse_origins t"
    by (rule collapse_least) (metis lookup_sup_origin lookup_le_collapse sup_mono)
  show "collapse_origins s \<squnion> collapse_origins t \<le> collapse_origins (s \<squnion> t)"
    by (simp add: collapse_mono)
qed

text \<open>Updating one origin soundly over-approximates the inserted value on read.\<close>
lemma inserted_le_collapse_update: "a \<le> collapse_origins (update_origin s k a)"
  by (metis lookup_update_origin_same lookup_le_collapse)

text \<open>Widening is extensive on both arguments (from the \<^class>\<open>widening\<close> instance).\<close>
lemma origin_widen_ge1: "(a :: ('a, 'b::bounded_warrowing) origin_st) \<le> a \<nabla> b"
  by (rule widen_ge1)
lemma origin_widen_ge2: "(b :: ('a, 'b::bounded_warrowing) origin_st) \<le> a \<nabla> b"
  by (rule widen_ge2)

end
