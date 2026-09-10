theory Exec_St_Algebra
  imports Exec_St_Base "Voblint_Domain.Abstract_Domain"
begin

section \<open>Pointwise abstract-domain operations\<close>

text \<open>
  Join, widening and narrowing are the same construction three times: apply an
  element operation at both defaults and at every location listed by either
  argument. This theory gives that construction once, instantiates it three
  times, and installs the lattice and warrowing classes the solver needs.

  The combinator's support is the two argument supports with duplicate keys
  removed. Keeping both copies would denote the same lookup function, but every
  join would concatenate, and a solver iteration would then grow the
  materialized list without bound while each lookup scans it.
\<close>

subsection \<open>Finite binary support and the pointwise combinator\<close>

fun support2_resolved_st ::
  "('a::bot) resolved_st => 'a resolved_st => location list" where
  "support2_resolved_st (_, _, ps1) (_, _, ps2) =
     remdups (map fst ps1 @ map fst ps2)"

fun map2_resolved_st ::
  "('a => 'a => 'a) => ('a::bot) resolved_st => 'a resolved_st =>
   'a resolved_st"
where
  "map2_resolved_st f (dl1, dg1, ps1) (dl2, dg2, ps2) =
     (f dl1 dl2, f dg1 dg2,
      map (\<lambda>loc. (loc,
        f (lookup_resolved_st (dl1, dg1, ps1) loc)
          (lookup_resolved_st (dl2, dg2, ps2) loc)))
        (support2_resolved_st (dl1, dg1, ps1) (dl2, dg2, ps2)))"

lemma map_of_map_key_list:
  "map_of (map (\<lambda>k. (k, g k)) ks) x =
     (if x \<in> set ks then Some (g x) else None)"
  by (induction ks) auto

lemma lookup_map2_resolved_st [simp]:
  "lookup_resolved_st (map2_resolved_st f s t) loc =
     f (lookup_resolved_st s loc) (lookup_resolved_st t loc)"
  by (cases s rule: prod_cases3, cases t rule: prod_cases3, cases loc)
    (auto simp: map_of_map_key_list map_of_resolved_none_iff[THEN iffD2])

lemma eq_resolved_st_map2:
  assumes "eq_resolved_st s1 s2"
    and "eq_resolved_st t1 t2"
  shows "eq_resolved_st (map2_resolved_st f s1 t1)
      (map2_resolved_st f s2 t2)"
  by (rule eq_resolved_stI)
     (simp add: eq_resolved_stD[OF assms(1)] eq_resolved_stD[OF assms(2)])

subsection \<open>Join and semilattice structure\<close>

definition merge_resolved_st ::
  "('a::bounded_semilattice_sup_bot) resolved_st =>
   'a resolved_st => 'a resolved_st"
where
  "merge_resolved_st s t = map2_resolved_st (\<squnion>) s t"

lemma lookup_merge_resolved_st [simp]:
  "lookup_resolved_st (merge_resolved_st s t) loc =
     lookup_resolved_st s loc \<squnion> lookup_resolved_st t loc"
  by (simp add: merge_resolved_st_def)

lemma eq_resolved_st_merge:
  assumes "eq_resolved_st s1 s2"
    and "eq_resolved_st t1 t2"
  shows "eq_resolved_st (merge_resolved_st s1 t1)
      (merge_resolved_st s2 t2)"
  using assms unfolding merge_resolved_st_def
  by (rule eq_resolved_st_map2)

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

subsection \<open>Widening and narrowing\<close>

definition widen_resolved_st ::
  "('a::bounded_warrowing) resolved_st =>
   'a resolved_st => 'a resolved_st"
where
  "widen_resolved_st s t = map2_resolved_st (\<nabla>) s t"

lemma lookup_widen_resolved_st [simp]:
  "lookup_resolved_st (widen_resolved_st s t) loc =
     lookup_resolved_st s loc \<nabla> lookup_resolved_st t loc"
  by (simp add: widen_resolved_st_def)

lemma eq_resolved_st_widen:
  assumes "eq_resolved_st s1 s2"
    and "eq_resolved_st t1 t2"
  shows "eq_resolved_st (widen_resolved_st s1 t1)
      (widen_resolved_st s2 t2)"
  using assms unfolding widen_resolved_st_def
  by (rule eq_resolved_st_map2)

text \<open>
  Widening and narrowing are lifted to a named constant first and only then
  installed as the class operation, unlike \<^const>\<open>sup\<close> which is lifted inside
  its own \<open>instantiation\<close>.  The detour is forced: the \<open>widening\<close> and
  \<open>narrowing\<close> classes carry axioms, so their \<open>instance\<close> proofs need the lookup
  equation, and inside an \<open>instantiation\<close> block the class operation is not yet
  the same term as a constant lifted there -- a lookup lemma stated on the
  latter fails to refine a goal about the former, and one proved before
  \<open>instance\<close> abstracts over the operation instead of fixing it.  \<^const>\<open>sup\<close>
  escapes this because the bare \<open>sup\<close> class has no axioms to discharge.
\<close>

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

definition narrow_resolved_st ::
  "('a::bounded_warrowing) resolved_st =>
   'a resolved_st => 'a resolved_st"
where
  "narrow_resolved_st s t = map2_resolved_st (\<Delta>) s t"

lemma lookup_narrow_resolved_st [simp]:
  "lookup_resolved_st (narrow_resolved_st s t) loc =
     lookup_resolved_st s loc \<Delta> lookup_resolved_st t loc"
  by (simp add: narrow_resolved_st_def)

lemma eq_resolved_st_narrow:
  assumes "eq_resolved_st s1 s2"
    and "eq_resolved_st t1 t2"
  shows "eq_resolved_st (narrow_resolved_st s1 t1)
      (narrow_resolved_st s2 t2)"
  using assms unfolding narrow_resolved_st_def
  by (rule eq_resolved_st_map2)

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

lemma lookup_narrow_resolved_st_q [simp]:
  "lookup_resolved_st_q (s \<Delta> t) loc =
     lookup_resolved_st_q s loc \<Delta> lookup_resolved_st_q t loc"
  by (simp add: narrow_resolved_st_q_def)

instance resolved_st_q :: (bounded_warrowing) warrowing ..


instance resolved_st_q :: (bounded_warrowing) bounded_warrowing ..

end
