theory Default_St_Algebra
  imports Default_St_Base "Voblint_Domain.Abstract_Domain"
begin

unbundle default_st_carrier_syntax

section \<open>Pointwise abstract-domain operations\<close>

text \<open>
  Join, widening and narrowing are the same construction three times: apply an
  element operation to both dictionaries of a state, at the default and at
  every name either argument lists. This theory gives that construction once,
  instantiates it three times, and installs the lattice and warrowing classes
  the solver needs.

  The combinator's support is the two argument supports with duplicate keys
  removed. Keeping both copies would denote the same lookup function, but every
  join would concatenate, and a solver iteration would then grow the
  materialized list without bound while each lookup scans it.
\<close>

subsection \<open>The pointwise combinator\<close>

fun map2_default_dict ::
  "('a => 'a => 'a) => 'a default_dict => 'a default_dict => 'a default_dict"
where
  "map2_default_dict f (d1, ps1) (d2, ps2) =
     (f d1 d2,
      map (\<lambda>x. (x, f (default_dict_get (d1, ps1) x) (default_dict_get (d2, ps2) x)))
        (remdups (map fst ps1 @ map fst ps2)))"

fun map2_default_st_rep ::
  "('a => 'a => 'a) => ('a::bot) default_st_rep => 'a default_st_rep =>
   'a default_st_rep"
where
  "map2_default_st_rep f (l1, g1) (l2, g2) =
     (map2_default_dict f l1 l2, map2_default_dict f g1 g2)"

lemma map_of_map_key_list:
  "map_of (map (\<lambda>k. (k, g k)) ks) x =
     (if x \<in> set ks then Some (g x) else None)"
  by (induction ks) auto

lemma default_dict_get_map2 [simp]:
  "default_dict_get (map2_default_dict f m1 m2) x =
     f (default_dict_get m1 x) (default_dict_get m2 x)"
  by (cases m1; cases m2)
    (auto simp: map_of_map_key_list map_of_resolved_none_iff[THEN iffD2])

text \<open>
  From here on the combinator is read through its lookup equation. Its
  defining equation would otherwise unfold first and hide it from
  @{thm [source] default_dict_get_map2}.
\<close>

declare map2_default_dict.simps [simp del]

lemma default_st_rep_get_map2 [simp]:
  "default_st_rep_get (map2_default_st_rep f s t) loc =
     f (default_st_rep_get s loc) (default_st_rep_get t loc)"
  by (cases s; cases t; cases loc) simp_all

lemma eq_default_st_rep_map2:
  assumes "eq_default_st_rep s1 s2"
    and "eq_default_st_rep t1 t2"
  shows "eq_default_st_rep (map2_default_st_rep f s1 t1)
      (map2_default_st_rep f s2 t2)"
  by (rule eq_default_st_repI)
     (simp add: eq_default_st_repD[OF assms(1)] eq_default_st_repD[OF assms(2)])

subsection \<open>Join and semilattice structure\<close>

definition merge_default_st_rep ::
  "('a::bounded_semilattice_sup_bot) default_st_rep =>
   'a default_st_rep => 'a default_st_rep"
where
  "merge_default_st_rep s t = map2_default_st_rep (\<squnion>) s t"

lemma default_st_rep_get_merge [simp]:
  "default_st_rep_get (merge_default_st_rep s t) loc =
     default_st_rep_get s loc \<squnion> default_st_rep_get t loc"
  by (simp add: merge_default_st_rep_def)

lemma eq_default_st_rep_merge:
  assumes "eq_default_st_rep s1 s2"
    and "eq_default_st_rep t1 t2"
  shows "eq_default_st_rep (merge_default_st_rep s1 t1)
      (merge_default_st_rep s2 t2)"
  using assms unfolding merge_default_st_rep_def
  by (rule eq_default_st_rep_map2)

instantiation default_st ::
  (bounded_semilattice_sup_bot) sup
begin
lift_definition sup_default_st ::
  "('a::bounded_semilattice_sup_bot) default_st =>
   'a default_st => 'a default_st"
  is merge_default_st_rep
  by (rule eq_default_st_rep_merge)
instance ..
end

lemma default_st_get_sup [simp]:
  "(s \<squnion> t)\<langle>loc\<rangle> = s\<langle>loc\<rangle> \<squnion> t\<langle>loc\<rangle>"
  by transfer (rule default_st_rep_get_merge)

instance default_st ::
  (bounded_semilattice_sup_bot) semilattice_sup
proof intro_classes
  fix s t u :: "('a::bounded_semilattice_sup_bot) default_st"
  show "s \<le> s \<squnion> t"
    by (simp add: le_default_st_iff)
  show "t \<le> s \<squnion> t"
    by (simp add: le_default_st_iff)
  show "s \<le> u \<Longrightarrow> t \<le> u \<Longrightarrow> s \<squnion> t \<le> u"
    by (simp add: le_default_st_iff)
qed

instance default_st ::
  (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

subsection \<open>Widening and narrowing\<close>

definition widen_default_st_rep ::
  "('a::{bounded_semilattice_sup_bot, warrowing}) default_st_rep =>
   'a default_st_rep => 'a default_st_rep"
where
  "widen_default_st_rep s t = map2_default_st_rep (\<nabla>) s t"

lemma default_st_rep_get_widen [simp]:
  "default_st_rep_get (widen_default_st_rep s t) loc =
     default_st_rep_get s loc \<nabla> default_st_rep_get t loc"
  by (simp add: widen_default_st_rep_def)

lemma eq_default_st_rep_widen:
  assumes "eq_default_st_rep s1 s2"
    and "eq_default_st_rep t1 t2"
  shows "eq_default_st_rep (widen_default_st_rep s1 t1)
      (widen_default_st_rep s2 t2)"
  using assms unfolding widen_default_st_rep_def
  by (rule eq_default_st_rep_map2)

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

lift_definition widen_on_default_st ::
  "('a::{bounded_semilattice_sup_bot, warrowing}) default_st =>
   'a default_st => 'a default_st"
  is widen_default_st_rep
  by (rule eq_default_st_rep_widen)

lemma default_st_get_widen_on [simp]:
  "(widen_on_default_st s t)\<langle>loc\<rangle> =
     s\<langle>loc\<rangle> \<nabla> t\<langle>loc\<rangle>"
  by transfer (rule default_st_rep_get_widen)

instantiation default_st :: ("{bounded_semilattice_sup_bot, warrowing}") widening
begin
definition widen_default_st ::
  "('a::{bounded_semilattice_sup_bot, warrowing}) default_st =>
   'a default_st => 'a default_st"
where
  "widen_default_st s t = widen_on_default_st s t"
instance
proof
  fix a b :: "('a::{bounded_semilattice_sup_bot, warrowing}) default_st"
  show "a \<le> (a \<nabla> b)"
    by (simp add: le_default_st_iff widen_default_st_def widen_ge1)
  show "b \<le> (a \<nabla> b)"
    by (simp add: le_default_st_iff widen_default_st_def widen_ge2)
qed
end

lemma default_st_get_widen [simp]:
  "(s \<nabla> t)\<langle>loc\<rangle> = s\<langle>loc\<rangle> \<nabla> t\<langle>loc\<rangle>"
  by (simp add: widen_default_st_def)

definition narrow_default_st_rep ::
  "('a::{bounded_semilattice_sup_bot, warrowing}) default_st_rep =>
   'a default_st_rep => 'a default_st_rep"
where
  "narrow_default_st_rep s t = map2_default_st_rep (\<Delta>) s t"

lemma default_st_rep_get_narrow [simp]:
  "default_st_rep_get (narrow_default_st_rep s t) loc =
     default_st_rep_get s loc \<Delta> default_st_rep_get t loc"
  by (simp add: narrow_default_st_rep_def)

lemma eq_default_st_rep_narrow:
  assumes "eq_default_st_rep s1 s2"
    and "eq_default_st_rep t1 t2"
  shows "eq_default_st_rep (narrow_default_st_rep s1 t1)
      (narrow_default_st_rep s2 t2)"
  using assms unfolding narrow_default_st_rep_def
  by (rule eq_default_st_rep_map2)

lift_definition narrow_on_default_st ::
  "('a::{bounded_semilattice_sup_bot, warrowing}) default_st =>
   'a default_st => 'a default_st"
  is narrow_default_st_rep
  by (rule eq_default_st_rep_narrow)

lemma default_st_get_narrow_on [simp]:
  "(narrow_on_default_st s t)\<langle>loc\<rangle> =
     s\<langle>loc\<rangle> \<Delta> t\<langle>loc\<rangle>"
  by transfer (rule default_st_rep_get_narrow)

instantiation default_st :: ("{bounded_semilattice_sup_bot, warrowing}") narrowing
begin
definition narrow_default_st ::
  "('a::{bounded_semilattice_sup_bot, warrowing}) default_st =>
   'a default_st => 'a default_st"
where
  "narrow_default_st s t = narrow_on_default_st s t"
instance
  by standard
     (auto simp add: le_default_st_iff narrow_default_st_def
       intro: narrow_ge narrow_le)
end

lemma default_st_get_narrow [simp]:
  "(s \<Delta> t)\<langle>loc\<rangle> = s\<langle>loc\<rangle> \<Delta> t\<langle>loc\<rangle>"
  by (simp add: narrow_default_st_def)

instance default_st :: ("{bounded_semilattice_sup_bot, warrowing}") warrowing ..

unbundle no default_st_carrier_syntax

end
