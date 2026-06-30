theory Exec_St
  imports Abstract_Domain "TD.Update_rules" "Voblint_IMP2.IMP2_Globals"
begin

class bounded_widening = bounded_semilattice_sup_bot + widening
class bounded_narrowing = bounded_semilattice_sup_bot + narrowing
class bounded_warrowing = bounded_semilattice_sup_bot + warrowing

section \<open>Executable abstract state: two-region explicit-default association list\<close>

text \<open>
  \<open>'a st\<close> is the executable representation of the abstract state \<open>vname => 'a\<close>
  (the \<open>'a abs_state\<close> of Abstract_Domain) for any value domain
  \<open>'a :: bounded_semilattice_sup_bot\<close>.  A state is a triple
  \<open>(dl, dg, ps)\<close>: a default for local variables, a default for global
  variables, and a finite list of explicit per-variable overrides.

  The two region-defaults are essential.  The locals/globals partition
  (@{const is_global}) splits \<open>vname\<close> into two *infinite* classes, and the
  pipeline routinely needs states that are uniform-but-different on the two
  classes: the sound input seed \<open>s0 = (\<lambda>_. top)\<close> is \<open>(top, top, [])\<close>;
  @{term \<open>restrict_local s\<close>} is \<open>bot\<close> on every global and \<open>s\<close> on every local;
  @{term \<open>restrict_global s\<close>} the converse.  A single hardwired default (the
  earlier \<open>bot\<close>-only design) cannot represent any of these with non-empty
  concretization, because \<open>gamma (bot) = {}\<close> forces \<open>gamma_state = {}\<close> on any
  cofinitely-\<open>bot\<close> state.

  Instances: order, bounded_semilattice_sup_bot, equal (via antisymmetry),
  widening / narrowing / warrowing pointwise on the value domain.
\<close>

subsection \<open>Underlying association list representation\<close>

type_synonym 'a st_rep = "'a \<times> 'a \<times> (vname \<times> 'a) list"

fun fun_rep_st :: "('a::bot) st_rep \<Rightarrow> vname \<Rightarrow> 'a" where
  "fun_rep_st (dl, dg, ps) =
     (\<lambda>x. case map_of ps x of Some a \<Rightarrow> a
                            | None \<Rightarrow> (if is_global x then dg else dl))"

lemma fun_rep_st_Cons:
  "fun_rep_st (dl, dg, (x, a) # ps) = (fun_rep_st (dl, dg, ps))(x := a)"
  by (rule ext) auto

definition eq_st :: "('a::bot) st_rep \<Rightarrow> 'a st_rep \<Rightarrow> bool" where
  "eq_st s1 s2 \<longleftrightarrow> fun_rep_st s1 = fun_rep_st s2"

lemma equivp_eq_st: "equivp eq_st"
  unfolding eq_st_def
  by (rule equivpI) (auto intro: reflpI sympI transpI)

declare [[typedef_overloaded]]
quotient_type 'a st = "('a::bot) st_rep" / "eq_st"
  morphisms rep_st Abs_st
  by (rule equivp_eq_st)

subsection \<open>Core operations\<close>

lift_definition lookup_st :: "('a::bot) st \<Rightarrow> vname \<Rightarrow> 'a"
  is fun_rep_st
  by (simp add: eq_st_def)

lift_definition update_st :: "('a::bot) st \<Rightarrow> vname \<Rightarrow> 'a \<Rightarrow> 'a st"
  is "\<lambda>(dl, dg, ps) x a. (dl, dg, (x, a) # ps)"
  by (auto simp: eq_st_def fun_eq_iff)

lemma lookup_update_same [simp]: "lookup_st (update_st s x a) x = a"
  by transfer (auto split: prod.split)

lemma lookup_update_diff [simp]: "x \<noteq> y \<Longrightarrow> lookup_st (update_st s x a) y = lookup_st s y"
  by transfer (auto split: prod.split)

subsection \<open>Infinitely many local and global variable names\<close>

text \<open>
  Both regions of the @{const is_global} partition are infinite, so outside any
  finite set of keys there is always a local and a global witness.  These power
  the per-region default comparison in the order below.
\<close>

lemma infinite_nonglobal_vnames: "infinite {x::vname. \<not> is_global x}"
proof -
  have inj: "inj (\<lambda>n::nat. replicate (Suc n) (CHR ''a''))"
    by (rule injI) (metis length_replicate nat.inject)
  have sub: "range (\<lambda>n::nat. replicate (Suc n) (CHR ''a'')) \<subseteq> {x. \<not> is_global x}"
    by (auto simp: is_global_def)
  have "infinite (range (\<lambda>n::nat. replicate (Suc n) (CHR ''a'')))"
  proof
    assume "finite (range (\<lambda>n::nat. replicate (Suc n) (CHR ''a'')))"
    then have "finite (UNIV::nat set)" using inj by (metis finite_imageD)
    then show False by simp
  qed
  with sub show ?thesis using infinite_super by blast
qed

lemma infinite_global_vnames: "infinite {x::vname. is_global x}"
proof -
  have inj: "inj (\<lambda>n::nat. replicate (Suc n) (CHR ''G''))"
    by (rule injI) (metis length_replicate nat.inject)
  have sub: "range (\<lambda>n::nat. replicate (Suc n) (CHR ''G'')) \<subseteq> {x. is_global x}"
    by (auto simp: is_global_def)
  have "infinite (range (\<lambda>n::nat. replicate (Suc n) (CHR ''G'')))"
  proof
    assume "finite (range (\<lambda>n::nat. replicate (Suc n) (CHR ''G'')))"
    then have "finite (UNIV::nat set)" using inj by (metis finite_imageD)
    then show False by simp
  qed
  with sub show ?thesis using infinite_super by blast
qed

lemma ex_local_vname_notin:
  assumes "finite K" shows "\<exists>x. \<not> is_global x \<and> x \<notin> K"
proof -
  have "\<not> {x. \<not> is_global x} \<subseteq> K"
    using infinite_nonglobal_vnames assms by (metis finite_subset)
  then show ?thesis by blast
qed

lemma ex_global_vname_notin:
  assumes "finite K" shows "\<exists>x. is_global x \<and> x \<notin> K"
proof -
  have "\<not> {x. is_global x} \<subseteq> K"
    using infinite_global_vnames assms by (metis finite_subset)
  then show ?thesis by blast
qed

subsection \<open>Order\<close>

fun less_eq_st_rep :: "('a::order_bot) st_rep \<Rightarrow> 'a st_rep \<Rightarrow> bool" where
  "less_eq_st_rep (dl1, dg1, ps1) (dl2, dg2, ps2) \<longleftrightarrow>
     dl1 \<le> dl2 \<and> dg1 \<le> dg2 \<and>
     (\<forall>x \<in> set (map fst ps1) \<union> set (map fst ps2).
        fun_rep_st (dl1, dg1, ps1) x \<le> fun_rep_st (dl2, dg2, ps2) x)"

lemma less_eq_st_rep_iff:
  "less_eq_st_rep r1 r2 \<longleftrightarrow> (\<forall>x. fun_rep_st r1 x \<le> fun_rep_st r2 x)"
proof (cases r1; cases r2)
  fix dl1 dg1 ps1 dl2 dg2 ps2
  assume r1: "r1 = (dl1, dg1, ps1)" and r2: "r2 = (dl2, dg2, ps2)"
  show ?thesis
  proof
    assume H: "less_eq_st_rep r1 r2"
    show "\<forall>x. fun_rep_st r1 x \<le> fun_rep_st r2 x"
    proof
      fix x
      show "fun_rep_st r1 x \<le> fun_rep_st r2 x"
      proof (cases "x \<in> set (map fst ps1) \<union> set (map fst ps2)")
        case True
        then show ?thesis using H r1 r2 by auto
      next
        case False
        then have n: "map_of ps1 x = None" "map_of ps2 x = None"
          by (auto simp: map_of_eq_None_iff)
        from H r1 r2 have "dl1 \<le> dl2" "dg1 \<le> dg2" by auto
        with n r1 r2 show ?thesis by (auto split: if_splits)
      qed
    qed
  next
    assume H: "\<forall>x. fun_rep_st r1 x \<le> fun_rep_st r2 x"
    have dl: "dl1 \<le> dl2"
    proof -
      obtain x where x: "\<not> is_global x"
        "x \<notin> set (map fst ps1) \<union> set (map fst ps2)"
        using ex_local_vname_notin[of "set (map fst ps1) \<union> set (map fst ps2)"]
        by auto
      from x(2) have mo: "map_of ps1 x = None" "map_of ps2 x = None"
        by (auto simp: map_of_eq_None_iff)
      from H have "fun_rep_st r1 x \<le> fun_rep_st r2 x" by blast
      then show ?thesis using mo x(1) r1 r2 by simp
    qed
    have dg: "dg1 \<le> dg2"
    proof -
      obtain x where x: "is_global x"
        "x \<notin> set (map fst ps1) \<union> set (map fst ps2)"
        using ex_global_vname_notin[of "set (map fst ps1) \<union> set (map fst ps2)"]
        by auto
      from x(2) have mo: "map_of ps1 x = None" "map_of ps2 x = None"
        by (auto simp: map_of_eq_None_iff)
      from H have "fun_rep_st r1 x \<le> fun_rep_st r2 x" by blast
      then show ?thesis using mo x(1) r1 r2 by simp
    qed
    from dl dg H r1 r2 show "less_eq_st_rep r1 r2" by simp
  qed
qed

instantiation st :: (order_bot) ord begin
lift_definition less_eq_st :: "('a::order_bot) st \<Rightarrow> 'a st \<Rightarrow> bool"
  is less_eq_st_rep
  by (auto simp: eq_st_def less_eq_st_rep_iff)
definition "(s :: ('a::order_bot) st) < t \<longleftrightarrow> s \<le> t \<and> \<not> t \<le> s"
instance ..
end

lemma le_st_iff: "(s \<le> t) \<longleftrightarrow> (\<forall>x. lookup_st s x \<le> lookup_st t x)"
  by transfer (rule less_eq_st_rep_iff)

instance st :: (order_bot) order
proof
  fix s t u :: "('a::order_bot) st"
  show "(s < t) \<longleftrightarrow> (s \<le> t \<and> \<not> t \<le> s)"
    by (simp add: less_st_def)
  show "s \<le> s"
    by (simp add: le_st_iff)
  show "s \<le> t \<Longrightarrow> t \<le> u \<Longrightarrow> s \<le> u"
    by (auto simp: le_st_iff intro: order_trans)
  show "s \<le> t \<Longrightarrow> t \<le> s \<Longrightarrow> s = t"
    by transfer
       (metis eq_st_def fun_eq_iff less_eq_st_rep_iff order_antisym)
qed

subsection \<open>Join (sup)\<close>

lemma map_of_map_self:
  "map_of (map (\<lambda>(k, _). (k, g k)) xs) x =
     (if x \<in> set (map fst xs) then Some (g x) else None)"
  by (induction xs) auto

lemma map_of_merge_pair:
  "(map_of (map (\<lambda>(k, _). (k, g k)) ps2) ++ map_of (map (\<lambda>(k, _). (k, g k)) ps1)) x
   = (if x \<in> set (map fst ps1) \<union> set (map fst ps2) then Some (g x) else None)"
  by (auto simp: map_add_def map_of_map_self split: option.splits)

fun merge_st_rep ::
  "('a::bounded_semilattice_sup_bot) st_rep \<Rightarrow> 'a st_rep \<Rightarrow> 'a st_rep" where
  "merge_st_rep (dl1, dg1, ps1) (dl2, dg2, ps2) =
     (dl1 \<squnion> dl2, dg1 \<squnion> dg2,
      map (\<lambda>(x, _). (x, fun_rep_st (dl1, dg1, ps1) x \<squnion> fun_rep_st (dl2, dg2, ps2) x))
          (ps1 @ ps2))"

lemma fun_rep_merge_st_rep [simp]:
  "fun_rep_st (merge_st_rep r1 r2) =
   (\<lambda>x. fun_rep_st r1 x \<squnion> fun_rep_st r2 x)"
proof (cases r1; cases r2)
  fix dl1 dg1 ps1 dl2 dg2 ps2
  assume r1: "r1 = (dl1, dg1, ps1)" and r2: "r2 = (dl2, dg2, ps2)"
  show ?thesis
    unfolding r1 r2
  proof (rule ext)
    fix x
    show "fun_rep_st (merge_st_rep (dl1, dg1, ps1) (dl2, dg2, ps2)) x
          = fun_rep_st (dl1, dg1, ps1) x \<squnion> fun_rep_st (dl2, dg2, ps2) x"
    proof (cases "x \<in> set (map fst ps1) \<union> set (map fst ps2)")
      case True
      then show ?thesis by (simp add: map_of_merge_pair)
    next
      case False
      then have "map_of ps1 x = None" "map_of ps2 x = None"
        by (auto simp: map_of_eq_None_iff)
      with False show ?thesis by (simp add: map_of_merge_pair split: if_splits)
    qed
  qed
qed

instantiation st :: (bounded_semilattice_sup_bot) sup begin
lift_definition sup_st :: "('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st \<Rightarrow> 'a st"
  is merge_st_rep by (simp add: eq_st_def)
instance ..
end

lemma lookup_sup_st [simp]:
  "lookup_st (s \<squnion> t) x = lookup_st s x \<squnion> lookup_st t x"
  by transfer simp

subsection \<open>Bot\<close>

instantiation st :: (bot) bot begin
lift_definition bot_st :: "('a::bot) st" is "(bot, bot, [])" .
instance ..
end

lemma lookup_bot_class [simp]: "lookup_st (bot :: ('a::bot) st) x = bot"
  by transfer simp

lemma bot_le_st: "(bot :: ('a::order_bot) st) \<le> s"
  by (simp add: le_st_iff)

instance st :: (order_bot) order_bot
  by standard (rule bot_le_st)

instance st :: (bounded_semilattice_sup_bot) semilattice_sup
proof
  fix s t u :: "('a::bounded_semilattice_sup_bot) st"
  show "s \<le> s \<squnion> t"
    by (simp add: le_st_iff)
  show "t \<le> s \<squnion> t"
    by (simp add: le_st_iff)
  show "s \<le> u \<Longrightarrow> t \<le> u \<Longrightarrow> s \<squnion> t \<le> u"
    by (simp add: le_st_iff)
qed

instance st :: (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

subsection \<open>Equal instance\<close>

text \<open>
  Equality via antisymmetry: \<open>s = t\<close> iff \<open>s \<le> t\<close> and \<open>t \<le> s\<close>.  The \<open>\<le>\<close> check
  inspects the two region-defaults and the finite union of override keys, so it
  is computable.
\<close>

instantiation st :: (bounded_semilattice_sup_bot) equal begin
definition "equal_class.equal (s :: ('a::bounded_semilattice_sup_bot) st) t \<longleftrightarrow> s \<le> t \<and> t \<le> s"
instance proof
  fix s t :: "('a::bounded_semilattice_sup_bot) st"
  show "equal_class.equal s t \<longleftrightarrow> (s = t)"
    unfolding equal_st_def by (meson antisym order_refl)
qed
end

subsection \<open>Pointwise warrowing on the value domain\<close>

text \<open>
  Pointwise @{const widen} / @{const narrow} on the value domain, lifted through
  @{const fun_rep_st} like @{const merge_st_rep} does for join.
\<close>

fun widen_st_rep :: "('a::bounded_warrowing) st_rep \<Rightarrow> 'a st_rep \<Rightarrow> 'a st_rep" where
  "widen_st_rep (dl1, dg1, ps1) (dl2, dg2, ps2) =
     (dl1 \<nabla> dl2, dg1 \<nabla> dg2,
      map (\<lambda>(x, _). (x, fun_rep_st (dl1, dg1, ps1) x \<nabla> fun_rep_st (dl2, dg2, ps2) x))
          (ps1 @ ps2))"

lemma fun_rep_widen_st_rep:
  "fun_rep_st (widen_st_rep r1 r2) =
   (\<lambda>x. fun_rep_st r1 x \<nabla> fun_rep_st r2 x)"
proof (cases r1; cases r2)
  fix dl1 dg1 ps1 dl2 dg2 ps2
  assume r1: "r1 = (dl1, dg1, ps1)" and r2: "r2 = (dl2, dg2, ps2)"
  show ?thesis
    unfolding r1 r2
  proof (rule ext)
    fix x
    show "fun_rep_st (widen_st_rep (dl1, dg1, ps1) (dl2, dg2, ps2)) x
          = fun_rep_st (dl1, dg1, ps1) x \<nabla> fun_rep_st (dl2, dg2, ps2) x"
    proof (cases "x \<in> set (map fst ps1) \<union> set (map fst ps2)")
      case True
      then show ?thesis by (simp add: map_of_merge_pair)
    next
      case False
      then have "map_of ps1 x = None" "map_of ps2 x = None"
        by (auto simp: map_of_eq_None_iff)
      with False show ?thesis by (simp add: map_of_merge_pair split: if_splits)
    qed
  qed
qed

fun narrow_st_rep :: "('a::bounded_warrowing) st_rep \<Rightarrow> 'a st_rep \<Rightarrow> 'a st_rep" where
  "narrow_st_rep (dl1, dg1, ps1) (dl2, dg2, ps2) =
     (dl1 \<Delta> dl2, dg1 \<Delta> dg2,
      map (\<lambda>(x, _). (x, fun_rep_st (dl1, dg1, ps1) x \<Delta> fun_rep_st (dl2, dg2, ps2) x))
          (ps1 @ ps2))"

lemma fun_rep_narrow_st_rep:
  "fun_rep_st (narrow_st_rep r1 r2) =
   (\<lambda>x. fun_rep_st r1 x \<Delta> fun_rep_st r2 x)"
proof (cases r1; cases r2)
  fix dl1 dg1 ps1 dl2 dg2 ps2
  assume r1: "r1 = (dl1, dg1, ps1)" and r2: "r2 = (dl2, dg2, ps2)"
  show ?thesis
    unfolding r1 r2
  proof (rule ext)
    fix x
    show "fun_rep_st (narrow_st_rep (dl1, dg1, ps1) (dl2, dg2, ps2)) x
          = fun_rep_st (dl1, dg1, ps1) x \<Delta> fun_rep_st (dl2, dg2, ps2) x"
    proof (cases "x \<in> set (map fst ps1) \<union> set (map fst ps2)")
      case True
      then show ?thesis by (simp add: map_of_merge_pair)
    next
      case False
      then have "map_of ps1 x = None" "map_of ps2 x = None"
        by (auto simp: map_of_eq_None_iff)
      with False show ?thesis by (simp add: map_of_merge_pair split: if_splits)
    qed
  qed
qed

lemma widen_st_rep_eq_st:
  "eq_st r1 r1' \<Longrightarrow> eq_st r2 r2' \<Longrightarrow>
   eq_st (widen_st_rep r1 r2) (widen_st_rep r1' r2')"
  by (auto simp: eq_st_def fun_rep_widen_st_rep)

lemma narrow_st_rep_eq_st:
  "eq_st r1 r1' \<Longrightarrow> eq_st r2 r2' \<Longrightarrow>
   eq_st (narrow_st_rep r1 r2) (narrow_st_rep r1' r2')"
  by (auto simp: eq_st_def fun_rep_narrow_st_rep)

lemma lookup_Abs_st [simp]:
  "lookup_st (Abs_st r) x = fun_rep_st r x"
  by transfer simp

lemma Abs_st_rep_st [simp]: "Abs_st (rep_st s) = s"
  by (fact Lifting.Quotient_abs_rep [OF Quotient_st])

lemma lookup_st_rep:
  "lookup_st s x = fun_rep_st (rep_st s) x"
  using lookup_Abs_st[of "rep_st s" x] by simp

lift_definition widen_on_st :: "('a::bounded_warrowing) st \<Rightarrow> 'a st \<Rightarrow> 'a st"
  is widen_st_rep
  by (auto simp: eq_st_def fun_rep_widen_st_rep fun_eq_iff)

lift_definition narrow_on_st :: "('a::bounded_warrowing) st \<Rightarrow> 'a st \<Rightarrow> 'a st"
  is narrow_st_rep
  by (auto simp: eq_st_def fun_rep_narrow_st_rep fun_eq_iff)

instantiation st :: (bounded_warrowing) widening begin

definition "widen (s :: ('a::bounded_warrowing) st) t = widen_on_st s t"

lemma lookup_widen_st_aux:
  "lookup_st (widen_on_st s t) x = lookup_st s x \<nabla> lookup_st t x"
  by transfer (simp add: fun_rep_widen_st_rep)

lemma widen_st_ge1:
  "(a :: 'a::bounded_warrowing st) \<le> widen a b"
  unfolding le_st_iff widen_st_def
  by (intro allI) (subst lookup_widen_st_aux, rule widen_ge1)

lemma widen_st_ge2:
  "(b :: 'a::bounded_warrowing st) \<le> widen a b"
  unfolding le_st_iff widen_st_def
  by (intro allI) (subst lookup_widen_st_aux, rule widen_ge2)

instance proof
  fix a b :: "('a::bounded_warrowing) st"
  show "a \<le> widen a b" by (rule widen_st_ge1)
  show "b \<le> widen a b" by (rule widen_st_ge2)
qed
end

lemma lookup_widen_st [simp]:
  "lookup_st (s \<nabla> t) x = lookup_st s x \<nabla> lookup_st t x"
  unfolding widen_st_def by (rule lookup_widen_st_aux)

instantiation st :: (bounded_warrowing) narrowing begin

definition "narrow (s :: ('a::bounded_warrowing) st) t = narrow_on_st s t"

lemma lookup_narrow_st_aux:
  "lookup_st (narrow_on_st s t) x = lookup_st s x \<Delta> lookup_st t x"
  by transfer (simp add: fun_rep_narrow_st_rep)

lemma narrow_st_ge:
  "b \<le> (a :: 'a::bounded_warrowing st) \<Longrightarrow> b \<le> narrow a b"
  unfolding le_st_iff narrow_st_def
  by (intro allI impI) (subst lookup_narrow_st_aux, auto intro: narrow_ge simp: le_st_iff)

lemma narrow_st_le:
  "b \<le> (a :: 'a::bounded_warrowing st) \<Longrightarrow> narrow a b \<le> a"
  unfolding le_st_iff narrow_st_def
  by (intro allI impI) (subst lookup_narrow_st_aux, auto intro: narrow_le simp: le_st_iff)

instance proof
  fix a b :: "('a::bounded_warrowing) st"
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b" by (rule narrow_st_ge)
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a" by (rule narrow_st_le)
qed
end

lemma lookup_narrow_st [simp]:
  "lookup_st (s \<Delta> t) x = lookup_st s x \<Delta> lookup_st t x"
  unfolding narrow_st_def by (rule lookup_narrow_st_aux)

instance st :: (bounded_warrowing) warrowing ..

subsection \<open>Refinement: 'a st vs 'a abs_state\<close>

text \<open>
  \<open>fun_of_st :: 'a st => 'a abs_state\<close> converts the executable representation to
  the abstract one (\<open>vname => 'a\<close>), used to state the bridge lemma (S4).
\<close>

abbreviation fun_of_st :: "('a::bot) st \<Rightarrow> 'a abs_state" where
  "fun_of_st s \<equiv> lookup_st s"

lemma fun_of_st_bot [simp]:
  "fun_of_st (bot :: ('a::bot) st) = (\<lambda>_. bot)"
  by (rule ext) simp

lemma fun_of_st_sup [simp]:
  "fun_of_st (s \<squnion> t) = fun_of_st s \<squnion> fun_of_st t"
  by (rule ext) (simp add: sup_fun_def)

lemma fun_of_st_mono:
  "s \<le> t \<Longrightarrow> fun_of_st s \<le> fun_of_st t"
  unfolding le_fun_def le_st_iff by simp

subsection \<open>Pointwise local/global projection at 'a st\<close>

text \<open>
  Executable local/global split for states of type \<open>'a st\<close>.  Each projection
  resets one region-default to \<open>bot\<close> and drops that region's overrides.

  \<open>restrict_local_st\<close>: keep only non-global variables (bot elsewhere).
  \<open>restrict_global_st\<close>: keep only global variables (bot elsewhere).
  \<open>combine_abs_st sc se\<close>: locals from sc, globals from se.
\<close>

lemma map_of_filter_key:
  "map_of (filter (\<lambda>(k, _). P k) xs) k = (if P k then map_of xs k else None)"
  by (induction xs) auto

lemma fun_rep_restrict_local_rep:
  "fun_rep_st ((\<lambda>(dl, dg, ps). (dl, bot, filter (\<lambda>(x, _). \<not> is_global x) ps)) r)
   = (\<lambda>x. if \<not> is_global x then fun_rep_st r x else bot)"
proof -
  obtain dl dg ps where r: "r = (dl, dg, ps)" using prod_cases3 by blast
  show ?thesis unfolding r
    by (rule ext) (auto simp: map_of_filter_key split: option.split)
qed

lemma fun_rep_restrict_global_rep:
  "fun_rep_st ((\<lambda>(dl, dg, ps). (bot, dg, filter (\<lambda>(x, _). is_global x) ps)) r)
   = (\<lambda>x. if is_global x then fun_rep_st r x else bot)"
proof -
  obtain dl dg ps where r: "r = (dl, dg, ps)" using prod_cases3 by blast
  show ?thesis unfolding r
    by (rule ext) (auto simp: map_of_filter_key split: option.split)
qed

lift_definition restrict_local_st :: "('a::bot) st \<Rightarrow> 'a st"
  is "\<lambda>(dl, dg, ps). (dl, bot, filter (\<lambda>(x, _). \<not> is_global x) ps)"
  by (auto simp: eq_st_def fun_rep_restrict_local_rep fun_eq_iff)

lift_definition restrict_global_st :: "('a::bot) st \<Rightarrow> 'a st"
  is "\<lambda>(dl, dg, ps). (bot, dg, filter (\<lambda>(x, _). is_global x) ps)"
  by (auto simp: eq_st_def fun_rep_restrict_global_rep fun_eq_iff)

definition combine_abs_st ::
    "('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st \<Rightarrow> 'a st"
  where "combine_abs_st sc se = restrict_local_st sc \<squnion> restrict_global_st se"

lemma lookup_restrict_local_st [simp]:
  "lookup_st (restrict_local_st s) x =
   (if \<not> is_global x then lookup_st s x else bot)"
  by transfer (simp add: fun_rep_restrict_local_rep)

lemma lookup_restrict_global_st [simp]:
  "lookup_st (restrict_global_st s) x =
   (if is_global x then lookup_st s x else bot)"
  by transfer (simp add: fun_rep_restrict_global_rep)

lemma lookup_combine_abs_st [simp]:
  "lookup_st (combine_abs_st sc se) x =
   (if is_global x then lookup_st se x else lookup_st sc x)"
  by (cases "is_global x")
     (simp_all add: combine_abs_st_def)

lemma st_eqI_lookup:
  assumes "\<And>x. lookup_st s1 x = lookup_st s2 x"
  shows "s1 = s2"
  using assms unfolding eq_st_def lookup_st_rep
  by (metis (no_types, lifting) ext Abs_st_rep_st eq_st_def st.abs_eq_iff) 

lemma restrict_global_st_eq_when_lookup_local_bot:
  assumes "\<And>x. \<not> is_global x \<Longrightarrow> lookup_st s x = bot"
  shows "restrict_global_st s = s"
  by (rule st_eqI_lookup) (auto simp: lookup_restrict_global_st assms)

lemma restrict_global_st_sup_restrict_global_st:
  "restrict_global_st a \<squnion> restrict_global_st b = restrict_global_st (a \<squnion> b)"
  by (rule st_eqI_lookup) (auto simp: lookup_restrict_global_st lookup_sup_st)

lemma bot_sup_restrict_global_st:
  "bot \<squnion> restrict_global_st s = restrict_global_st s"
  by (rule st_eqI_lookup) (auto simp: lookup_restrict_global_st lookup_sup_st)

end

