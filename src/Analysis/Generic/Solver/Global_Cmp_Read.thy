theory Global_Cmp_Read
  imports TD_Side_CFG
begin

section \<open>Context-compatible global read\<close>

text \<open>
  \<^const>\<open>glob_env\<close> joins ALL named-global slots on every read, so the global
  value seen at a program point is context-invariant: indexing local unknowns by
  context cannot recover a per-context global.  \<open>glob_env_cmp\<close> filters that join
  by a compatibility relation \<open>cmp\<close> between the reading context and a global key,
  mirroring the digest-compatible global read of side-effecting constraint
  systems.  Two collapse points pin it to the existing reads:
  \<^item> \<open>cmp = (\<lambda>_ _. True)\<close> recovers \<^const>\<open>glob_env\<close> (join all keys);
  \<^item> a single compatible key \<open>{k. cmp ctx k} = {k0}\<close> recovers the single slot
    \<open>\<sigma> (Inr k0)\<close>.
\<close>

definition glob_env_cmp ::
  "('c \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> 'c
   \<Rightarrow> ('l + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> 'a abs_state"
where
  "glob_env_cmp cmp ctx \<sigma> = abs_join_set (\<squnion>) \<bottom> ((\<lambda>k. \<sigma> (Inr k)) ` {k. cmp ctx k})"

lemma glob_env_cmp_finite_keys: "finite {k::'g::finite. cmp ctx k}"
  by (rule finite_subset[OF subset_UNIV]) simp

text \<open>Every compatible slot is below the filtered join.\<close>
lemma glob_env_cmp_upper:
  assumes "cmp ctx k"
  shows "\<sigma> (Inr k) \<le> glob_env_cmp cmp ctx \<sigma>"
  unfolding glob_env_cmp_def abs_join_set_def
  by (rule mem_image_le_fold[OF glob_env_cmp_finite_keys comp_fun_commute_sup sup_ge1 sup_ge2])
     (use assms in blast)

text \<open>The filtered join is the least upper bound of the compatible slots.\<close>
lemma glob_env_cmp_le:
  assumes "\<And>k. cmp ctx k \<Longrightarrow> \<sigma> (Inr k) \<le> X"
  shows "glob_env_cmp cmp ctx \<sigma> \<le> X"
  unfolding glob_env_cmp_def
  by (rule abs_join_set_le[OF finite_imageI[OF glob_env_cmp_finite_keys]])
     (use assms in blast)

text \<open>Collapse 1: everything-compatible read is \<^const>\<open>glob_env\<close>.\<close>
lemma glob_env_cmp_True:
  "glob_env_cmp (\<lambda>_ _. True) ctx \<sigma> = glob_env \<sigma>"
  unfolding glob_env_cmp_def glob_env_def by simp

text \<open>Collapse 2: a single compatible key is that slot.\<close>
lemma glob_env_cmp_singleton:
  assumes "{k. cmp ctx k} = {k0}"
  shows "glob_env_cmp cmp ctx \<sigma> = \<sigma> (Inr k0)"
proof (rule order_antisym)
  have k0: "cmp ctx k0" using assms by blast
  show "glob_env_cmp cmp ctx \<sigma> \<le> \<sigma> (Inr k0)"
    by (rule glob_env_cmp_le) (use assms in auto)
  show "\<sigma> (Inr k0) \<le> glob_env_cmp cmp ctx \<sigma>"
    using k0 by (rule glob_env_cmp_upper)
qed

section \<open>Context-compatible side environment\<close>

text \<open>
  The reading counterpart of \<open>side_env_ctx\<close>: the local unknown at \<open>(v, ctx)\<close>
  joined with the \<open>cmp\<close>-filtered globals for \<open>ctx\<close>, instead of the join-all
  \<^const>\<open>glob_env\<close>.  \<open>cmp = (\<lambda>_ _. True)\<close> reproduces the join-all read; a single
  compatible key reduces to a single global slot.
\<close>

definition side_env_cmp ::
  "('c \<Rightarrow> 'g \<Rightarrow> bool)
   \<Rightarrow> ((pp \<times> 'c) + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> (pp \<times> 'c) \<Rightarrow> 'a abs_state"
where
  "side_env_cmp cmp \<sigma> p = \<sigma> (Inl p) \<squnion> glob_env_cmp cmp (snd p) \<sigma>"

text \<open>
  True-compatible read reproduces the join-all discipline: the global part is
  the join of every named-global slot, independent of the context.  (\<^const>\<open>glob_env\<close>
  fixes its local index to \<^typ>\<open>pp\<close>, so the join-all shape is spelled out here.)
\<close>
lemma side_env_cmp_True:
  "side_env_cmp (\<lambda>_ _. True) \<sigma> p
     = \<sigma> (Inl p) \<squnion> abs_join_set (\<squnion>) \<bottom> ((\<lambda>k. \<sigma> (Inr k)) ` UNIV)"
  unfolding side_env_cmp_def glob_env_cmp_def by simp

lemma side_env_cmp_singleton:
  assumes "{k. cmp ctx k} = {k0}"
  shows "side_env_cmp cmp \<sigma> (v, ctx) = \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr k0)"
proof -
  have "glob_env_cmp cmp ctx \<sigma> = \<sigma> (Inr k0)"
    using assms by (rule glob_env_cmp_singleton)
  thus ?thesis unfolding side_env_cmp_def by simp
qed

section \<open>Monotonicity\<close>

text \<open>
  The filtered read is monotone in the global slots it selects, hence in the
  whole environment.  Mirrors \<^const>\<open>glob_env\<close>'s \<open>glob_env_mono\<close> /
  \<open>glob_env_mono_Inr\<close>; used by the post-fixpoint global-bound chain.
\<close>

lemma glob_env_cmp_mono_Inr:
  assumes "\<And>k. cmp ctx k \<Longrightarrow> \<sigma>1 (Inr k) \<le> \<sigma>2 (Inr k)"
  shows "glob_env_cmp cmp ctx \<sigma>1 \<le> glob_env_cmp cmp ctx \<sigma>2"
proof (rule glob_env_cmp_le)
  fix k assume k: "cmp ctx k"
  have "\<sigma>1 (Inr k) \<le> \<sigma>2 (Inr k)" using k by (rule assms)
  also have "\<sigma>2 (Inr k) \<le> glob_env_cmp cmp ctx \<sigma>2" using k by (rule glob_env_cmp_upper)
  finally show "\<sigma>1 (Inr k) \<le> glob_env_cmp cmp ctx \<sigma>2" .
qed

lemma glob_env_cmp_mono:
  assumes "\<sigma>1 \<le> \<sigma>2" shows "glob_env_cmp cmp ctx \<sigma>1 \<le> glob_env_cmp cmp ctx \<sigma>2"
  by (rule glob_env_cmp_mono_Inr) (rule le_funD[OF assms])

lemma side_env_cmp_mono:
  assumes "\<sigma>1 \<le> \<sigma>2" shows "side_env_cmp cmp \<sigma>1 p \<le> side_env_cmp cmp \<sigma>2 p"
  unfolding side_env_cmp_def
  by (rule sup_mono[OF le_funD[OF assms] glob_env_cmp_mono[OF assms]])

text \<open>
  The filtered read never exceeds the join-all read: the \<open>cmp\<close> discipline is at
  least as precise as the monovariant \<^const>\<open>glob_env\<close> (which fixes its local
  index to \<^typ>\<open>pp\<close>).  Soundness relative to the concrete semantics is a separate
  obligation (the compatibility premise), not implied by this bound.
\<close>
lemma glob_env_cmp_le_glob_env:
  "glob_env_cmp cmp ctx (\<sigma> :: pp + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
     \<le> glob_env \<sigma>"
  by (rule glob_env_cmp_le) (rule glob_env_upper)

section \<open>Executable filtered read\<close>

text \<open>
  The read a keyed generator performs at a program point: fold-join over the
  \<open>cmp\<close>-compatible global keys, enumerated from the finite key type.  This is the
  QueryG-chain form of \<^const>\<open>glob_env_cmp\<close> and its executable replacement --- the
  definitional set-image fold is not code-generatable, exactly as for
  \<^const>\<open>glob_env\<close> (\<open>glob_env_code\<close>).  Filtering \<^const>\<open>Enum.enum\<close> by \<open>cmp ctx\<close>
  realises \<open>{k. cmp ctx k}\<close> concretely.
\<close>

lemma glob_env_cmp_code [code]:
  "glob_env_cmp cmp ctx
     (\<sigma> :: 'l + 'g::enum \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   = List.fold (\<squnion>) (map (\<lambda>k. \<sigma> (Inr k)) (filter (cmp ctx) Enum.enum)) \<bottom>"
proof -
  interpret ci: comp_fun_idem "(\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _"
    by unfold_locales (auto simp: sup_left_commute)
  have keys: "{k. cmp ctx k} = set (filter (cmp ctx) Enum.enum)"
    by (auto simp: UNIV_enum[symmetric])
  have "glob_env_cmp cmp ctx \<sigma>
        = Finite_Set.fold (\<squnion>) \<bottom>
            (set (map (\<lambda>k. \<sigma> (Inr k)) (filter (cmp ctx) Enum.enum)))"
    unfolding glob_env_cmp_def abs_join_set_def by (simp add: keys)
  also have "\<dots> = List.fold (\<squnion>) (map (\<lambda>k. \<sigma> (Inr k)) (filter (cmp ctx) Enum.enum)) \<bottom>"
    by (rule ci.fold_set_fold)
  finally show ?thesis .
qed

end
