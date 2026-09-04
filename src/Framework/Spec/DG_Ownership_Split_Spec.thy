theory DG_Ownership_Split_Spec
  imports DG_Local_State_Spec State_Restriction
begin

section \<open>Lifting a whole-state analysis onto the global channel\<close>

text \<open>
  Every other specification in this session is local-only: it answers from the
  local value and never touches \<open>man_global\<close> or \<open>man_sideg\<close>. This
  theory takes such a specification and returns one that does the opposite, and is
  the reason those capabilities exist.

  The lifted specification chooses \<open>D = G = 'a abs_state\<close>, splitting each
  state by variable ownership: \<^const>\<open>combine_env\<close>'s predicate is the source
  language's own declaration of which names are global, so the global names live on
  the shared channel and the rest on the program point's own unknown. The split is
  not a representation choice: a return recombines two concrete stores by that same
  ownership rule, keeping the caller's locals and taking the globals from the
  callee, which is what \<open>gamma_ownership_split_combine_env\<close> states.

  Each lifted transfer therefore reads the shared fact, rejoins it with the local
  half to recover the whole state, runs the argument's transfer on a manager
  holding that whole state, and splits the result back -- publishing the global
  half with \<open>man_sideg\<close> and answering with the local half. Its compiled tree
  reads the source, queries the global key, publishes a \<open>Side\<close>, and answers,
  which is what makes it the only specification here whose equations carry a
  genuine \<open>QueryG\<close> and \<open>Side\<close>.

  Because it consumes and produces a specification, it is a lifter in Goblint's
  sense -- a \<open>Spec2Spec\<close> functor, like the privatizations that give a Base
  analysis its shared-state discipline -- not a second way of writing an analysis.
  The argument keeps its own transfers; only what a transfer's local value means,
  and what happens to its result, change.

  The construction is generic in the carrier -- the same three operations exist on
  function-valued states and on the solver's association lists -- but not in the
  ownership rule, which is always \<^const>\<open>combine_env\<close> and the two
  \<open>restrict_\<close> projections at that carrier.
\<close>


subsection \<open>The ownership-splitting wrapper\<close>

text \<open>
  The pattern is stated once, over any carrier that can merge a local and a global
  half and project each back out. Which carrier is a separate question from what
  the wrapper does: the same three operations exist on function-valued states and
  on the solver's association lists, so the executable mirror is this definition at
  other arguments rather than a second development.

  It wraps a transfer rather than a pure function. What the wrapped transfer sees
  is a manager whose local value is the merged whole state; its own capabilities
  are the outer ones, which a whole-state transfer never calls. That is what makes
  the wrapper a specification-to-specification lifter -- Goblint's
  \<open>Spec2Spec\<close> -- instead of a second way of writing a transfer.
\<close>

definition ownership_split_transfer_gen ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,unit,'d::bounded_semilattice_sup_bot,'d) man_transfer
   \<Rightarrow> ('x,'k,unit,'d,'d) man_transfer"
where
  "ownership_split_transfer_gen cmb rg rl T m =
     do {
       g \<leftarrow> man_global m ();
       res \<leftarrow> T (man_with_local m (cmb (man_local m) g));
       _ \<leftarrow> man_sideg m () (rg res);
       sp_return (rl res)
     }"

text \<open>
  A return combine is the same pattern with two values to merge: the caller
  continuation becomes the wrapped transfer's local value, and the callee exit is
  merged against the same shared fact before it is handed over. Merging both sides
  means the wrapped transfer sees two whole states and needs to know nothing about
  the split -- in particular the callee's globals come from the shared channel,
  not from its own locally-restricted copy.
\<close>

definition ownership_split_combine_transfer_gen ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,unit,'d::bounded_semilattice_sup_bot,'d) man_combine_transfer
   \<Rightarrow> ('x,'k,unit,'d,'d) man_combine_transfer"
where
  "ownership_split_combine_transfer_gen cmb rg rl T m de =
     do {
       g \<leftarrow> man_global m ();
       res \<leftarrow> T (man_with_local m (cmb (man_local m) g)) (cmb de g);
       _ \<leftarrow> man_sideg m () (rg res);
       sp_return (rl res)
     }"

text \<open>
  Entry is the one boundary the pattern cannot be reused at verbatim: a call
  answers a list of alternatives rather than one successor value. The shared
  fact is read once and the wrapped entry runs once against the merged caller
  state, so every alternative comes out of the same whole state --- an actual
  may mention a global, so the alternatives cannot be computed from the local
  half alone. Each alternative then has both of its halves split, and the answer
  is the list of split pairs.

  What reaches the shared channel is the join, over every alternative, of both
  halves' global projections. A continuation is as much a product of the merged
  state as its callee entry is, and the split discards its global half;
  publishing only one of the two would need a proof that the other carries no
  global information the environment does not already hold.
\<close>

definition ownership_split_enter_sides ::
  "('d \<Rightarrow> 'd) \<Rightarrow> ('d::bounded_semilattice_sup_bot) enter_result list \<Rightarrow> 'd"
where
  "ownership_split_enter_sides rg pairs =
     foldr (\<lambda>(cont, entry) acc. rg cont \<squnion> rg entry \<squnion> acc) pairs bot"

lemma ownership_split_enter_sides_Nil [simp]:
  "ownership_split_enter_sides rg [] = bot"
  by (simp add: ownership_split_enter_sides_def)

lemma ownership_split_enter_sides_Cons [simp]:
  "ownership_split_enter_sides rg ((cont, entry) # pairs)
     = rg cont \<squnion> rg entry \<squnion> ownership_split_enter_sides rg pairs"
  by (simp add: ownership_split_enter_sides_def)

text \<open>
  What the joint publication bounds, and what it is bounded by. The two member
  rules are what a soundness proof reaches for once it has selected a covering
  alternative: that pair's two halves are each below what the call published, so
  a concretization taken against the published global still contains them. They
  stay untagged --- their conclusions are bare inequalities in \<open>rg\<close> and would
  broaden proof search wherever a \<open>\<le>\<close> goal appears.
\<close>

lemma ownership_split_enter_sides_le_iff:
  "ownership_split_enter_sides rg pairs \<le> g
     \<longleftrightarrow> (\<forall>(cont, entry) \<in> set pairs. rg cont \<le> g \<and> rg entry \<le> g)"
  by (induction pairs) auto

lemma ownership_split_enter_sides_cont_le:
  assumes "(cont, entry) \<in> set pairs"
  shows "rg cont \<le> ownership_split_enter_sides rg pairs"
  using assms ownership_split_enter_sides_le_iff by blast

lemma ownership_split_enter_sides_entry_le:
  assumes "(cont, entry) \<in> set pairs"
  shows "rg entry \<le> ownership_split_enter_sides rg pairs"
  using assms ownership_split_enter_sides_le_iff by blast

definition ownership_split_enter_transfer_gen ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,unit,'d::bounded_semilattice_sup_bot,'d) man_enter_transfer
   \<Rightarrow> ('x,'k,unit,'d,'d) man_enter_transfer"
where
  "ownership_split_enter_transfer_gen cmb rg rl T m =
     do {
       g \<leftarrow> man_global m ();
       pairs \<leftarrow> T (man_with_local m (cmb (man_local m) g));
       _ \<leftarrow> man_sideg m () (ownership_split_enter_sides rg pairs);
       sp_return (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)
     }"

subsection \<open>What the compiled tree reads and publishes\<close>

text \<open>
  Soundness judges a transfer by these two observations, so they are proved once
  here, on the pattern at a whole-state transfer, rather than per carrier: the
  answer is the local projection of the merged whole state, and the contribution at
  the routed key is its global projection.
\<close>

lemma traverse_ownership_split_transfer_gen [simp]:
  "locals (traverse_rhs
             (transfer_tree (ownership_split_transfer_gen cmb rg rl (local_transfer f))
                src (\<lambda>_. gk)) \<tau>)
     = rl (f (cmb (locals (\<tau> src)) (globs (\<tau> (Inr gk)))))"
  by (cases src)
     (simp_all add: transfer_tree_def dg_edge_tree_man_def ownership_split_transfer_gen_def
        local_transfer_def man_with_local_def mk_dg_man_def dg_read_at_def dg_read_global_def
        dg_sideg_def sp_bind_assoc)

lemma sides_ownership_split_transfer_gen [simp]:
  "globs (sides_of_rhs
            (transfer_tree (ownership_split_transfer_gen cmb rg rl (local_transfer f))
               src (\<lambda>_. gk)) \<tau> (Inr gk))
     = rg (f (cmb (locals (\<tau> src)) (globs (\<tau> (Inr gk)))))"
  by (cases src)
     (simp_all add: transfer_tree_def dg_edge_tree_man_def ownership_split_transfer_gen_def
        local_transfer_def man_with_local_def mk_dg_man_def dg_read_at_def dg_read_global_def
        dg_sideg_def sp_bind_assoc)

lemma traverse_ownership_split_combine_transfer_gen [simp]:
  "locals (traverse_rhs
             (combine_transfer_tree
                (ownership_split_combine_transfer_gen cmb rg rl (local_combine_transfer h))
                src_cc src_ex (\<lambda>_. gk)) \<tau>)
     = rl (h (cmb (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk))))
             (cmb (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk)))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        ownership_split_combine_transfer_gen_def local_combine_transfer_def man_with_local_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc)

lemma sides_ownership_split_combine_transfer_gen [simp]:
  "globs (sides_of_rhs
            (combine_transfer_tree
               (ownership_split_combine_transfer_gen cmb rg rl (local_combine_transfer h))
               src_cc src_ex (\<lambda>_. gk)) \<tau> (Inr gk))
     = rg (h (cmb (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk))))
             (cmb (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk)))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        ownership_split_combine_transfer_gen_def local_combine_transfer_def man_with_local_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc)

subsection \<open>The ownership rule at the pointwise carrier\<close>

text \<open>The three carrier operations the wrapper is generic in, fixed at the
  function-valued states: \<^const>\<open>combine_env\<close> merges by the classifier, and the
  two \<open>restrict_\<close> projections read each half back out.\<close>

definition ownership_split_transfer ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot abs_state,'a abs_state) man_transfer
   \<Rightarrow> ('x,'k,unit,'a abs_state,'a abs_state) man_transfer"
where
  "ownership_split_transfer gs =
     ownership_split_transfer_gen (combine_env gs) (restrict_global_for gs) (restrict_local_for gs)"

text \<open>
  What the lifter reads, in the same terms. The shared slot is read before the
  wrapped transfer runs, so it is a dependency of the call whatever the wrapped
  transfer does --- and it stays one even when nothing is published there,
  which is exactly why dependencies are tracked apart from
  \<^const>\<open>enter_runs\<close>'s publications. The trailing \<open>man_sideg\<close> writes rather
  than reads, so it contributes no dependency of its own.
\<close>

lemma enter_deps_ownership_split_enter_transfer_gen [intro]:
  fixes sigma :: "'x + 'k \<Rightarrow> ('d::bounded_semilattice_sup_bot,'d) dg_state"
  assumes T: "enter_deps T (man_with_local (mk_dg_man d key)
                              (cmb d (globs (sigma (Inr (key ())))))) sigma pairs deps"
  shows "enter_deps (ownership_split_enter_transfer_gen cmb rg rl T) (mk_dg_man d key) sigma
           (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)
           ({Inr (key ())} \<union> deps)"
  unfolding enter_deps_def
proof (intro allI)
  fix K
  show "dep_aux sigma (ownership_split_enter_transfer_gen cmb rg rl T (mk_dg_man d key) K)
          = ({Inr (key ())} \<union> deps)
            \<union> dep_aux sigma (K (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs))"
    by (simp add: ownership_split_enter_transfer_gen_def dg_read_global_def dg_sideg_def
        sp_read_global_def sp_publish_def sp_bind_def sp_return_def comp_def
        enter_depsD[OF T] Un_assoc)
qed

definition ownership_split_enter_transfer ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot abs_state,'a abs_state) man_enter_transfer
   \<Rightarrow> ('x,'k,unit,'a abs_state,'a abs_state) man_enter_transfer"
where
  "ownership_split_enter_transfer gs =
     ownership_split_enter_transfer_gen (combine_env gs) (restrict_global_for gs)
       (restrict_local_for gs)"

text \<open>
  How the lifter behaves under a solution, in the same terms as the transfer it
  wraps. The manager has to be a concrete \<^const>\<open>mk_dg_man\<close>: for an arbitrary
  one \<open>man_sideg m ()\<close> is opaque and the slot it publishes at cannot be named,
  so there would be nothing to state.

  The wrapped transfer is run at the reconstructed caller state, so its
  alternatives are the ones computed against the whole state rather than the
  local half --- that is the step a caller-local-only entry could not perform.
  Its own publications survive in \<open>pub\<close>, and the lifter adds exactly one
  contribution of its own, at the routed slot.
\<close>

lemma enter_runs_ownership_split_enter_transfer_gen [intro]:
  fixes sigma :: "'x + 'k \<Rightarrow> ('d::bounded_semilattice_sup_bot,'d) dg_state"
  assumes T: "enter_runs T (man_with_local (mk_dg_man d key)
                              (cmb d (globs (sigma (Inr (key ())))))) sigma pairs pub"
  shows "enter_runs (ownership_split_enter_transfer_gen cmb rg rl T) (mk_dg_man d key) sigma
           (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)
           (pub \<squnion> (bot(Inr (key ()) := DG bot (ownership_split_enter_sides rg pairs))))"
  unfolding enter_runs_def
proof (intro allI conjI)
  fix K
  show "traverse_rhs (ownership_split_enter_transfer_gen cmb rg rl T (mk_dg_man d key) K) sigma
          = traverse_rhs (K (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)) sigma"
    by (simp add: ownership_split_enter_transfer_gen_def dg_read_global_def dg_sideg_def
        sp_read_global_def sp_publish_def sp_bind_def sp_return_def comp_def
        enter_runsD_traverse[OF T])
next
  fix K
  show "sides_of_rhs (ownership_split_enter_transfer_gen cmb rg rl T (mk_dg_man d key) K) sigma
          = (pub \<squnion> (bot(Inr (key ()) := DG bot (ownership_split_enter_sides rg pairs))))
            \<squnion> sides_of_rhs (K (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)) sigma"
    by (simp add: ownership_split_enter_transfer_gen_def dg_read_global_def dg_sideg_def
        sp_read_global_def sp_publish_def sp_bind_def sp_return_def comp_def Let_def
        enter_runsD_sides[OF T] sup_fun_def fun_upd_def)
       (auto simp: fun_eq_iff ac_simps split: if_splits)
qed

definition ownership_split_combine_transfer ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot abs_state,'a abs_state) man_combine_transfer
   \<Rightarrow> ('x,'k,unit,'a abs_state,'a abs_state) man_combine_transfer"
where
  "ownership_split_combine_transfer gs =
     ownership_split_combine_transfer_gen (combine_env gs) (restrict_global_for gs)
       (restrict_local_for gs)"


subsection \<open>The specification-to-specification lifter\<close>

text \<open>
  Every edge transfer of the argument specification is wrapped, entry through its
  own list-shaped wrapper, and the whole return pipeline is wrapped once rather
  than stage by stage: wrapping each stage separately would split and re-merge
  between them, and the second merge would read the shared fact again instead of
  the first stage's own result. So \<^const>\<open>dgs_combine_env\<close> stays at its identity
  default and \<^const>\<open>dgs_combine_assign\<close> carries the wrapped
  \<^const>\<open>dg_spec_combine_transfer\<close> of the argument.
\<close>

definition ownership_split_lift ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot abs_state,'a abs_state) dg_spec
   \<Rightarrow> ('x,'k,unit,'a abs_state,'a abs_state) dg_spec"
where
  "ownership_split_lift gs S = default_local_dg_spec\<lparr>
     dgs_skip := ownership_split_transfer gs (dgs_skip S),
     dgs_assign := (\<lambda>x e. ownership_split_transfer gs (dgs_assign S x e)),
     dgs_special := (\<lambda>sc x. ownership_split_transfer gs (dgs_special S sc x)),
     dgs_branch := (\<lambda>b pol. ownership_split_transfer gs (dgs_branch S b pol)),
     dgs_body := (\<lambda>p. ownership_split_transfer gs (dgs_body S p)),
     dgs_return := (\<lambda>e p. ownership_split_transfer gs (dgs_return S e p)),
     dgs_enter := (\<lambda>ci. ownership_split_enter_transfer gs (dgs_enter S ci)),
     dgs_event := (\<lambda>evt. ownership_split_transfer gs (dgs_event S evt)),
     dgs_combine_assign :=
       (\<lambda>ci. ownership_split_combine_transfer gs (dg_spec_combine_transfer S ci)) \<rparr>"

declare ownership_split_lift_def [code_unfold]

lemma dg_spec_step_ownership_split_lift:
  "dg_spec_step (ownership_split_lift gs S) a = ownership_split_transfer gs (dg_spec_step S a)"
  unfolding ownership_split_lift_def by (cases a) simp_all

lemma dgs_enter_ownership_split_lift:
  "dgs_enter (ownership_split_lift gs S) ci = ownership_split_enter_transfer gs (dgs_enter S ci)"
  unfolding ownership_split_lift_def by simp

lemma dg_spec_combine_transfer_ownership_split_lift:
  "dg_spec_combine_transfer (ownership_split_lift gs S) ci
     = ownership_split_combine_transfer gs (dg_spec_combine_transfer S ci)"
  unfolding dg_spec_combine_transfer_def dgs_combine_def ownership_split_lift_def
  by (simp add: local_transfer_def local_combine_transfer_def man_with_local_def)


section \<open>What a split point means\<close>

text \<open>
  A point's two halves are read back by routing each name to the component that
  owns it, never by joining them: an untouched name keeps whatever precision its
  owning half has, instead of being coarsened by the other half's unrelated
  default. That routing is exactly the merge the transfers above perform, which
  is why this is the concretization they are sound for.
\<close>

definition gamma_ownership_split ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state \<Rightarrow> store set"
where
  "gamma_ownership_split gs d g = \<lbrakk>combine_env gs d g\<rbrakk>"

lemma gamma_ownership_split_eq: "gamma_ownership_split gs d g = \<lbrakk>combine_env gs d g\<rbrakk>"
  unfolding gamma_ownership_split_def ..

lemma gamma_ownership_splitD [dest]: "s \<in> gamma_ownership_split gs d g \<Longrightarrow> s \<in> \<lbrakk>combine_env gs d g\<rbrakk>"
  unfolding gamma_ownership_split_def by simp

lemma gamma_ownership_split_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_ownership_split gs d g \<subseteq> gamma_ownership_split gs d' g'"
  unfolding gamma_ownership_split_def
  by (rule gamma_state_mono) (use assms in \<open>auto simp: combine_env_def le_fun_def\<close>)

text \<open>
  A return merges two concrete stores by the same ownership routing the
  abstract merge uses, so the merged store is still described by the caller's
  own merged state: its locals come from the caller side, and its globals from
  a state whose global half is the same \<open>g\<close>.
\<close>

lemma gamma_ownership_split_combine_env:
  assumes cc: "s \<in> \<lbrakk>combine_env gs dc g\<rbrakk>"
    and ex: "t \<in> \<lbrakk>combine_env gs de g\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env gs dc g\<rbrakk>"
proof (rule gamma_stateI)
  fix x
  show "combine_env gs s t x \<in> gamma (combine_env gs dc g x)"
  proof (cases "gs x")
    case True
    have "t x \<in> gamma (combine_env gs de g x)" using ex by (simp add: gamma_state_def)
    then show ?thesis using True by (simp add: combine_env_def)
  next
    case False
    have "s x \<in> gamma (combine_env gs dc g x)" using cc by (simp add: gamma_state_def)
    then show ?thesis using False by (simp add: combine_env_def)
  qed
qed

text \<open>
  The return value is the one name read off the callee's local half rather than
  through the merge, so it needs \<^const>\<open>reserved_ret_var\<close>: only because no
  program declares \<^const>\<open>ret_var\<close> global does that half agree with the merged
  state there.
\<close>

lemma gamma_ownership_split_combine_assign:
  assumes reserved: "reserved_ret_var gs"
    and cc: "s \<in> \<lbrakk>combine_env gs dc g\<rbrakk>"
    and ex: "t \<in> \<lbrakk>combine_env gs de g\<rbrakk>"
  shows "combine_assign dst (t ret_var) (combine_env gs s t)
           \<in> \<lbrakk>combine_assign dst (de ret_var) (combine_env gs dc g)\<rbrakk>"
proof (cases dst)
  case None
  then show ?thesis using gamma_ownership_split_combine_env[OF cc ex] by simp
next
  case (Some x)
  have ret: "t ret_var \<in> gamma (de ret_var)"
  proof -
    have "t ret_var \<in> gamma (combine_env gs de g ret_var)"
      using ex by (simp add: gamma_state_def)
    then show ?thesis
      using reserved by (simp add: combine_env_def reserved_ret_var_def)
  qed
  show ?thesis
    unfolding Some
    using gamma_ownership_split_combine_env[OF cc ex] ret
    by (auto simp: gamma_state_def)
qed

section \<open>Soundness of the lifted analysis\<close>

text \<open>
  The wrapped specification's own soundness is the only mathematics here. Each
  obligation reduces by the four observation lemmas to a statement about the
  merged state, where \<open>combine_env_restrict_id\<close> rebuilds exactly what the
  wrapped transfer was applied to -- so what is left is the transfer contract
  itself, cited from the locale.

  The argument is a Base specification rather than an arbitrary one because the
  wrapper feeds it a local value the environment never held: an argument that read
  a global of its own would read it at a slot this concretization does not account
  for. A whole-state analysis makes no such read, which is exactly what
  \<^const>\<open>local_state_dg_spec_for\<close> guarantees about its trees.

  The callee exit is merged before the wrapped combine sees it, so the return slot
  is read off a whole state like every other name and no \<open>reserved_ret_var\<close>
  side condition arises.
\<close>

theorem (in sound_transfer_for) sound_dg_spec_ownership_split_lift:
  "sound_dg_spec (ownership_split_lift gs (local_state_dg_spec_for gs sk asn sp br bd rt en ev))
     (gamma_ownership_split gs) gs"
proof (unfold_locales, goal_cases)
  case (1 d d' g g')
  then show ?case by (rule gamma_ownership_split_mono)
next
  case (2 a \<tau> src gk)
  show ?case
    unfolding dg_spec_edge_tree_def dg_spec_step_ownership_split_lift
      dg_spec_step_local_state_for ownership_split_transfer_def gamma_ownership_split_def
    by (simp add: step_sound_for)
next
  case (3 s \<tau> src_cc gk t src_ex ci)
  then show ?case
    unfolding dg_spec_combine_transfer_ownership_split_lift
      local_state_dg_spec_for_def dg_spec_combine_transfer_local_dg_spec
      ownership_split_combine_transfer_def gamma_ownership_split_def
    by (simp add: ownership_split_combine_transfer_gen_def local_combine_transfer_def
        man_with_local_def mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc
        combine_collect_sound)
qed


end
