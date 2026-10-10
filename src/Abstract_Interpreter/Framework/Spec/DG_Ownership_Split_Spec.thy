theory DG_Ownership_Split_Spec
  imports DG_Local_State_Spec State_Restriction "Voblint_Solver.Strategy_Program_Fold"
begin

section \<open>Lifting a whole-state analysis onto the global channel\<close>

text \<open>
  Every other specification in this session is local-only: it answers from the
  local value and never touches \<open>man_global\<close> or \<open>man_sideg\<close>. This
  theory takes such a specification and returns one that does the opposite, and is
  the reason those capabilities exist.

  The lifted specification uses one carrier for \<open>D\<close> and \<open>G\<close>, splitting each
  state by variable ownership: \<^const>\<open>combine_env\<close>'s predicate is the source
  language's own declaration of which names are global, so the global names live on
  the shared channel and the rest on the program point's own unknown. The split is
  not a representation choice: a return recombines two concrete stores by that same
  ownership rule, keeping the caller's locals and taking the globals from the
  callee.

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
  restrictions to the global and the local half at that carrier.
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
       res \<leftarrow> T (m\<lparr>man_local := cmb (man_local m) g\<rparr>);
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
       res \<leftarrow> T (m\<lparr>man_local := cmb (man_local m) g\<rparr>) (cmb de g);
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
     (\<Squnion>(cont, entry)\<leftarrow>pairs. rg cont \<squnion> rg entry)"

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

definition ownership_split_enter_transfer_gen ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,unit,'d::bounded_semilattice_sup_bot,'d) man_enter_transfer
   \<Rightarrow> ('x,'k,unit,'d,'d) man_enter_transfer"
where
  "ownership_split_enter_transfer_gen cmb rg rl T m =
     do {
       g \<leftarrow> man_global m ();
       pairs \<leftarrow> T (m\<lparr>man_local := cmb (man_local m) g\<rparr>);
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

lemma dg_local_traverse_ownership_split_transfer_gen [simp]:
  "dg_local (traverse_program
             (transfer_program (ownership_split_transfer_gen cmb rg rl (local_transfer f))
                src (\<lambda>_. gk)) \<tau>)
     = rl (f (cmb (dg_local (\<tau> src)) (dg_global (\<tau> (Inr gk)))))"
  by (simp add: traverse_transfer_program ownership_split_transfer_gen_def
      local_transfer_def sp_compile_with_def sp_bind_def sp_return_def)

lemma dg_global_sides_ownership_split_transfer_gen [simp]:
  "dg_global (sides_of_program
            (transfer_program (ownership_split_transfer_gen cmb rg rl (local_transfer f))
               src (\<lambda>_. gk)) \<tau> (Inr gk))
     = rg (f (cmb (dg_local (\<tau> src)) (dg_global (\<tau> (Inr gk)))))"
  by (simp add: sides_transfer_program ownership_split_transfer_gen_def
      local_transfer_def sp_compile_with_def sp_bind_def sp_return_def)

lemma dg_local_traverse_ownership_split_combine_transfer_gen [simp]:
  "dg_local (traverse_program
             (combine_transfer_program
                (ownership_split_combine_transfer_gen cmb rg rl (local_combine_transfer h))
                src_cc src_ex (\<lambda>_. gk)) \<tau>)
     = rl (h (cmb (dg_local (\<tau> src_cc)) (dg_global (\<tau> (Inr gk))))
             (cmb (dg_local (\<tau> src_ex)) (dg_global (\<tau> (Inr gk)))))"
  by (simp add: traverse_combine_transfer_program ownership_split_combine_transfer_gen_def
      local_combine_transfer_def sp_compile_with_def sp_bind_def sp_return_def)

lemma dg_global_sides_ownership_split_combine_transfer_gen [simp]:
  "dg_global (sides_of_program
            (combine_transfer_program
               (ownership_split_combine_transfer_gen cmb rg rl (local_combine_transfer h))
               src_cc src_ex (\<lambda>_. gk)) \<tau> (Inr gk))
     = rg (h (cmb (dg_local (\<tau> src_cc)) (dg_global (\<tau> (Inr gk))))
             (cmb (dg_local (\<tau> src_ex)) (dg_global (\<tau> (Inr gk)))))"
  by (simp add: sides_combine_transfer_program ownership_split_combine_transfer_gen_def
      local_combine_transfer_def sp_compile_with_def sp_bind_def sp_return_def)

text \<open>A whole-state transfer never asks, so the query channel the generator
  installs around the wrapper leaves it unchanged.\<close>

lemma ownership_split_transfer_gen_local_outer_man [simp]:
  "ownership_split_transfer_gen cmb rg rl (local_transfer f) (outer_man Q m)
     = ownership_split_transfer_gen cmb rg rl (local_transfer f) m"
  by (simp add: ownership_split_transfer_gen_def local_transfer_def)
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
  assumes T: "enter_deps T (mk_dg_man (cmb d (dg_global (sigma (Inr (unknown_of ()))))) unknown_of)
                sigma pairs deps"
  shows "enter_deps (ownership_split_enter_transfer_gen cmb rg rl T) (mk_dg_man d unknown_of) sigma
           (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)
           ({Inr (unknown_of ())} \<union> deps)"
  unfolding enter_deps_def
proof (intro allI)
  fix K
  show "dep_aux sigma (ownership_split_enter_transfer_gen cmb rg rl T (mk_dg_man d unknown_of) K)
          = ({Inr (unknown_of ())} \<union> deps)
            \<union> dep_aux sigma (K (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs))"
    by (simp add: ownership_split_enter_transfer_gen_def sp_bind_def sp_return_def
        enter_depsD[OF T] Un_assoc)
qed
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
  assumes T: "enter_runs T (mk_dg_man (cmb d (dg_global (sigma (Inr (unknown_of ()))))) unknown_of)
                sigma pairs pub"
  shows "enter_runs (ownership_split_enter_transfer_gen cmb rg rl T) (mk_dg_man d unknown_of) sigma
           (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)
           (pub \<squnion> (bot(Inr (unknown_of ()) := DG bot (ownership_split_enter_sides rg pairs))))"
  unfolding enter_runs_def
proof (intro allI conjI)
  fix K
  show "traverse_rhs (ownership_split_enter_transfer_gen cmb rg rl T (mk_dg_man d unknown_of) K) sigma
          = traverse_rhs (K (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)) sigma"
    by (simp add: ownership_split_enter_transfer_gen_def sp_bind_def sp_return_def
        enter_runsD_traverse[OF T])
next
  fix K
  show "sides_of_rhs (ownership_split_enter_transfer_gen cmb rg rl T (mk_dg_man d unknown_of) K) sigma
          = (pub \<squnion> (bot(Inr (unknown_of ()) := DG bot (ownership_split_enter_sides rg pairs))))
            \<squnion> sides_of_rhs (K (map (\<lambda>(cont, entry). (rl cont, rl entry)) pairs)) sigma"
    by (simp add: ownership_split_enter_transfer_gen_def sp_bind_def sp_return_def
        enter_runsD_sides[OF T] sup_fun_def fun_upd_def)
       (auto simp: fun_eq_iff ac_simps split: if_splits)
qed

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

definition ownership_split_lift_gen ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,unit,'d::bounded_semilattice_sup_bot,'d) dg_spec
   \<Rightarrow> ('x,'k,unit,'d,'d) dg_spec"
where
  "ownership_split_lift_gen cmb rg rl S = local_dg_spec_template\<lparr>
     dgs_skip := ownership_split_transfer_gen cmb rg rl (skip\<^sup>\<sharp> S),
     dgs_assign := (\<lambda>x e. ownership_split_transfer_gen cmb rg rl (assign\<^sup>\<sharp> S x e)),
     dgs_special := (\<lambda>sc x. ownership_split_transfer_gen cmb rg rl (special\<^sup>\<sharp> S sc x)),
     dgs_branch := (\<lambda>b pol. ownership_split_transfer_gen cmb rg rl (branch\<^sup>\<sharp> S b pol)),
     dgs_body := (\<lambda>p. ownership_split_transfer_gen cmb rg rl (body\<^sup>\<sharp> S p)),
     dgs_return := (\<lambda>e p. ownership_split_transfer_gen cmb rg rl (return\<^sup>\<sharp> S e p)),
     dgs_enter := (\<lambda>ci. ownership_split_enter_transfer_gen cmb rg rl (enter\<^sup>\<sharp> S ci)),
     dgs_event := (\<lambda>evt. ownership_split_transfer_gen cmb rg rl (event\<^sup>\<sharp> S evt)),
     dgs_combine_assign :=
       (\<lambda>ci. ownership_split_combine_transfer_gen cmb rg rl (dg_spec_combine_transfer S ci)) \<rparr>"

text \<open>Both eliminate a constructed wrapper specification and expose the
  corresponding transfer wrapper, in a terminating direction, so they fire
  wherever a lifted specification meets the edge or combine dispatch.\<close>

lemma dg_spec_step_ownership_split_lift_gen [simp]:
  "dg_spec_step (ownership_split_lift_gen cmb rg rl S) a
     = ownership_split_transfer_gen cmb rg rl (dg_spec_step S a)"
  unfolding ownership_split_lift_gen_def by (cases a) simp_all

lemma dgs_enter_ownership_split_lift_gen [simp]:
  "enter\<^sup>\<sharp> (ownership_split_lift_gen cmb rg rl S) ci
     = ownership_split_enter_transfer_gen cmb rg rl (enter\<^sup>\<sharp> S ci)"
  unfolding ownership_split_lift_gen_def by simp

lemma dgs_query_ownership_split_lift_gen [simp]:
  "dgs_query (ownership_split_lift_gen cmb rg rl S) m q = sp_return \<top>"
  unfolding ownership_split_lift_gen_def by simp

lemma dg_spec_combine_transfer_ownership_split_lift_gen [simp]:
  "dg_spec_combine_transfer (ownership_split_lift_gen cmb rg rl S) ci
     = ownership_split_combine_transfer_gen cmb rg rl (dg_spec_combine_transfer S ci)"
  unfolding dg_spec_combine_transfer_def ownership_split_lift_gen_def
  by (simp add: local_transfer_def local_combine_transfer_def)

text \<open>The lifter preserves well-formedness: it reads the shared slot, runs the
  wrapped transfer at a manager built the same way, publishes once and answers.
  Every step of that is a closure lemma.\<close>

lemma sp_wf_dgs_combine_assign_ownership_split_lift_gen [intro]:
  assumes "dg_spec_wf S"
  shows
    "sp_wf (combine_assign\<^sup>\<sharp> (ownership_split_lift_gen cmb rg rl S) ci (mk_dg_man d unknown_of) ex)"
  unfolding ownership_split_lift_gen_def
  by (auto simp: ownership_split_combine_transfer_gen_def
      intro!: sp_wf_bind dg_spec_wf_combine[OF assms])

lemma dg_spec_wf_ownership_split_lift_gen [intro]:
  assumes "dg_spec_wf S"
  shows "dg_spec_wf (ownership_split_lift_gen cmb rg rl S)"
  unfolding dg_spec_wf_def
  by (auto simp: ownership_split_transfer_gen_def ownership_split_enter_transfer_gen_def
      ownership_split_combine_transfer_gen_def
      intro!: sp_wf_bind dg_spec_wf_step_ask[OF assms] dg_spec_wf_enter[OF assms]
        dg_spec_wf_combine[OF assms])

end
