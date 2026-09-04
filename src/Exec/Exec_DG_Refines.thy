theory Exec_DG_Refines
  imports
    "Voblint_Framework.DG_Soundness"
    "Voblint_Framework.DG_Ownership_Split_Spec"
    Exec_Refinement
    "Voblint_Framework.Routed_Context"
begin

section \<open>The executable carrier and its readback\<close>

text \<open>
  The verified solver uses the executable association-list carrier \<open>'a exec_dg_st\<close>, while
  soundness is stated over function-valued abstract states. This theory is the bottom of the
  bridge: the D/G product's lattice structure and the classifier-parametric readback
  \<open>fun_of_dg_st_for\<close> that lifts \<open>fun_of_exec_dg_st_for\<close> to that product. Everything
  here is carrier-level -- no specification, no transfer, no equation shape -- so a
  domain's executable mirror is related to its abstract state once, here, and the
  specification layers above never restate it.

  D/G lattice operations are componentwise, so the product inherits the order, join, bottom,
  equality, and widening operations the solver requires.
\<close>


type_synonym 'a exec_dg_st = "'a resolved_st_q"

subsection \<open>The combined warrowing arity for the executable state\<close>

text \<open>
  The D/G product requires each executable component to satisfy
  \<open>bounded_warrowing\<close>.  The association-list carrier already provides the required bottom,
  join, and warrowing operations, so the combined instance follows directly.
\<close>

text \<open>The quotient carrier inherits the executable lattice structure.\<close>


subsection \<open>Classifier-parametric readback\<close>

text \<open>
  The executable local/side readback, generic in the classifier: a placed
  executable state is written with a declaration-driven classifier, so
  reading it back needs the same classifier or the readback consults the
  wrong slot.
\<close>

definition fun_of_exec_dg_st_for ::
  "(vname => bool) => ('a::bot) exec_dg_st => 'a abs_state" where
  "fun_of_exec_dg_st_for gs = fun_of_resolved_st_q_for gs"

lemma fun_of_exec_dg_st_for_bot [simp]:
  "fun_of_exec_dg_st_for gs (bot :: ('a::order_bot) exec_dg_st) = bot"
  unfolding fun_of_exec_dg_st_for_def by (rule fun_of_resolved_st_q_for_bot)

lemma fun_of_exec_dg_st_for_sup [simp]:
  "fun_of_exec_dg_st_for gs ((s :: ('a::bounded_semilattice_sup_bot) exec_dg_st) \<squnion> t)
     = fun_of_exec_dg_st_for gs s \<squnion> fun_of_exec_dg_st_for gs t"
  unfolding fun_of_exec_dg_st_for_def by (rule fun_of_resolved_st_q_for_sup)

definition fun_of_dg_st_for ::
  "(vname => bool) =>
   (('a::bot) exec_dg_st, ('b::bot) exec_dg_st) dg_state => ('a abs_state, 'b abs_state) dg_state"
where
  "fun_of_dg_st_for gs d =
    DG (fun_of_exec_dg_st_for gs (locals d)) (fun_of_exec_dg_st_for gs (globs d))"

lemma fun_of_dg_st_for_simps [simp]:
  "locals (fun_of_dg_st_for gs d) = fun_of_exec_dg_st_for gs (locals d)"
  "globs (fun_of_dg_st_for gs d) = fun_of_exec_dg_st_for gs (globs d)"
  "fun_of_dg_st_for gs (DG a b) = DG (fun_of_exec_dg_st_for gs a) (fun_of_exec_dg_st_for gs b)"
  by (simp_all add: fun_of_dg_st_for_def)

lemma fun_of_dg_st_for_bot [simp]:
  "fun_of_dg_st_for gs (bot :: ('a::bounded_semilattice_sup_bot exec_dg_st,
                         'b::bounded_semilattice_sup_bot exec_dg_st) dg_state) = bot"
  by (simp add: bot_dg_state_def)

lemma location_vname_location_of [simp]:
  "location_vname (location_of gs x) = x"
  by (simp add: location_of_def)
subsection \<open>Whole-function readback of the two restrictions\<close>

text \<open>Not \<open>[simp]\<close>: the whole-function shape competes with the pointwise
  \<open>fun_of_resolved_st_q_for_restrict_local\<close>/\<open>fun_of_resolved_st_q_for_restrict_global\<close>
  normal form other proofs already rely on. Cited explicitly where the
  whole-function shape is what's needed.\<close>

lemma fun_of_resolved_st_q_for_restrict_local_for:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) = restrict_local_for gs (fun_of_resolved_st_q_for gs s)"
  by (rule ext) (simp add: restrict_local_for_def fun_of_resolved_st_q_for_restrict_local)

lemma fun_of_resolved_st_q_for_restrict_global_for:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) = restrict_global_for gs (fun_of_resolved_st_q_for gs s)"
  by (rule ext) (simp add: restrict_global_for_def fun_of_resolved_st_q_for_restrict_global)

section \<open>The ownership-splitting analysis at the executable carrier\<close>

text \<open>
  \<^const>\<open>ownership_split_transfer_gen\<close> asks only that a carrier can merge a local and a
  global half and project each back out. The association-list carrier answers
  with \<^const>\<open>combine_resolved_st_q\<close> and the two \<open>restrict_\<dots>_resolved_q\<close>
  projections, so the executable analysis is that transfer at those three
  arguments -- not a second definition of what the analysis does. The lemmas
  just above are why the readback carries it to the function-valued instance.
\<close>

definition ownership_split_transfer_st ::
  "('x,'k,unit,'a::bounded_semilattice_sup_bot exec_dg_st,'a exec_dg_st) man_transfer
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st,'a exec_dg_st) man_transfer"
where
  "ownership_split_transfer_st =
     ownership_split_transfer_gen combine_resolved_st_q restrict_global_resolved_q restrict_local_resolved_q"

text \<open>
  Entry is the same wrapping one step up in arity: it answers a list of
  caller-continuation/callee-entry pairs rather than one successor value, so the
  executable carrier supplies the same three operations to
  \<^const>\<open>ownership_split_enter_transfer_gen\<close>.
\<close>

definition ownership_split_enter_transfer_st ::
  "('x,'k,unit,'a::bounded_semilattice_sup_bot exec_dg_st,'a exec_dg_st) man_enter_transfer
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st,'a exec_dg_st) man_enter_transfer"
where
  "ownership_split_enter_transfer_st =
     ownership_split_enter_transfer_gen combine_resolved_st_q restrict_global_resolved_q
       restrict_local_resolved_q"

text \<open>
  The callee exit reaches the wrapped stage merged against the same shared fact,
  like the caller continuation. The return slot is read off it at the classifier's
  own location for \<^const>\<open>ret_var\<close>; that name is local, so the merge leaves it
  at the callee's own value.
\<close>

definition ownership_split_combine_transfer_st ::
  "(vname \<Rightarrow> bool) \<Rightarrow> call_info
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot exec_dg_st,'a exec_dg_st) man_combine_transfer"
where
  "ownership_split_combine_transfer_st gs ci =
     ownership_split_combine_transfer_gen combine_resolved_st_q restrict_global_resolved_q
       restrict_local_resolved_q
       (local_combine_transfer
          (\<lambda>env de. combine_assign_resolved_q gs (ci_dst ci)
                      (lookup_resolved_st_q de (location_of gs ret_var)) env))"

definition ownership_split_dg_spec_st_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st,'a exec_dg_st) dg_spec"
where
  "ownership_split_dg_spec_st_for gs tf_st enter_st = default_local_dg_spec\<lparr>
     dgs_skip := ownership_split_transfer_st (local_transfer (tf_st EA_Nop)),
     dgs_assign := (\<lambda>x e. ownership_split_transfer_st (local_transfer (tf_st (EA_Assign x e)))),
     dgs_special := (\<lambda>sc x. ownership_split_transfer_st (local_transfer (tf_st (EA_Special sc x)))),
     dgs_branch := (\<lambda>b pol. ownership_split_transfer_st
                      (local_transfer (tf_st (if pol then EA_Assume b else EA_AssumeNot b)))),
     dgs_body := (\<lambda>p. ownership_split_transfer_st (local_transfer (tf_st EA_Nop))),
     dgs_return := (\<lambda>e p. ownership_split_transfer_st (local_transfer (tf_st (EA_Ret e p)))),
     dgs_enter := (\<lambda>ci. ownership_split_enter_transfer_st
                          (local_enter_transfer (\<lambda>d. [(d, enter_st ci d)]))),
     dgs_event := (\<lambda>ev. case ev of Check_Event bc
                     \<Rightarrow> ownership_split_transfer_st (local_transfer (tf_st (EA_Check bc)))),
     dgs_combine_assign := ownership_split_combine_transfer_st gs \<rparr>"

lemma dg_spec_step_ownership_split_st_for:
  "dg_spec_step (ownership_split_dg_spec_st_for gs tf_st enter_st) a
     = ownership_split_transfer_st (local_transfer (tf_st a))"
  unfolding ownership_split_dg_spec_st_for_def
  by (cases a) simp_all

lemma dgs_enter_ownership_split_dg_spec_st_for:
  "enter\<^sup># (ownership_split_dg_spec_st_for gs tf_st enter_st) ci
     = ownership_split_enter_transfer_st (local_enter_transfer (\<lambda>d. [(d, enter_st ci d)]))"
  unfolding ownership_split_dg_spec_st_for_def by simp

lemma dg_spec_combine_transfer_ownership_split_dg_spec_st_for:
  "dg_spec_combine_transfer (ownership_split_dg_spec_st_for gs tf_st enter_st) ci m de
     = ownership_split_combine_transfer_st gs ci m de"
  unfolding dg_spec_combine_transfer_def dgs_combine_def ownership_split_dg_spec_st_for_def
  by (simp add: local_transfer_def local_combine_transfer_def man_with_local_def)

end

