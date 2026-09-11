theory Exec_DG_State
  imports Exec_St_Restriction_Refinement "Voblint_Framework.DG_Constraint_Trees"
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

subsection \<open>Classifier-parametric readback\<close>

text \<open>
  The executable local/side readback, generic in the classifier: an
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
end
