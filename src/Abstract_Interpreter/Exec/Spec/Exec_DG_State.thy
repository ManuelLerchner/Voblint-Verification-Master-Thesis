theory Exec_DG_State
  imports Default_St_Restriction_Refinement "Voblint_Framework.DG_Constraint_Programs"
begin

section \<open>The executable carrier and its readback\<close>

text \<open>
  The verified solver uses the executable association-list carrier \<open>'a default_st\<close>, while
  soundness is stated over function-valued abstract states. This theory is the bottom of the
  bridge: the D/G product's lattice structure and the classifier-parametric readback
  \<open>dg_state_to_fun\<close> that lifts \<^const>\<open>default_st_to_fun\<close> to that product. Everything
  here is carrier-level -- no specification, no transfer, no equation shape -- so a
  domain's executable mirror is related to its abstract state once, here, and the
  specification layers above never restate it.

  D/G lattice operations are componentwise, so the product inherits the order, join, bottom,
  equality, and widening operations the solver requires.
\<close>


subsection \<open>Classifier-parametric readback\<close>

text \<open>
  The executable local/side readback is \<^const>\<open>default_st_to_fun\<close>, generic in
  the classifier: an executable state is written with a declaration-driven classifier,
  so reading it back needs the same classifier or the readback consults the wrong slot.
  \<open>dg_state_to_fun\<close> applies it to both components.
\<close>

definition dg_state_to_fun ::
  "(vname => bool) =>
   (('a::bot) default_st, ('b::bot) default_st) dg_state => ('a abs_state, 'b abs_state) dg_state"
where
  "dg_state_to_fun \<G> d =
    DG (default_st_to_fun \<G> (dg_local d)) (default_st_to_fun \<G> (dg_global d))"

lemma dg_state_to_fun_simps [simp]:
  "dg_local (dg_state_to_fun \<G> d) = default_st_to_fun \<G> (dg_local d)"
  "dg_global (dg_state_to_fun \<G> d) = default_st_to_fun \<G> (dg_global d)"
  "dg_state_to_fun \<G> (DG a b) = DG (default_st_to_fun \<G> a) (default_st_to_fun \<G> b)"
  by (simp_all add: dg_state_to_fun_def)

lemma dg_state_to_fun_bot [simp]:
  "dg_state_to_fun \<G> (bot :: ('a::bounded_semilattice_sup_bot default_st,
                         'b::bounded_semilattice_sup_bot default_st) dg_state) = bot"
  by (simp add: bot_dg_state_def)
end
