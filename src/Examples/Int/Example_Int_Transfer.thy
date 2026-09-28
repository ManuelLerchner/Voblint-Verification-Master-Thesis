theory Example_Int_Transfer
  imports
    Voblint_Analysis_Int.Int_Transfer
    Example_Int_Backward
begin

section \<open>Reaching the composite operations the way the analysis does\<close>

text \<open>
  Every abstract operation the pipeline runs is reached through a dispatcher --
  \<open>int_tf_abs\<close> for an edge action, \<open>enter_int_dom_ci_for\<close> for a call's entry,
  \<open>branch_int_dom_for\<close> for a guard -- rather than by naming the underlying
  primitive. That a primitive is sound in isolation says nothing about whether
  the dispatcher picks it, so the lemmas below go the long way round and pin
  what comes out. Vocabulary: \<open>test_gs\<close> is the variable classifier,
  \<open>int_dom_sipc s i p c\<close> overwrites \<open>top\<close> in the order sign, interval, parity,
  congruence, and \<open>test_env_top\<close>, inherited from \<open>Example_Int_Backward\<close>, is the
  everywhere-unconstrained starting state.
\<close>

text \<open>
  \<open>test_gs\<close> classifies every variable as local, so the entry operation resets
  the whole frame to \<open>top\<close> before binding formals -- the simplest possible
  classifier for exercising \<open>enter_int_dom_for\<close>.
\<close>

definition test_gs :: "vname => bool" where
  "test_gs _ = False"

subsection \<open>Assignment and procedure entry through the registered operations\<close>

text \<open>
  \<open>int_tf_abs\<close> dispatches \<open>EA_Assign\<close> to the mode's assignment operation:
  reached through the dispatcher rather than through \<open>assign_int_dom\<close>
  directly, this confirms the dispatch is wired to the right primitive, not
  just that \<open>assign_int_dom\<close> is sound in isolation.
\<close>

lemma int_tf_abs_once_assign:
  "int_tf_abs Refine_Once (EA_Assign (STR ''x'') (N 5)) test_env_top (STR ''x'') =
   int_dom_of_int 5"
  by simp eval

text \<open>
  The entry operation resets the frame (every variable is local under
  \<open>test_gs\<close>) and binds the single formal \<open>p\<close> to the actual's abstract value.
\<close>

lemma enter_int_dom_ci_for_once_binds_formal:
  "enter_int_dom_ci_for Refine_Once test_gs
     (call_info_of (CallEdge None [STR ''p''] [N 7]) (STR ''f''))
     test_env_top (STR ''p'') =
   int_dom_of_int 7"
  by (simp add: int_tf.op_defs) eval

subsection \<open>Guard refinement through the registered operations\<close>

text \<open>
  The dispatcher's guard case is \<^const>\<open>branch_int_dom_for\<close> at the mode, which
  the bundle derives from \<open>int_refine_ops mode\<close>; there is no per-mode branch to
  pin it against. The abstract branch normalizes against \<open>is_empty_state\<close>, which
  quantifies over an infinite \<open>vname\<close> and so has no code equation; the executable
  filter the bundle derives is what runs. That it narrows \<open>x + 1 = 3\<close> to exactly
  \<open>x = 2\<close> under \<open>Once\<close> and to the congruence component alone under \<open>Never\<close> is
  proved in \<^theory>\<open>Voblint_Examples_Int.Example_Int_Backward\<close>, which this
  theory imports.
\<close>

lemma int_tf_abs_assume_is_branch:
  "int_tf_abs mode (EA_Assume b) = branch_int_dom_for mode b True"
  by simp

subsection \<open>Min/Max special-call dispatch through the registered bundle\<close>

text \<open>
  Sign, Interval, and Parity each combine their real \<open>min\<close> primitive on the
  two literal operands (both positive and odd, so \<open>SPos\<close>/\<open>Ivl 3 3\<close>/\<open>POdd\<close>
  all agree exactly); Congruence has no \<open>min\<close> primitive of its own
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Transfer\<close>'s own note on
  \<open>int_dom_min_raw\<close>/\<open>int_dom_max_raw\<close>), so mode-aware refinement is what
  supplies the congruence component here -- from Parity's \<open>POdd\<close>, not from
  Interval's exact singleton, which is why the result is \<open>mk_congruence 1 2\<close>
  (\"odd\") rather than the sharper \<open>congruence_of_int 3\<close> (\"exactly 3\").
\<close>

lemma int_tf_abs_once_special_min:
  "int_tf_abs Refine_Once
     (EA_Special (Min (N 3) (N 5)) (STR ''x''))
     test_env_top (STR ''x'') =
   int_dom_sipc SPos (Ivl (Fin 3) (Fin 3)) POdd (mk_congruence 1 2)"
  by simp eval

end
