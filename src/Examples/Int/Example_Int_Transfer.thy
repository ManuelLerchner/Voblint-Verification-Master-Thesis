theory Example_Int_Transfer
  imports Voblint_Analysis_Int.Int_Transfer
begin

section \<open>Composite integer-domain transfer functions: examples\<close>

text \<open>
  \<open>test_gs\<close> classifies every variable as local, so the entry operation resets
  the whole frame to \<open>top\<close> before binding formals -- the simplest possible
  classifier for exercising \<open>enter_int_dom_for\<close>.
\<close>

definition test_gs :: "vname => bool" where
  "test_gs _ = False"

definition test_env_top :: "int_dom abs_state" where
  "test_env_top = (%_. top)"

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
  unfolding enter_int_dom_ci_for_def by simp eval

subsection \<open>Guard refinement through the registered operations, mode contrast\<close>

text \<open>
  The same \<open>x + 1 = 3 ==> x = 2\<close> witness as
  \<open>Example_Int_Backward.bfilter_int_dom_once_plus_eq_exact\<close>, in the two
  halves that together say what a single dispatched branch step would: the
  dispatcher's branch case is the mode's own \<open>branch_int_dom_*\<close>, and that
  branch's filter narrows exactly. The dispatch half is an equation between
  operations rather than a computation, because \<open>branch_int_dom_*\<close> collapses
  the lifted filter and \<open>bfilter_lifted\<close> normalizes against
  \<open>is_empty_state\<close>, which quantifies over an infinite \<open>vname\<close> and so has no
  code equation --- only the executable \<open>resolved_st_q\<close> mirror
  \<open>branch_int_dom_*_st\<close> runs.
\<close>

lemma branch_int_dom_for_once_is_branch_int_dom:
  "branch_int_dom_for Refine_Once = branch_int_dom_once"
  by simp

lemma branch_int_dom_for_never_is_branch_int_dom:
  "branch_int_dom_for Refine_Never = branch_int_dom_never"
  by simp

lemma bfilter_once_assume_exact:
  "bfilter_int_dom_once (Eq (Plus (V (STR ''x'')) (N 1)) (N 3)) True
     test_env_top (STR ''x'') =
   int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2)"
  by eval

lemma bfilter_never_assume_congruence_only:
  "bfilter_int_dom_never (Eq (Plus (V (STR ''x'')) (N 1)) (N 3)) True
     test_env_top (STR ''x'') =
   int_dom_sipc STop top PTop (congruence_of_int 2)"
  by eval

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

