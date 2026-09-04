theory Example_Int_Transfer
  imports Voblint_Analysis.Int_Transfer
begin

section \<open>Composite integer-domain transfer functions: examples\<close>

text \<open>
  \<open>test_gs\<close> classifies every variable as local, so \<open>tf_enter\<close> resets the
  whole frame to \<open>top\<close> before binding formals -- the simplest possible
  classifier for exercising \<open>enter_int_dom_for\<close>.
\<close>

definition test_gs :: "vname => bool" where
  "test_gs _ = False"

definition test_env_top :: "int_dom abs_state" where
  "test_env_top = (%_. top)"

subsection \<open>Assignment and procedure entry through the registered bundle\<close>

text \<open>
  \<open>apply_tf\<close> dispatches \<open>EA_Assign\<close> to \<open>tf_assign\<close>: reached through
  \<open>int_tf_once_for\<close> rather than \<open>assign_int_dom\<close> directly, this confirms
  the bundle's \<open>tf_assign\<close> field is wired to the right primitive, not just
  that \<open>assign_int_dom\<close> is sound in isolation.
\<close>

lemma apply_tf_once_assign:
  "apply_tf (int_tf_once_for test_gs) (EA_Assign (STR ''x'') (N 5)) test_env_top (STR ''x'') =
   int_dom_of_int 5"
  unfolding int_tf_once_for_def by simp eval

text \<open>
  \<open>tf_enter\<close> resets the frame (every variable is local under \<open>test_gs\<close>)
  and binds the single formal \<open>p\<close> to the actual's abstract value.
\<close>

lemma tf_enter_once_binds_formal:
  "snd (tf_enter (int_tf_once_for test_gs)
     (call_info_of (CallEdge None [STR ''p''] [N 7]) (STR ''f''))
     test_env_top) (STR ''p'') =
   int_dom_of_int 7"
  unfolding int_tf_once_for_def by simp eval

subsection \<open>Guard refinement through the registered bundle, mode contrast\<close>

text \<open>
  The same \<open>x + 1 = 3 ==> x = 2\<close> witness as
  \<open>Example_Int_Backward.bfilter_int_dom_once_plus_eq_exact\<close>, in the two
  halves that together say what a single \<open>apply_tf\<close> run would: the bundle's
  \<open>tf_branch\<close> field is the mode's own \<open>branch_int_dom_*\<close>, and that branch's
  filter narrows exactly. The dispatch half is an equation between
  operations rather than a computation, because \<open>branch_int_dom_*\<close> collapses
  the lifted filter and \<open>bfilter_lifted\<close> normalizes against
  \<open>is_empty_state\<close>, which quantifies over an infinite \<open>vname\<close> and so has no
  code equation --- only the executable \<open>resolved_st_q\<close> mirror
  \<open>branch_int_dom_*_st\<close> runs.
\<close>

lemma tf_branch_once_is_branch_int_dom:
  "tf_branch (int_tf_once_for test_gs) = branch_int_dom_once"
  by (simp add: int_tf_once_for_def)

lemma tf_branch_never_is_branch_int_dom:
  "tf_branch (int_tf_never_for test_gs) = branch_int_dom_never"
  by (simp add: int_tf_never_for_def)

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
  (\<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>'s own note on
  \<open>int_dom_min_raw\<close>/\<open>int_dom_max_raw\<close>), so mode-aware refinement is what
  supplies the congruence component here -- from Parity's \<open>POdd\<close>, not from
  Interval's exact singleton, which is why the result is \<open>mk_congruence 1 2\<close>
  (\"odd\") rather than the sharper \<open>congruence_of_int 3\<close> (\"exactly 3\").
\<close>

lemma apply_tf_once_special_min:
  "apply_tf (int_tf_once_for test_gs)
     (EA_Special (Min (N 3) (N 5)) (STR ''x''))
     test_env_top (STR ''x'') =
   int_dom_sipc SPos (Ivl (Fin 3) (Fin 3)) POdd (mk_congruence 1 2)"
  unfolding int_tf_once_for_def by simp eval

end

