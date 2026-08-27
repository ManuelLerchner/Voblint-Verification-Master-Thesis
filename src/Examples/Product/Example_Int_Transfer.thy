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

text \<open>These witnesses build edge actions by hand rather than compiling a program, so
  the payloads are elaborated against \<^const>\<open>default_tyenv\<close> -- every variable at
  \<^const>\<open>I32\<close>, which is what an unannotated source program declares.\<close>

subsection \<open>Assignment and procedure entry through the registered bundle\<close>

text \<open>
  \<open>apply_tf\<close> dispatches \<open>EA_Assign\<close> to \<open>tf_assign\<close>: reached through
  \<open>int_tf_once_for\<close> rather than \<open>assign_int_dom\<close> directly, this confirms
  the bundle's \<open>tf_assign\<close> field is wired to the right primitive, not just
  that \<open>assign_int_dom\<close> is sound in isolation.
\<close>

lemma apply_tf_once_assign:
  "apply_tf (int_tf_once_for test_gs) (EA_Assign (STR ''x'') (elaborate_to default_tyenv (default_tyenv (STR ''x'')) (N 5))) test_env_top (STR ''x'') =
   int_dom_of_int 5"
  by eval

text \<open>
  \<open>tf_enter\<close> resets the frame (every variable is local under \<open>test_gs\<close>)
  and binds the single formal \<open>p\<close> to the actual's abstract value.
\<close>

lemma tf_enter_once_binds_formal:
  "tf_enter (int_tf_once_for test_gs) [STR ''p'']
     (compile_actuals default_tyenv [STR ''p''] [N 7]) test_env_top (STR ''p'') =
   int_dom_of_int 7"
  by eval

subsection \<open>Guard refinement through the registered bundle, mode contrast\<close>

text \<open>
  The same \<open>x + 1 = 3 ==> x = 2\<close> witness as
  \<open>Example_Int_Backward.bfilter_int_dom_once_plus_eq_exact\<close>, now reached
  through \<open>apply_tf\<close>'s \<open>EA_Assume\<close> dispatch: confirms \<open>tf_branch\<close> is wired
  to \<open>bfilter_int_dom_once\<close>, not merely that the underlying filter is
  sound in isolation.
\<close>

text \<open>
  \<^const>\<open>test_env_top\<close> starts \<open>x\<close> unbounded, and that is what stops the product
  pinning it. The guard's backward filter gives congruence the exact answer --
  \<open>x \<equiv> 2\<close> -- but modulo \<^term>\<open>4294967296::int\<close>, because the operation is an
  \<^const>\<open>I32\<close> addition. A congruence class that wide selects a single value
  only against a bounded interval, and the entry interval here has no bounds,
  so nothing propagates back to sign or interval.

  Seeding \<open>x\<close> at its kind's range instead of at \<^const>\<open>top\<close> would close it:
  \<^term>\<open>ik_range I32\<close> is exactly one residue wide, so the two together pin
  \<open>x = 2\<close>. That is a property of the entry state, not of the transfer under
  test, which is why this witness records the components as they stand rather
  than asserting a reduction the entry state cannot support.
\<close>

lemma apply_tf_once_assume_congruence_mod_i32:
  "apply_tf (int_tf_once_for test_gs)
     (EA_Assume (elaborate_syn default_tyenv (Eq (Plus (V (STR ''x'')) (N 1)) (N 3))))
     test_env_top (STR ''x'') =
   int_dom_sipc STop (Ivl MinInf PlusInf) PEven (mk_congruence 2 4294967296)"
  by eval

lemma apply_tf_never_assume_congruence_only:
  "apply_tf (int_tf_never_for test_gs)
     (EA_Assume (elaborate_syn default_tyenv (Eq (Plus (V (STR ''x'')) (N 1)) (N 3))))
     test_env_top (STR ''x'') =
   int_dom_sipc STop top PTop (mk_congruence 2 4294967296)"
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

  Sign answers \<^const>\<open>STop\<close> rather than \<^const>\<open>SPos\<close>, and that is the write
  site's conversion, not the \<open>min\<close> primitive: \<^const>\<open>SPos\<close> concretizes to
  every positive integer, so converting it to \<^const>\<open>I32\<close> cannot rule out a
  value that wraps negative. A magnitude-free domain has no way to answer that
  question, which is why the product carries Interval alongside it.
\<close>

lemma apply_tf_once_special_min:
  "apply_tf (int_tf_once_for test_gs)
     (EA_Special (Min (default_tyenv (STR ''x'')) (TN I32 3) (TN I32 5)) (STR ''x''))
     test_env_top (STR ''x'') =
   int_dom_sipc STop (Ivl (Fin 3) (Fin 3)) POdd (mk_congruence 1 2)"
  by eval

end

