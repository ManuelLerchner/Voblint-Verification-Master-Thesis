theory Example_Int_Backward
  imports Voblint_Analysis.Int_Backward
begin

section \<open>Composite integer-domain backward filtering: examples\<close>

text \<open>
  \<open>test_env_top\<close> is the composite domain's own top: every variable
  starts fully unconstrained, so any narrowing shown below comes from the
  guard, not from the starting state.
\<close>

definition test_env_top :: "int_dom abs_state" where
  "test_env_top = (%_. top)"

subsection \<open>x + 1 = 3 ==> x = 2 modulo the I32 wrap\<close>

text \<open>
  Each guard is the elaborated \<^typ>\<open>texp\<close> a compiled \<open>EA_Assume\<close> edge
  carries, so the narrowing reads its operand kinds off the tree.
  Congruence's own inverse (\<open>Congruence_Backward.inv_plus_congruence_ik\<close>,
  composed with \<open>cong_unwrap\<close> to reconcile the \<open>ik_norm\<close>-wrapped result
  register) runs inside \<open>int_dom\<close>'s \<open>inv_plus\<close>/\<open>inv_minus\<close>/\<open>inv_times\<close>,
  so the congruence component narrows even where cross-component refinement
  is switched off.

  What the sum's kind costs is the singleton. The addition is normed at
  \<^const>\<open>I32\<close>, so the strongest statement about \<open>x\<close> is \<open>2\<close> modulo \<open>2 ^ 32\<close>,
  not \<open>{2}\<close>; pinning it to \<open>{2}\<close> needs the range fact that \<open>x\<close> is
  representable at \<^const>\<open>I32\<close>, which \<^const>\<open>test_env_top\<close> deliberately
  withholds. Refinement therefore reaches Parity -- \<open>2\<close> modulo an even
  modulus is even -- but Sign and Interval stay at top.
\<close>

lemma bfilter_int_dom_once_plus_eq_congruence:
  "bfilter_int_dom_once
     (elaborate_syn default_tyenv (Eq (Plus (V (STR ''x'')) (N 1)) (N 3))) True
     test_env_top (STR ''x'') =
   int_dom_sipc STop top PEven (mk_congruence 2 4294967296)"
  by eval

lemma bfilter_int_dom_fixpoint_plus_eq_congruence:
  "bfilter_int_dom_fixpoint
     (elaborate_syn default_tyenv (Eq (Plus (V (STR ''x'')) (N 1)) (N 3))) True
     test_env_top (STR ''x'') =
   int_dom_sipc STop top PEven (mk_congruence 2 4294967296)"
  by eval

text \<open>
  \<open>Refine_Never\<close> skips cross-component refinement, so Parity stays at top
  too; Congruence's own inverse still narrows inside \<open>inv_plus\<close>, which is
  where this lemma's congruence component comes from.
\<close>

lemma bfilter_int_dom_never_plus_eq_congruence_only:
  "bfilter_int_dom_never
     (elaborate_syn default_tyenv (Eq (Plus (V (STR ''x'')) (N 1)) (N 3))) True
     test_env_top (STR ''x'') =
   int_dom_sipc STop top PTop (mk_congruence 2 4294967296)"
  by eval

subsection \<open>Distributed information, exact after refinement\<close>

text \<open>
  The guard \<open>x = x\<close> is tautological and contributes no semantic
  restriction of its own. What matters is the starting state: \<open>x\<close> already
  denotes the singleton \<open>{0}\<close> through the intersection of Interval
  \<open>[-1,0]\<close> and Parity \<open>PEven\<close> (\<open>-1\<close> is odd, so only \<open>0\<close> is both in range
  and even), but that fact is distributed across components -- neither
  Interval nor Parity is a singleton on its own. Traversing the tautological
  guard still runs the composite intersection/refinement machinery, which
  propagates the existing information until Sign, Interval, and Congruence
  all expose the same precision Parity and Interval jointly already implied.
  This is \<open>refinement_round_is_progressive\<close>'s (\<open>Example_Int_Domain\<close>)
  own witness, reached here through the guard machinery instead of a direct
  \<open>refine_round\<close> call.
\<close>

lemma bfilter_int_dom_once_self_refine_exact:
  "bfilter_int_dom_once
     (elaborate_syn default_tyenv (Eq (V (STR ''x'')) (V (STR ''x''))))
     True
     ((%_. top)((STR ''x'') := int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PEven top))
     (STR ''x'') =
   int_dom_sipc SZero (Ivl (Fin 0) (Fin 0)) PEven (mk_congruence 0 2)"
  by eval

subsection \<open>Congruence precision unavailable from Sign/Interval alone\<close>

lemma bfilter_int_dom_once_congruence_tightens_interval:
  "bfilter_int_dom_once
     (elaborate_syn default_tyenv (Eq (V (STR ''x'')) (V (STR ''x''))))
     True
     ((%_. top)
       ((STR ''x'') :=
          int_dom_sipc STop (Ivl (Fin 0) (Fin 10)) PTop (mk_congruence 1 4)))
     (STR ''x'') =
   int_dom_sipc SPos (Ivl (Fin 1) (Fin 9)) POdd (mk_congruence 1 4)"
  by eval

text \<open>
  Without refinement, the same input passes through unchanged: no Sign or
  Interval operator alone can derive \<open>[1,9]\<close>/\<open>SPos\<close>/\<open>POdd\<close> from \<open>[0,10]\<close>
  and \<open>x = 1 mod 4\<close> -- only cross-component refinement extracts it.
\<close>

lemma bfilter_int_dom_never_congruence_unused:
  "bfilter_int_dom_never
     (elaborate_syn default_tyenv (Eq (V (STR ''x'')) (V (STR ''x''))))
     True
     ((%_. top)
       ((STR ''x'') :=
          int_dom_sipc STop (Ivl (Fin 0) (Fin 10)) PTop (mk_congruence 1 4)))
     (STR ''x'') =
   int_dom_sipc STop (Ivl (Fin 0) (Fin 10)) PTop (mk_congruence 1 4)"
  by eval

end

