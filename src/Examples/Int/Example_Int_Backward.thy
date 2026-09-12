theory Example_Int_Backward
  imports Voblint_Analysis_Int.Int_Backward
begin

section \<open>What a guard, read backwards, tells the four components\<close>

text \<open>
  A backward filter runs a boolean guard in reverse: given an abstract state and
  the truth value the guard is assumed to take, it returns what each variable
  must have been for the guard to come out that way. The three lemma families
  below run one guard through \<open>bfilter_int_dom_never\<close>, \<open>bfilter_int_dom_once\<close>
  and \<open>bfilter_int_dom_fixpoint\<close> and pin the results by \<open>eval\<close>, so the
  difference between them is exactly what cross-component refinement buys.
  Vocabulary: \<open>int_dom_sipc s i p c\<close> overwrites \<open>top\<close> in the order sign,
  interval, parity, congruence; \<open>congruence_of_int n\<close> is the class containing
  only \<open>n\<close>, and \<open>mk_congruence c m\<close> the class of \<open>c\<close> modulo \<open>m\<close>.
\<close>

text \<open>
  \<open>test_env_top\<close> is the composite domain's own top: every variable
  starts fully unconstrained, so any narrowing shown below comes from the
  guard, not from the starting state.
\<close>

definition test_env_top :: "int_dom abs_state" where
  "test_env_top = (\<lambda>_. top)"

subsection \<open>x + 1 = 3 ==> x = 2\<close>

text \<open>
  The composite analogue of \<open>Example_Congruence_Backward\<close>'s single-domain
  \<open>x + 1 = 3 ==> x = 2\<close> witness. \<open>Refine_Once\<close> is local to each composite
  operation, not to the whole recursive traversal: the guard's own
  \<open>afilter\<close> recursion invokes refinement once inside \<open>inv_plus_int_dom\<close>
  and again at the \<open>V\<close> leaf's \<open>intersect_int_dom_mode\<close>, so two refinement
  rounds run along this single path even under \<open>Once\<close>. A caller who only
  knows \<open>refine Refine_Once d\<close> is one round should not expect
  \<open>bfilter_int_dom_once\<close> to match that bound -- a recursive backward
  filter can invoke refinement at multiple nodes. Here it already reaches
  the exact singleton, so \<open>Refine_Fixpoint\<close> finds nothing further to do.
\<close>

lemma bfilter_int_dom_once_plus_eq_exact:
  "bfilter_int_dom_once
     (Eq (Plus (V (STR ''x'')) (N 1)) (N 3)) True
     test_env_top (STR ''x'') =
   int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2)"
  by eval

lemma bfilter_int_dom_fixpoint_plus_eq_exact:
  "bfilter_int_dom_fixpoint
     (Eq (Plus (V (STR ''x'')) (N 1)) (N 3)) True
     test_env_top (STR ''x'') =
   int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2)"
  by eval

text \<open>
  \<open>Refine_Never\<close> applies no cross-component refinement at all. Congruence's
  own real inverse (\<open>Congruence_Backward.inv_plus_congruence\<close>) still
  narrows the congruence component directly -- that is the component's own
  inversion, not refinement -- but Sign, Interval, and Parity never learn
  about it.
\<close>

lemma bfilter_int_dom_never_plus_eq_congruence_only:
  "bfilter_int_dom_never
     (Eq (Plus (V (STR ''x'')) (N 1)) (N 3)) True
     test_env_top (STR ''x'') =
   int_dom_sipc STop top PTop (congruence_of_int 2)"
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
  The starting state is the one \<open>Example_Int_Domain\<close>'s
  \<open>refinement_round_is_progressive\<close> hands to a single \<open>refine_round\<close>, where the
  sign component stops at \<open>SNonPos\<close>. The guard traversal invokes refinement at
  several nodes instead of once, so it reaches \<open>SZero\<close> here.
\<close>

lemma bfilter_int_dom_once_self_refine_exact:
  "bfilter_int_dom_once
     (Eq (V (STR ''x'')) (V (STR ''x'')))
     True
     ((\<lambda>_. top)((STR ''x'') := int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PEven top))
     (STR ''x'') =
   int_dom_sipc SZero (Ivl (Fin 0) (Fin 0)) PEven (mk_congruence 0 2)"
  by eval

subsection \<open>Congruence precision unavailable from Sign/Interval alone\<close>

lemma bfilter_int_dom_once_congruence_tightens_interval:
  "bfilter_int_dom_once
     (Eq (V (STR ''x'')) (V (STR ''x'')))
     True
     ((\<lambda>_. top)
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
     (Eq (V (STR ''x'')) (V (STR ''x'')))
     True
     ((\<lambda>_. top)
       ((STR ''x'') :=
          int_dom_sipc STop (Ivl (Fin 0) (Fin 10)) PTop (mk_congruence 1 4)))
     (STR ''x'') =
   int_dom_sipc STop (Ivl (Fin 0) (Fin 10)) PTop (mk_congruence 1 4)"
  by eval

lemma int_direct_comparisons_all_modes:
  "map (\<lambda>mode. map (\<lambda>c. aval_int_dom mode (c (V (STR ''x'')) (N 0))
      (\<lambda>_. int_dom_of_int (-1))) [LessEq, Greater, GreaterEq, NotEq])
    [Refine_Never, Refine_Once, Refine_Fixpoint] =
   replicate 3 [int_dom_of_int 1, int_dom_of_int 0,
                int_dom_of_int 0, int_dom_of_int 1]"
  by eval

lemma int_false_disequality_refines:
  "bfilter_int_dom_once (NotEq (Plus (V (STR ''x'')) (N 1)) (N 3))
    False test_env_top (STR ''x'') =
   int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2)"
  by eval


lemma int_division_remainder_modes:
  "map (\<lambda>mode. aval_int_dom mode (Div (N (-7)) (N 3)) (\<lambda>_. top))
      [Refine_Never, Refine_Once, Refine_Fixpoint] =
    [div_int_dom Refine_Never (int_dom_of_int (-7)) (int_dom_of_int 3),
     int_dom_of_int (-2), int_dom_of_int (-2)]"
  "map (\<lambda>mode. aval_int_dom mode (Mod (N (-7)) (N 3)) (\<lambda>_. top))
      [Refine_Once, Refine_Fixpoint] = [int_dom_of_int (-1), int_dom_of_int (-1)]"
  by eval+

lemma int_exact_division_recovers_parity:
  "map (\<lambda>mode. int_parity (aval_int_dom mode
      (Div (Times (N 6) (V (STR ''n''))) (N 3)) (\<lambda>_. top)))
    [Refine_Never, Refine_Once, Refine_Fixpoint] = [PTop, PEven, PEven]"
  "map (\<lambda>mode. int_parity (aval_int_dom mode
      (Div (Plus (Times (N 12) (V (STR ''n''))) (N 3)) (N (-3))) (\<lambda>_. top)))
    [Refine_Never, Refine_Once, Refine_Fixpoint] = [PTop, POdd, POdd]"
  by eval+

definition division_remainder_exp :: exp where
  "division_remainder_exp =
    Mod (Div (Plus (Times (N 12) (V (STR ''n''))) (N 3)) (N 3)) (N 4)"

lemma int_division_remainder_progressive:
  "map (\<lambda>mode. int_ivl (aval_int_dom mode division_remainder_exp
      (\<lambda>_. int_dom_sipc SNonNeg (Ivl (Fin 0) (Fin 20)) PTop top)))
    [Refine_Never, Refine_Once, Refine_Fixpoint] =
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 1) (Fin 1), Ivl (Fin 1) (Fin 1)]"
  "map (\<lambda>mode. int_sign (aval_int_dom mode division_remainder_exp
      (\<lambda>_. int_dom_sipc SNonNeg (Ivl (Fin 0) (Fin 20)) PTop top)))
    [Refine_Never, Refine_Once, Refine_Fixpoint] = [SNonNeg, SNonNeg, SPos]"
  by eval+

end

