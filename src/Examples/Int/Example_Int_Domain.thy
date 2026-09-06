section \<open>Example: exact emptiness in the composite integer domain\<close>

theory Example_Int_Domain
  imports "Voblint_Analysis_Int.Int_Arithmetic"
begin

text \<open>
  Componentwise bottom tests miss contradictions between individually inhabited
  abstractions. The composite test decides emptiness of the shared integer
  concretization.
\<close>

lemma sign_interval_contradiction:
  "is_empty (int_dom_sip SPos (Ivl (Fin (-2)) (Fin (-1))) PTop)"
  by eval

lemma sign_interval_components_inhabited:
  "gamma_sign SPos \<noteq> {}"
  "gamma_ivl (Ivl (Fin (-2)) (Fin (-1))) \<noteq> {}"
  "gamma_parity PTop \<noteq> {}"
proof -
  have sign_witness: "1 \<in> gamma_sign SPos" by simp
  have ivl_witness: "-1 \<in> gamma_ivl (Ivl (Fin (-2)) (Fin (-1)))" by simp
  have parity_witness: "0 \<in> gamma_parity PTop" by simp
  show "gamma_sign SPos \<noteq> {}" using sign_witness by blast
  show "gamma_ivl (Ivl (Fin (-2)) (Fin (-1))) \<noteq> {}" using ivl_witness by blast
  show "gamma_parity PTop \<noteq> {}" using parity_witness by blast
qed

lemma interval_parity_contradiction:
  "is_empty (int_dom_sip STop (Ivl (Fin 0) (Fin 0)) POdd)"
  by eval

lemma interval_parity_components_inhabited:
  "gamma_sign STop \<noteq> {}"
  "gamma_ivl (Ivl (Fin 0) (Fin 0)) \<noteq> {}"
  "gamma_parity POdd \<noteq> {}"
proof -
  have sign_witness: "0 \<in> gamma_sign STop" by simp
  have ivl_witness: "0 \<in> gamma_ivl (Ivl (Fin 0) (Fin 0))" by simp
  have parity_witness: "1 \<in> gamma_parity POdd" by simp
  show "gamma_sign STop \<noteq> {}" using sign_witness by blast
  show "gamma_ivl (Ivl (Fin 0) (Fin 0)) \<noteq> {}" using ivl_witness by blast
  show "gamma_parity POdd \<noteq> {}" using parity_witness by blast
qed

lemma compatible_components_nonbottom:
  "\<not> is_empty (int_dom_sip SNonNeg (Ivl (Fin 0) (Fin 1)) POdd)"
  by eval

lemma compatible_components_witness:
  "1 \<in> gamma (int_dom_sip SNonNeg (Ivl (Fin 0) (Fin 1)) POdd)"
  by (simp add: int_dom_sip_def gamma_int_dom_def top_int_dom_ext_def)


text \<open>
  Congruence can contradict the bounded range or Parity while every involved
  component remains inhabited. Compatible constraints retain their common
  witness.
\<close>

lemma interval_congruence_contradiction:
  "is_empty
    (int_dom_sipc
      STop
      (Ivl (Fin 0) (Fin 0))
      PTop
      (mk_congruence 1 2))"
  by eval

lemma parity_congruence_contradiction:
  "is_empty
    (int_dom_sipc
      STop
      (top :: ivl)
      PEven
      (mk_congruence 1 2))"
  by eval

lemma congruence_components_inhabited:
  "gamma_ivl (Ivl (Fin 0) (Fin 0)) \<noteq> {}"
  "gamma_parity PEven \<noteq> {}"
  "gamma_congruence (mk_congruence 1 2) \<noteq> {}"
proof -
  have "0 \<in> gamma_ivl (Ivl (Fin 0) (Fin 0))" by simp
  then show "gamma_ivl (Ivl (Fin 0) (Fin 0)) \<noteq> {}" by blast
  have "0 \<in> gamma_parity PEven" by simp
  then show "gamma_parity PEven \<noteq> {}" by blast
  have "1 \<in> gamma_congruence (mk_congruence 1 2)" by simp
  then show "gamma_congruence (mk_congruence 1 2) \<noteq> {}" by blast
qed

lemma compatible_four_components_nonbottom:
  "\<not> is_empty
    (int_dom_sipc
      SNonNeg
      (Ivl (Fin 0) (Fin 3))
      POdd
      (mk_congruence 1 2))"
  by eval

lemma compatible_four_components_witness:
  "1 \<in> gamma
    (int_dom_sipc
      SNonNeg
      (Ivl (Fin 0) (Fin 3))
      POdd
      (mk_congruence 1 2))"
  by (simp add: int_dom_sipc_def gamma_int_dom_def top_int_dom_ext_def)



section \<open>Progressive integer-domain refinement\<close>

lemma congruence_refines_interval_bounds:
  "int_ivl
    (refine_congruence
      (int_dom_sipc
        STop
        (Ivl (Fin 0) (Fin 10))
        PTop
        (mk_congruence 1 4))) =
   Ivl (Fin 1) (Fin 9)"
  by eval

lemma parity_exports_congruence_fact:
  "int_congruence
    (refine_congruence
      (int_dom_sipc
        STop
        (top :: ivl)
        POdd
        (top :: congruence))) =
   mk_congruence 1 2"
  by eval

lemma congruence_refinement_detects_contradiction:
  "is_empty
    (refine_congruence
      (int_dom_sipc
        STop
        (Ivl (Fin 0) (Fin 0))
        PTop
        (mk_congruence 1 2)))"
  by eval

definition progressive_refinement_input :: int_dom where
  "progressive_refinement_input =
     int_dom_sipc
       STop
       (Ivl (Fin (-1)) (Fin 0))
       PEven
       (top :: congruence)"

lemma refinement_round_is_progressive:
  "refine_round progressive_refinement_input =
   int_dom_sipc
     SNonPos
     (Ivl (Fin 0) (Fin 0))
     PEven
     (mk_congruence 0 2)"
  by eval

lemma refinement_once_sign:
  "int_sign
    (refine Refine_Once progressive_refinement_input) =
   SNonPos"
  by eval

lemma refinement_fixpoint_result:
  "refine Refine_Fixpoint progressive_refinement_input =
   int_dom_sipc
     SZero
     (Ivl (Fin 0) (Fin 0))
     PEven
     (mk_congruence 0 2)"
  by eval

lemma refinement_once_not_fixpoint:
  "refine Refine_Once progressive_refinement_input \<noteq>
   refine Refine_Fixpoint progressive_refinement_input"
  by eval

lemma refinement_fixpoint_collapses_bottom:
  "refine Refine_Fixpoint
    (int_dom_sipc
      STop
      (Ivl (Fin 0) (Fin 0))
      PTop
      (mk_congruence 1 2)) =
   (bot :: int_dom)"
  by eval


section \<open>Composite integer arithmetic\<close>

definition arithmetic_left :: int_dom where
  "arithmetic_left =
     int_dom_sipc
       SNeg
       (Ivl (Fin (-1)) (Fin (-1)))
       POdd
       (top :: congruence)"

definition arithmetic_right :: int_dom where
  "arithmetic_right =
     int_dom_sipc
       SNonNeg
       (Ivl (Fin 0) (Fin 1))
       POdd
       (top :: congruence)"

text \<open>
  The two operands each describe a concrete odd value. Their independent raw
  sums expose the progressive-refinement witness: Sign loses the zero result,
  while Interval, Parity, and Congruence recover it across successive rounds.
\<close>

lemma arithmetic_raw_produces_progressive_input:
  "plus_int_dom_raw arithmetic_left arithmetic_right =
   progressive_refinement_input"
  by eval

lemma arithmetic_never_is_raw:
  "plus_int_dom Refine_Never arithmetic_left arithmetic_right =
   plus_int_dom_raw arithmetic_left arithmetic_right"
  by eval

lemma arithmetic_once_result:
  "plus_int_dom Refine_Once arithmetic_left arithmetic_right =
   int_dom_sipc
     SNonPos
     (Ivl (Fin 0) (Fin 0))
     PEven
     (mk_congruence 0 2)"
  by eval

lemma arithmetic_fixpoint_result:
  "plus_int_dom Refine_Fixpoint arithmetic_left arithmetic_right =
   int_dom_sipc
     SZero
     (Ivl (Fin 0) (Fin 0))
     PEven
     (mk_congruence 0 2)"
  by eval

lemma arithmetic_once_not_fixpoint:
  "plus_int_dom Refine_Once arithmetic_left arithmetic_right ~=
   plus_int_dom Refine_Fixpoint arithmetic_left arithmetic_right"
  by eval

lemma arithmetic_retains_congruence:
  "int_congruence
    (plus_int_dom Refine_Never
      (int_dom_sipc STop (top :: ivl) PTop (mk_congruence 1 4))
      (int_dom_sipc STop (top :: ivl) PTop (mk_congruence 3 6))) =
   mk_congruence 0 2"
  by eval

lemma arithmetic_literal_embedding:
  "int_dom_of_int (-3) =
   int_dom_sipc
     SNeg
     (Ivl (Fin (-3)) (Fin (-3)))
     POdd
     (mk_congruence (-3) 0)"
  by eval

definition arithmetic_env :: "vname => int_dom" where
  "arithmetic_env x =
     (if x = STR ''x'' then arithmetic_left
      else if x = STR ''y'' then arithmetic_right
      else top)"

lemma arithmetic_evaluator_refines_each_operation:
  "aval_int_dom Refine_Fixpoint
    (Plus (V (STR ''x'')) (V (STR ''y'')))
    arithmetic_env =
   int_dom_sipc
     SZero
     (Ivl (Fin 0) (Fin 0))
     PEven
     (mk_congruence 0 2)"
  by eval
end
