theory TD_Total
  imports
    Abstract_Domain
    Sign_Domain
    Interval_Domain
    Constraint_System
    TD_Interface
    "TD.TD_warrow"
begin

(*
  Track B: Total Correctness via TD_warrow_mono_term
  ===================================================

  Connects the abstract domains to the TD_warrow_mono_term locale from
  vendor/td-verification (stilscher/td-verification, session TD).

  Requirements per domain:
    1. 'd :: order_bot      (typeclass instances for sign/ivl)
    2. widening_precise     (b <= a ==> a ∇ b = a)
    3. wf widening_chains   (via measure m_ivl / trivial for sign)
    4. narrowing_le         (b <= a ==> a △ b <= a)
    5. wf narrowing_chains  (via measure n_ivl)
    6. is_mono_eq T         (RHS monotone w.r.t. env order)
    7. mono_deps T          (dependencies monotone w.r.t. env order)
    8. finite (UNIV :: 'x set)   (PP type must be a finite type)

  PP type for Track B
  -------------------
  We cannot use `type_synonym pp = nat` since nat is infinite and
  TD_warrow_mono_term requires `finite (UNIV :: 'x set)`.

  Instead, define a small finite datatype for each target program.
  Example for a 3-node CFG (entry, loop-head, exit):
*)

(*
datatype pp3 = PP3_Entry | PP3_Loop | PP3_Exit

lemma finite_pp3[simp]: "finite (UNIV :: pp3 set)"
  by (metis finite.emptyI finite_insert pp3.exhaust)
*)

(*
  Sign Domain — Track B obligations
  -----------------------------------
  Needed beyond Track A:
    S1.9:  instantiation sign :: order
    S1.10: instantiation sign :: order_bot
    S1.11: widen_sign = join_sign, widening_precise trivially holds
    B3.3:  is_mono_eq for sign RHS
    B3.4:  mono_deps for sign RHS
*)

(*
  widening_precise for sign: trivial because widen_sign = join_sign
  and join is the least upper bound, so b <= a implies join a b = a.
*)
lemma sign_widening_precise:
  "b ≤ (a :: sign_state) ⟹ widen_sign_state a b = a"
  sorry

(*
  Widening chains for sign are well-founded because sign is a finite lattice
  (height 3: SBot < SNeg/SZero/SPos < STop). Any ascending chain terminates.
*)
lemma sign_wf_widening_chains: "wf {(x, y :: sign). x \<noteq> y \<and> x = widen_sign y x}"
  sorry

(*
  is_mono_eq for sign: the RHS is monotone w.r.t. the pointwise order on environments.
  Key fact: join_sign is monotone, and apply_tf (for sign) is monotone pointwise.
*)
lemma sign_is_mono_eq:
  "is_mono_eq (sign_rhs :: pp_fin ⇒ (pp_fin, sign_state) strategy_tree)"
  sorry

(*
  Interval Domain — Track B obligations
  ----------------------------------------
  Beyond Track A, need I1.13–I1.16 and B3.7–B3.8.
*)

(*
  widening_precise for ivl:
    b ≤ a means Ivl l2 u2 ≤ Ivl l1 u1, i.e. l1 ≤ l2 (left tighter) and u2 ≤ u1 (right tighter).
    widen_ivl (Ivl l1 u1) (Ivl l2 u2):
      left:  if l1 ≤ l2 then l1 else MinInf  — since l1 ≤ l2, result = l1
      right: if u2 ≤ u1 then u1 else PlusInf — since u2 ≤ u1, result = u1
    So widen_ivl a b = Ivl l1 u1 = a. QED (4 cases on eint constructors).
*)
lemma ivl_widening_precise:
  "(b :: ivl) ≤ a ⟹ widen_ivl a b = a"
  sorry

(*
  Measure for widening chains: m_ivl counts finite bounds (0, 1, or 2).
  Analogous to AFP Abs_Int3.thy:263.
*)
definition m_ivl :: "ivl ⇒ nat" where
  "m_ivl iv = (case iv of Ivl l u ⇒
     (case l of MinInf ⇒ 0 | PlusInf ⇒ 0 | Fin _ ⇒ 1) +
     (case u of PlusInf ⇒ 0 | MinInf ⇒ 0 | Fin _ ⇒ 1))"

lemma ivl_wf_widening_chains:
  "wf {(x, y :: ivl). x \<noteq> y \<and> x = widen_ivl y x}"
  sorry

(*
  narrow_ivl: tighten bounds back from ±∞ when the abstract value permits.
  narrowing_le: b ≤ a ⟹ narrow_ivl a b ≤ a  (narrowing never increases).
*)
definition narrow_ivl :: "ivl ⇒ ivl ⇒ ivl" where
  "narrow_ivl a b = (case (a, b) of
     (Ivl l1 u1, Ivl l2 u2) ⇒
       Ivl (if l1 = MinInf then l2 else l1)
           (if u1 = PlusInf then u2 else u1))"

lemma ivl_narrowing_le:
  "(b :: ivl) ≤ a ⟹ narrow_ivl a b ≤ a"
  sorry

(*
  is_mono_eq for ivl: the RHS is monotone w.r.t. the pointwise order on environments.
  This is the main technical lemma of Track B; requires showing join_ivl is monotone
  and apply_tf (for ivl) is monotone.
*)
lemma ivl_is_mono_eq:
  "is_mono_eq (ivl_rhs :: pp_fin ⇒ (pp_fin, ivl_state) strategy_tree)"
  sorry

(*
  Locale instantiations:
  Once the above lemmas are proved, discharge the TD_warrow_mono_term locale.

  interpretation ivl_warrow_mono_term: TD_warrow_mono_term ivl_rhs widen_ivl narrow_ivl
    using ivl_widening_precise ivl_narrowing_le ivl_wf_widening_chains ...
    sorry

  Corollary: total correctness
    theorem goblint_total_sound_ivl:
      assumes "is_mono_eq ivl_rhs" and "mono_deps ivl_rhs"
      shows "solve_dom x"
    ...
*)

end
