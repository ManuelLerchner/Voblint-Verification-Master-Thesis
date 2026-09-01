theory Example_Per_Origin_Widening_Precision
  imports
    "Voblint_Solver.Solver_Menu"
    "Voblint_Analysis.Ivl_Exec"
begin

section \<open>Per-origin widening keeps a precision the joined-then-widened slot loses\<close>

text \<open>
  Two producers write a different constant to the same global unknown, and nothing else
  happens: each producer issues one \<^const>\<open>Side\<close> contribution and stabilises.  The
  concrete slot value is therefore exactly \<open>[1, 2]\<close>, and any update rule reporting more
  than that is losing precision to its own combination discipline rather than to the
  program.

  This separates the two widening rules on \<^const>\<open>solver_menu\<close>, which agree everywhere a
  global has a single producer:

  \<^item> \<^const>\<open>update_global_warrowing_apinis\<close> widens the slot value \<^emph>\<open>after\<close> the join.  The
    left producer's write leaves the slot at \<open>[1, 1]\<close>.  The right producer's write then
    recomputes \<^const>\<open>sup_over_origins\<close> as \<open>[1, 2]\<close> and widens \<open>[1, 1] \<nabla> [1, 2]\<close>; the upper
    bound grew, so it goes to \<^const>\<open>PlusInf\<close>.  The growth is an artifact of two producers
    sharing one slot -- neither producer's own contribution ever moved.
  \<^item> \<^const>\<open>update_global_warrowing_per_origin\<close> widens each contribution against that
    origin's previous contribution and joins afterwards.  Both writes are first writes for
    their origin, so the \<open>bot \<nabla> x = x\<close> law (\<^theory>\<open>Voblint_Analysis.Interval_Warrowing\<close>)
    keeps each exact, and the read joins them to \<open>[1, 2]\<close>.

  The narrowing half of warrowing cannot repair the joined rule here: once both producers
  are stable neither re-issues its contribution, so there is no later recomputation for
  \<^const>\<open>narrow\<close> to descend from and \<open>[1, +inf]\<close> is a genuine fixpoint.
\<close>

datatype two_writer_unknown = TW_Main | TW_Left | TW_Right
datatype two_writer_global = TW_Slot

text \<open>\<open>TW_Main\<close> forces both producers before reading the slot; the producers carry no local
  value of their own, so the slot is the only thing the run computes.\<close>
fun two_writer_eqs :: "(two_writer_unknown, two_writer_global, ivl) eqsT" where
  "two_writer_eqs TW_Main =
     QueryL TW_Left (\<lambda>_. QueryL TW_Right (\<lambda>_. QueryG TW_Slot Answer))"
| "two_writer_eqs TW_Left = Side TW_Slot (Ivl (Fin 1) (Fin 1)) (Answer bot)"
| "two_writer_eqs TW_Right = Side TW_Slot (Ivl (Fin 2) (Fin 2)) (Answer bot)"

subsection \<open>The slot under every update rule at once\<close>

text \<open>\<open>join\<close> and \<open>per_origin\<close> agree at the exact \<open>[1, 2]\<close>: neither widens, and storing a
  contribution per origin then taking \<^const>\<open>sup_over_origins\<close> reconstructs the value
  accumulating them into one slot produces.  They are the precision ceiling on this
  system, and \<open>warrow_per_origin\<close> meets it while keeping the termination guarantee that
  \<open>join\<close> and \<open>per_origin\<close> do not carry.\<close>
lemma two_writer_slot_across_update_rules:
  "run_menu id two_writer_eqs TW_Main (Inr TW_Slot)
     = [(STR ''join'',              Ivl (Fin 1) (Fin 2)),
        (STR ''per_origin'',        Ivl (Fin 1) (Fin 2)),
        (STR ''warrow'',            Ivl (Fin 1) PlusInf),
        (STR ''warrow_per_origin'', Ivl (Fin 1) (Fin 2))]"
  by eval

subsection \<open>The two widening rules, named separately\<close>

text \<open>The contrast the menu row above shows, pinned as its own pair of facts so a change to
  either widening rule fails on the claim it breaks rather than on a list mismatch.\<close>

lemma two_writer_slot_warrow_loses_upper_bound:
  "snd (TD_side_warrowing_apinis_Interp_solve two_writer_eqs TW_Main) (Inr TW_Slot)
     = Ivl (Fin 1) PlusInf"
  by eval

lemma two_writer_slot_warrow_per_origin_exact:
  "snd (TD_side_warrowing_per_origin_Interp_solve two_writer_eqs TW_Main) (Inr TW_Slot)
     = Ivl (Fin 1) (Fin 2)"
  by eval

end
