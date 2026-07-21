theory CFG_Def
  imports "Voblint_IMP2.IMP2_Syntax" "HOL-Library.Countable" "HOL-Library.Product_Lexorder"
begin

section \<open>Control-flow graph definition\<close>

text \<open>
  A \<open>cfg\<close> is an interprocedural control-flow graph over program points:
    - an entry location and an exit location,
    - a set of \<open>edges\<close> (u, a, v), meaning ''go from u to v performing action a'',
    - a set of \<open>combines\<close> matching call sites to their return targets.
  Program points are natural numbers, allocated during translation.  Build one with the
  constructor \<open>mk_cfg en ex E C\<close>.

  Translation from IMP2 to CFG is in IMP2_Proc_to_CFG.thy.
  The equation system over a CFG is in Equations/Constraint_System.thy.
\<close>

subsection \<open>Program points\<close>

type_synonym pp = nat

subsection \<open>Edge actions\<close>

text \<open>
  Each edge carries one of:
    EA_Nop          -- unconditional edge (no state change)
    EA_Assign x a   -- assignment: state updated as s(x := aval a s)
    EA_Assume b     -- assume b holds: filter states where bval b s = True
    EA_AssumeNot b  -- assume b fails: filter states where bval b s = False
\<close>

datatype edge_action =
    EA_Nop
  | EA_Assign   vname aexp
  | EA_Assume   bexp
  | EA_AssumeNot bexp
  | EA_Enter    "vname list" "aexp list"
      (* call/scope entry: initialize fresh callee locals from caller actuals *)

instance edge_action :: countable
  by countable_datatype

type_synonym combine_info = "pp * pp * pp * vname option"

definition combine_call_node :: "combine_info \<Rightarrow> pp" where
  "combine_call_node ci = (case ci of (call, ex, ret, dst) \<Rightarrow> call)"

definition combine_exit_node :: "combine_info \<Rightarrow> pp" where
  "combine_exit_node ci = (case ci of (call, ex, ret, dst) \<Rightarrow> ex)"

definition combine_return_node :: "combine_info \<Rightarrow> pp" where
  "combine_return_node ci = (case ci of (call, ex, ret, dst) \<Rightarrow> ret)"

definition combine_dst :: "combine_info \<Rightarrow> vname option" where
  "combine_dst ci = (case ci of (call, ex, ret, dst) \<Rightarrow> dst)"

subsection \<open>CFG record\<close>

text \<open>
  The record is exactly the interprocedural control-flow structure the concrete semantics
  rides on: the distinguished locations \<open>cfg_entry\<close> and \<open>cfg_exit\<close>, the labelled
  transition relation \<open>edges\<close>, and the call/return matching relation \<open>combines\<close> --- a
  \<open>(call, exit, return, dst)\<close> tuple linking three program points, not a labelled edge.
  \<open>valid_ltr\<close>'s closure rules read \<open>cfg_entry\<close>, \<open>edges\<close>, and
  \<open>combines\<close>; \<open>cfg_exit\<close> names the end location at which termination/exit reachability
  is stated.  The record carries no derived or tooling fields: the node set a graph walk
  would need is reconstructed from \<open>edges\<close> where required (e.g. visualization), and solver
  edge/predecessor enumeration lives in a separate theory in the analysis session.
\<close>
record cfg =
  edges     :: "(pp \<times> edge_action \<times> pp) set"
  cfg_entry :: pp
  cfg_exit  :: pp
  combines  :: "combine_info set"

subsection \<open>CFG construction\<close>

definition mk_cfg ::
  "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> combine_info set \<Rightarrow> cfg" where
  "mk_cfg entry exit E C =
     \<lparr> edges = E, cfg_entry = entry, cfg_exit = exit, combines = C \<rparr>"

declare mk_cfg_def[simp]

(* Affine shift along program points compile c (n+k) is compile c n with all pp+k. *)

definition offset_edges :: "nat \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> (pp \<times> edge_action \<times> pp) set" where
  "offset_edges k E = (\<lambda>(u,a,v). (u + k, a, v + k)) ` E"

lemma offset_edges_Un[simp]:
  "offset_edges k (A \<union> B) = offset_edges k A \<union> offset_edges k B"
  unfolding offset_edges_def by force

subsection \<open>Edge-action classification\<close>

definition is_enter_action :: "edge_action \<Rightarrow> bool" where
  "is_enter_action a = (case a of EA_Enter _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

subsection \<open>Executable examples\<close>

value "cfg_entry (mk_cfg 0 2 {(0, EA_Nop, 1), (1, EA_Nop, 2)} {})"
value "cfg_exit  (mk_cfg 0 2 {(0, EA_Nop, 1), (1, EA_Nop, 2)} {})"

end
