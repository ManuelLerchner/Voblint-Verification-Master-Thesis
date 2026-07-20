theory CFG_Def
  imports "Voblint_IMP2.IMP2_Syntax" "HOL-Library.Countable" "HOL-Library.Product_Lexorder"
begin

section \<open>Control-flow graph definition\<close>

text \<open>
  A CFG represents a program as a directed graph where:
    - Nodes are program points (natural numbers, allocated during translation).
    - Edges carry edge actions: assignments, branch assumptions, or no-ops.
    - Each edge (u, a, v) means: ''go from u to v, performing action a''.

  A `cfg` is a record with `nodes`, `edges`, `cfg_entry`, `cfg_exit`, and
  `combines`.  Use the smart constructor `mk_cfg en ex E C` to build CFGs:
  it auto-computes `nodes` from the edges plus endpoints, so every edge and
  combine endpoint is a node by construction.

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

record cfg =
  nodes     :: "pp set"
  edges     :: "(pp \<times> edge_action \<times> pp) set"
  cfg_entry :: pp
  cfg_exit  :: pp
  combines  :: "combine_info set"

subsection \<open>CFG construction\<close>

definition mk_cfg ::
  "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> combine_info set \<Rightarrow> cfg" where
  "mk_cfg entry exit E C =
     \<lparr> nodes = ({entry, exit} \<union> fst ` E \<union> (snd \<circ> snd) ` E
                  \<union> combine_call_node ` C
                  \<union> combine_exit_node ` C
                  \<union> combine_return_node ` C),
       edges = E,
       cfg_entry = entry,
       cfg_exit = exit,
       combines = C
     \<rparr>"

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
