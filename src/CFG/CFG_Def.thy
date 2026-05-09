theory CFG_Def
  imports IMP2_Syntax
begin

(*
  CFG -- Control-Flow Graph Definition.

  A CFG represents a program as a directed graph where:
    - Nodes are program points (natural numbers, allocated during translation).
    - Edges carry edge actions: assignments, branch assumptions, or no-ops.
    - Each edge (u, a, v) means: "go from u to v, performing action a".

  Translation from IMP2 to CFG is in IMP2_to_CFG.thy.
  The equation system over a CFG is in Equations/Constraint_System.thy.
*)

(* ── Program Points ───────────────────────────────────────────── *)

type_synonym pp = nat

(* ── Edge Actions ─────────────────────────────────────────────── *)
(*
  Each edge carries one of:
    EA_Nop          -- unconditional edge (no state change)
    EA_Assign x a   -- assignment: state updated as s(x := aval a s)
    EA_Assume b     -- assume b holds: filter states where bval b s = True
    EA_AssumeNot b  -- assume b fails: filter states where bval b s = False
*)

datatype edge_action =
    EA_Nop
  | EA_Assign   vname aexp
  | EA_Assume   bexp
  | EA_AssumeNot bexp

(* ── CFG Record ───────────────────────────────────────────────── *)

record cfg =
  cfg_entry :: pp
  cfg_exit  :: pp
  cfg_edges :: "(pp * edge_action * pp) set"

(* ── Derived Notions ──────────────────────────────────────────── *)

definition cfg_nodes :: "cfg => pp set" where
  "cfg_nodes g = {cfg_entry g, cfg_exit g}
                 Un Union ((\<lambda>(u, _, v). {u, v}) ` cfg_edges g)"

definition predecessors :: "cfg => pp => (pp * edge_action) set" where
  "predecessors g v = {(u, a) | u a. (u, a, v) : cfg_edges g}"

definition successors :: "cfg => pp => (pp * edge_action) set" where
  "successors g u = {(w, a) | w a. (u, a, w) : cfg_edges g}"

(* ── Well-Formedness ──────────────────────────────────────────── *)

definition cfg_wf :: "cfg => bool" where
  "cfg_wf g = (cfg_entry g \<noteq> cfg_exit g
               \<and> finite (cfg_edges g)
               \<and> (\<forall>(u, _, v) \<in> cfg_edges g. u \<in> cfg_nodes g \<and> v \<in> cfg_nodes g))"

end
