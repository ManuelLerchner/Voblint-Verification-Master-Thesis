theory Direct_Equations
  imports Constraint_System IMP2_to_CFG TD_Interface
begin

(*
  Direct Equation System AST \<rightarrow> equations, no CFG intermediate.

  Alternative to the CFG-based route:
    CFG route:  compile c n  \<rightarrow>  cfg record  \<rightarrow>  rhs via cfg_edges
    Direct:     predecessors_of c n v        \<rightarrow>  rhs directly

  The label allocation scheme mirrors compile exactly (same entry/exit
  for every command), so the two approaches produce identical equation
  systems.  The correspondence theorem makes this precise.

  Why bother?
    - One fewer data-structure layer (no cfg record, no predecessors/
      successors helpers).
    - The "structural proof" (predecessors_eq_cfg_predecessors) is a clean
      induction on c that makes the CFG construction fully explicit.
    - Opens the possibility of going AST \<rightarrow> equations directly without
      ever building a graph, which may simplify the result-mapping proof.
*)


(* ── Label Allocation Helpers ───────────────────────────────────── *)
(*
  These mirror the numbers that compile produces.

  size_com c  = number of fresh labels consumed when compiling c.
  exit_of c n = the exit program point when c is allocated starting at n.

  entry_of c n = n  always  (the entry is always the allocation base),
  so we don't define a separate function for it.
*)

fun size_com :: "com \<Rightarrow> nat" where
    "size_com SKIP              = 2"
  | "size_com (_ ::= _)         = 2"
  | "size_com (c1 ;; c2)        = size_com c1 + size_com c2"
  | "size_com (IF _ THEN c1 ELSE c2) = size_com c1 + size_com c2 + 2"
  | "size_com (WHILE _ DO c)    = size_com c + 2"

fun exit_of :: "com \<Rightarrow> nat \<Rightarrow> pp" where
    "exit_of SKIP              n = n + 1"
  | "exit_of (_ ::= _)         n = n + 1"
  | "exit_of (c1 ;; c2)        n = exit_of c2 (n + size_com c1)"
  | "exit_of (IF _ THEN c1 ELSE c2) n = n + 1 + size_com c1 + size_com c2"
  | "exit_of (WHILE _ DO c)    n = n + 1 + size_com c"

(*
  Sanity: size_com and exit_of agree with compile.
  The fresh-counter returned by compile c n equals n + size_com c,
  and the exit node returned by compile c n equals exit_of c n.
*)
lemma compile_size:
  "compile c n = (n', en, ex, E) \<Longrightarrow> n' = n + size_com c"
  sorry

lemma compile_exit:
  "compile c n = (n', en, ex, E) \<Longrightarrow> ex = exit_of c n"
  sorry

lemma compile_entry:
  "compile c n = (n', en, ex, E) \<Longrightarrow> en = n"
  by (induct c arbitrary: n n' en ex E) (auto simp: Let_def split: prod.splits)


(* ── Structural Predecessors ────────────────────────────────────── *)
(*
  predecessors_of c n v  =  the set of (u, action) pairs such that
  there is a CFG edge (u, action, v) in the equation system for command c
  when allocated starting at label n.

  This is a structural recursion: each command's predecessors are
  determined by the AST shape, with a linking Nop edge wherever two
  sub-commands are connected.
*)

fun predecessors_of :: "com \<Rightarrow> nat \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) set"
where

    (* SKIP: single edge  entry -[Nop]-> exit *)
    "predecessors_of SKIP n v =
       (if v = n + 1 then {(n, EA_Nop)} else {})"

    (* Assign: single edge  entry -[Assign x a]-> exit *)
  | "predecessors_of (x ::= a) n v =
       (if v = n + 1 then {(n, EA_Assign x a)} else {})"

    (* Seq: c1 in [n, n + size_com c1), c2 starts at n1 = n + size_com c1.
            Linking edge: exit_of c1 n -[Nop]-> n1. *)
  | "predecessors_of (c1 ;; c2) n v =
       (let n1  = n + size_com c1;
            ex1 = exit_of c1 n
        in     predecessors_of c1 n  v
             \<union> (if v = n1 then {(ex1, EA_Nop)} else {})
             \<union> predecessors_of c2 n1 v)"

    (* If: entry = n;  c1 at n+1;  c2 at n2 = n+1+size_com c1;  exit = xn.
           Branch edges:  n -[Assume b]-> en1,  n -[AssumeNot b]-> en2.
           Merge  edges:  ex1 -[Nop]-> xn,      ex2 -[Nop]-> xn. *)
  | "predecessors_of (IF b THEN c1 ELSE c2) n v =
       (let n1  = n + 1;
            n2  = n1 + size_com c1;
            en1 = n1;
            en2 = n2;
            ex1 = exit_of c1 n1;
            ex2 = exit_of c2 n2;
            xn  = n2 + size_com c2
        in     (if v = en1 then {(n, EA_Assume b)}    else {})
             \<union> (if v = en2 then {(n, EA_AssumeNot b)} else {})
             \<union> predecessors_of c1 n1 v
             \<union> predecessors_of c2 n2 v
             \<union> (if v = xn  then {(ex1, EA_Nop), (ex2, EA_Nop)} else {}))"

    (* While: head = n;  body at n+1;  exit = xn = n+1+size_com c.
              Edges: head -[Assume b]-> en_body,
                     head -[AssumeNot b]-> xn,
                     ex_body -[Nop]-> head  (back edge). *)
  | "predecessors_of (WHILE b DO c) n v =
       (let en_body = n + 1;
            ex_body = exit_of c (n + 1);
            xn      = n + 1 + size_com c
        in     (if v = en_body then {(n, EA_Assume b)}    else {})
             \<union> (if v = xn      then {(n, EA_AssumeNot b)} else {})
             \<union> predecessors_of c (n + 1) v
             \<union> (if v = n       then {(ex_body, EA_Nop)}   else {}))"


(* ── Correspondence with compile ────────────────────────────────── *)
(*
  The structural predecessor set equals the set of predecessors in the
  CFG edge set produced by compile.
  Proof: induction on c; each case unfolds compile and predecessors_of
  and checks the edge sets match.
*)

lemma predecessors_eq_compile:
  "compile c n = (n', en, ex, E) \<Longrightarrow>
   predecessors_of c n v = {(u, a) | u a. (u, a, v) \<in> E}"
  sorry


(* ── Direct RHS ─────────────────────────────────────────────────── *)
(*
  direct_rhs c n  is the RHS function for the direct approach.
  Formula is identical to rhs in Constraint_System.thy, but
  uses predecessors_of instead of cfg_edges.
*)

definition direct_rhs ::
    "com
     \<Rightarrow> nat
     \<Rightarrow> 'a domain_transfer
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> pp
     \<Rightarrow> 'a abs_state"
where
  "direct_rhs c n tf join_abs bot_abs s0 env v =
     (let preds = predecessors_of c n v;
          vals  = (\<lambda>(u, a). apply_tf tf a (env u)) ` preds;
          base  = if v = n then insert s0 vals else vals
      in  abs_join_set join_abs bot_abs base)"

(*
  Correspondence: direct_rhs = cfg rhs.
  Proof: unfold both definitions and apply predecessors_eq_compile.
*)

theorem direct_rhs_eq_cfg_rhs:
  assumes comp: "compile c n = (n', en, ex, E)"
  shows "direct_rhs c n tf join_abs bot_abs s0 env v
       = rhs (\<lparr>cfg_entry = en, cfg_exit = ex, cfg_edges = E\<rparr>)
             tf join_abs bot_abs s0 env v"
  (*
    Both definitions reduce to abs_join_set over the same set of values.
    Key steps:
      predecessors_eq_compile[OF comp] : predecessors_of c n v = {(u,a) | (u,a,v)\<in>E}
      compile_entry[OF comp]           : en = n, so cfg_entry g = n
    Then direct_rhs_def and rhs_def unfold to the same abs_join_set call.
  *)
  sorry

(*
  Monotonicity of direct_rhs inherits from rhs_mono via correspondence.
*)

lemma direct_rhs_mono:
  assumes comp: "compile c n = (n', en, ex, E)"
  assumes fin:  "finite E"
  assumes cfu:  "comp_fun_commute (join_abs :: 'a::ord abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes le:   "\<forall>v. env1 v \<le> env2 v"
  shows "direct_rhs c n tf join_abs bot_abs s0 env1 v
       \<le> direct_rhs c n tf join_abs bot_abs s0 env2 v"
  sorry


(* ── Direct Strategy Trees ──────────────────────────────────────── *)
(*
  Build the AFP strategy_tree for each program point directly from the AST,
  without going through a cfg record.

  Mirrors make_rhs_tree in TD_Interface.thy exactly:
  the only change is the source of predecessors.
*)

definition direct_tree ::
    "com
     \<Rightarrow> nat
     \<Rightarrow> 'a domain_transfer
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> pp
     \<Rightarrow> (pp, 'a abs_state) strategy_tree"
where
  "direct_tree c n tf join_abs bot_abs s0 v =
     (let preds = predecessors_of c n v;
          ps = (if finite preds then sorted_list_of_set preds else []);
          acc0  = if v = n then join_abs bot_abs s0 else bot_abs
      in  rhs_tree_fold tf join_abs acc0 ps)"

(*
  direct_tree agrees with make_rhs_tree (up to the choice of ordering for
  predecessors).  Both use the same SOME to pick an ordering; correctness
  of the fold is order-independent by comp_fun_commute.
*)

lemma direct_tree_eq_make_rhs_tree:
  assumes comp: "compile c n = (n', en, ex, E)"
  shows "direct_tree c n tf join_abs bot_abs s0 v
       = make_rhs_tree
           (\<lparr>cfg_entry = en, cfg_exit = ex, cfg_edges = E\<rparr>)
           tf join_abs bot_abs s0 v"
  sorry


(* ── Top-Level: Direct Analysis ─────────────────────────────────── *)
(*
  Run the TD solver using direct_tree as the equation-system interface.
  No CFG record is constructed; the equation system comes straight from the AST.
*)

definition direct_analyse ::
    "com
     \<Rightarrow> 'a::bot domain_transfer
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> pp \<Rightarrow> 'a abs_state"
where
  "direct_analyse c tf join_abs bot_abs s0 =
     (let T  = direct_tree c 0 tf join_abs bot_abs s0;
          \<sigma>  = TD_plain_Interp_solve T 0
      in  (\<lambda>v. lookup_bot \<sigma> v))"

(*
  direct_analyse = td_analyse: both feed the same strategy trees to the solver.
*)

theorem direct_eq_cfg_analyse:
  "direct_analyse c tf join_abs bot_abs s0 v
   = td_analyse c tf join_abs bot_abs s0 v"
  (*
    Proof sketch:
    1. Obtain (n', en, ex, E) = compile c 0.
    2. compile_entry  gives en = 0;
       to_cfg_def     gives to_cfg c = \<lparr>cfg_entry=0, cfg_exit=ex, cfg_edges=E\<rparr>.
    3. direct_tree_eq_make_rhs_tree gives
         direct_tree c 0 ... = make_rhs_tree (to_cfg c) ...
    4. Both definitions use TD_plain_Interp_solve on equal trees at point 0 = cfg_entry.
    5. lookup_bot applied to the same \<sigma> is equal.
  *)
  sorry

end
