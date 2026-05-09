theory IMP2_to_CFG
  imports CFG_Def IMP2_Semantics
begin

(*
  IMP2 -- Translation to CFG.

  compile c n  returns  (n', entry, exit, edges)  where:
    n    = fresh program-point counter on entry
    n'   = fresh counter on exit (all pp's allocated are in [n, n'))
    entry, exit  are the entry and exit nodes for c's sub-graph
    edges        is the set of CFG edges for c

  Translation scheme (standard structured-program CFG):
    SKIP           : entry -[Nop]-> exit
    x ::= a        : entry -[Assign x a]-> exit
    c1 ;; c2       : c1_entry ---c1---> c1_exit -[Nop]-> c2_entry ---c2---> c2_exit
    IF b THEN c1 ELSE c2 :
                     entry -[Assume b]-> c1_entry ---c1---> c1_exit -[Nop]-> exit
                     entry -[AssumeNot b]-> c2_entry ---c2---> c2_exit -[Nop]-> exit
    WHILE b DO c   :
                     head -[Assume b]-> body_entry ---c---> body_exit -[Nop]-> head  (back)
                     head -[AssumeNot b]-> exit
*)

(* ── Compile Function ─────────────────────────────────────────── *)

fun compile :: "com => nat => nat * pp * pp * (pp * edge_action * pp) set"
where
    "compile SKIP n =
       (n + 2, n, n + 1, {(n, EA_Nop, n + 1)})"

  | "compile (x ::= a) n =
       (n + 2, n, n + 1, {(n, EA_Assign x a, n + 1)})"

  | "compile (c1 ;; c2) n =
       (let (n1, en1, ex1, E1) = compile c1 n;
            (n2, en2, ex2, E2) = compile c2 n1
        in  (n2, en1, ex2, E1 Un {(ex1, EA_Nop, en2)} Un E2))"

  | "compile (IF b THEN c1 ELSE c2) n =
       (let en  = n;
            (n1, en1, ex1, E1) = compile c1 (n + 1);
            (n2, en2, ex2, E2) = compile c2 n1;
            xn  = n2
        in  (n2 + 1, en, xn,
             {(en, EA_Assume b,    en1),
              (en, EA_AssumeNot b, en2)}
             Un E1 Un E2
             Un {(ex1, EA_Nop, xn),
                 (ex2, EA_Nop, xn)}))"

  | "compile (WHILE b DO c) n =
       (let head = n;
            (n1, en1, ex1, E1) = compile c (n + 1);
            xn  = n1
        in  (n1 + 1, head, xn,
             {(head, EA_Assume b,    en1),
              (head, EA_AssumeNot b, xn)}
             Un E1
             Un {(ex1, EA_Nop, head)}))"

(* ── Top-Level Wrapper ────────────────────────────────────────── *)

definition to_cfg :: "com => cfg" where
  "to_cfg c =
     (let (_, en, ex, E) = compile c 0
      in  (| cfg_entry = en, cfg_exit = ex, cfg_edges = E |))"

(* ── Freshness: Allocated pp's Are Disjoint From Counter ──────── *)

lemma compile_fresh:
  "compile c n = (n', en, ex, E)
   ==>  (ALL (u, _, v) : E. u < n'  &  v < n')
        &  en < n'  &  ex < n'  &  n <= n'"
  sorry

(* All allocated pp's are >= n (nothing reuses old counters). *)
lemma compile_ge:
  "compile c n = (n', en, ex, E)
   ==>  (ALL (u, _, v) : E. u >= n  &  v >= n)
        &  en >= n  &  ex >= n"
  sorry

(* ── Structural Correctness Statements ───────────────────────── *)
(*
  The key correctness property:
  If compile c n = (n', en, ex, E), then for any two states s and t,
    big_step (c, s) t
  iff
    there exists a CFG path from en to ex in E that transforms s to t.
  Proved in CFG_Collecting.thy.
*)

lemma compile_entry_ne_exit:
  "compile c n = (n', en, ex, E)  ==>  en ~= ex"
  sorry

(* Every CFG produced by compile has finitely many edges (programs are finite). *)
lemma compile_finite:
  "compile c n = (n', en, ex, E)  ==>  finite E"
  sorry

lemma to_cfg_finite: "finite (cfg_edges (to_cfg c))"
  unfolding to_cfg_def
  by (simp add: Let_def split: prod.splits) (meson compile_finite)

(*
  to_cfg always produces a well-formed CFG:
    - entry ≠ exit (compile_entry_ne_exit)
    - finite edges (to_cfg_finite)
    - all edge endpoints are valid nodes (compile_fresh)
  Stated as a lemma so downstream proofs can use cfg_wf without
  re-deriving it inline from compile properties each time.
*)
lemma to_cfg_wf: "cfg_wf (to_cfg c)"
  unfolding cfg_wf_def to_cfg_def
  sorry (* by compile_entry_ne_exit + to_cfg_finite + compile_fresh node-bound *)

end
