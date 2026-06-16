theory Exec_CFG
  imports IMP2_Proc_to_CFG
begin

section \<open>Executable CFG edge enumeration\<close>

text \<open>
  List-level mirror of @{const compile} / @{const compile_prog} so edge
  enumeration and predecessor lookup code-generate without relying on
  the non-executable sorted-set encodings @{const cfg_edges_list} and
  @{const cfg_combines_list}.
\<close>

subsection \<open>Layer (a): drop the finite guard on @{const cfg_edges_list}\<close>

lemma cfg_edges_list_code [code]:
  "cfg_edges_list g = sorted_list_of_set (edges g)"
  unfolding cfg_edges_list_def
  by (cases "finite (edges g)")
     (auto simp: sorted_list_of_set.fold_insort_key.infinite)

lemma cfg_combines_list_code [code]:
  "cfg_combines_list g = sorted_list_of_set (combines g)"
  unfolding cfg_combines_list_def
  by (cases "finite (combines g)")
     (auto simp: sorted_list_of_set.fold_insort_key.infinite)

subsection \<open>List-level compilation mirror\<close>

fun compile_edges ::
  "proc_table \<Rightarrow> proc_layout \<Rightarrow> com \<Rightarrow> nat \<Rightarrow>
   nat \<times> pp \<times> pp \<times> (pp \<times> edge_action \<times> pp) list \<times> (pp \<times> pp \<times> pp) list"
where
    "compile_edges \<Pi> lay SKIP n =
       (n + 2, n, n + 1, [(n, EA_Nop, n + 1)], [])"

  | "compile_edges \<Pi> lay (Assign x a) n =
       (n + 2, n, n + 1, [(n, EA_Assign x a, n + 1)], [])"

  | "compile_edges \<Pi> lay (Seq c1 c2) n =
       (let (n1, en1, ex1, E1, C1) = compile_edges \<Pi> lay c1 n;
             (n2, en2, ex2, E2, C2) = compile_edges \<Pi> lay c2 n1
         in  (n2, en1, ex2,
              E1 @ (if ex1 = en2 then [] else [(ex1, EA_Nop, en2)]) @ E2,
              C1 @ C2))"

  | "compile_edges \<Pi> lay (If b c1 c2) n =
       (let en  = n;
             (n1, en1, ex1, E1, C1) = compile_edges \<Pi> lay c1 (n + 1);
             (n2, en2, ex2, E2, C2) = compile_edges \<Pi> lay c2 n1;
             xn  = n2
         in  (n2 + 1, en, xn,
              [(en, EA_Assume b,    en1),
               (en, EA_AssumeNot b, en2)]
              @ E1 @ E2
              @ [(ex1, EA_Nop, xn),
                 (ex2, EA_Nop, xn)],
              C1 @ C2))"

  | "compile_edges \<Pi> lay (While b c) n =
       (let head = n;
             (n1, en1, ex1, E1, C1) = compile_edges \<Pi> lay c (n + 1);
             xn  = n1
         in  (n1 + 1, head, xn,
              [(head, EA_Assume b,    en1),
               (head, EA_AssumeNot b, xn)]
              @ E1
              @ [(ex1, EA_Nop, head)],
              C1))"

  | "compile_edges \<Pi> lay (Scope c) n =
       (let (n', en, ex, E, C) = compile_edges \<Pi> lay c (n + 1);
             scope_ex = n'
         in  (n' + 1, n, scope_ex,
              E @ [(n, EA_Enter, en)],
              C @ [(n, ex, scope_ex)]))"

  | "compile_edges \<Pi> lay (Call p) n =
       (case lay p of
          None \<Rightarrow> (n + 1, n, n, [], [])
        | Some (en_p, ex_p, E_p, C_p) \<Rightarrow>
            (n + 1, n, n + 1,
             [(n, EA_Enter, en_p)],
             [(n, ex_p, n + 1)]))"

  | "compile_edges \<Pi> lay Restore n =
       (n, n, n, [], [])"

fun compile_procs_list_edges ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> proc_layout \<Rightarrow> nat \<Rightarrow>
   nat \<times> proc_layout \<times> (pp \<times> edge_action \<times> pp) list \<times> (pp \<times> pp \<times> pp) list"
where
    "compile_procs_list_edges \<Pi> [] lay n = (n, lay, [], [])"

  | "compile_procs_list_edges \<Pi> (p # ps) lay n =
       (case \<Pi> p of
          None \<Rightarrow> compile_procs_list_edges \<Pi> ps lay n
        | Some body \<Rightarrow>
            (let (n', en, ex, E, C) = compile_edges \<Pi> lay body n;
                  lay' = (case lay p of
                            None \<Rightarrow> (lay (p := Some (en, ex, set E, set C)))
                          | Some _ \<Rightarrow> lay);
                  (n'', lay'', Eacc, Cacc) = compile_procs_list_edges \<Pi> ps lay' n'
              in  (n'', lay'', E @ Eacc, C @ Cacc)))"

definition prog_cfg_edges ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp \<times> edge_action \<times> pp) list"
where
  "prog_cfg_edges \<Pi> ps main =
     (let (n1, lay, E_proc, C_proc) = compile_procs_list_edges \<Pi> ps (\<lambda>_. None) 0;
           (n2, en, ex, E_main, C_main) = compile_edges \<Pi> lay main n1
       in  E_proc @ E_main)"

definition prog_cfg_combines ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp \<times> pp \<times> pp) list"
where
  "prog_cfg_combines \<Pi> ps main =
     (let (n1, lay, E_proc, C_proc) = compile_procs_list_edges \<Pi> ps (\<lambda>_. None) 0;
           (n2, en, ex, E_main, C_main) = compile_edges \<Pi> lay main n1
       in  C_proc @ C_main)"

subsection \<open>Set correspondence with set-based compilation\<close>

text \<open>
  Each list-based mirror returns identical counter, entry, exit values as the
  set-based original; the list fields satisfy @{term "set xs = S"} for the
  corresponding set field @{term S}.  The single-direction formulation is
  essential: the counter agreement it provides lets the Seq/If IH for the
  second subcommand fire at the right offset.
\<close>

lemma compile_edges_sound:
  "compile_edges \<Pi> lay c n = (n', en, ex, Es, Cs) \<Longrightarrow>
   compile \<Pi> lay c n = (n', en, ex, set Es, set Cs)"
proof (induction \<Pi> lay c n arbitrary: n' en ex Es Cs rule: compile_edges.induct)
  case (1 \<Pi> lay n) thus ?case by auto
next
  case (2 \<Pi> lay x a n) thus ?case by auto
next
  case (3 \<Pi> lay c1 c2 n)
  obtain n1 en1 ex1 E1s C1s
    where h1: "compile_edges \<Pi> lay c1 n = (n1, en1, ex1, E1s, C1s)"
    by (cases "compile_edges \<Pi> lay c1 n") auto
  obtain n2 en2 ex2 E2s C2s
    where h2: "compile_edges \<Pi> lay c2 n1 = (n2, en2, ex2, E2s, C2s)"
    by (cases "compile_edges \<Pi> lay c2 n1") auto
  have ih1: "compile \<Pi> lay c1 n = (n1, en1, ex1, set E1s, set C1s)"
    using "3.IH"(1) h1 by blast
  have ih2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, set E2s, set C2s)"
    by (simp add: "3.IH"(2) h1 h2)
  from "3.prems" h1 h2 ih1 ih2
  show ?case by (auto simp add: Let_def)
next
  case (4 \<Pi> lay b c1 c2 n)
  obtain n1 en1 ex1 E1s C1s
    where h1: "compile_edges \<Pi> lay c1 (n + 1) = (n1, en1, ex1, E1s, C1s)"
    by (cases "compile_edges \<Pi> lay c1 (n + 1)") auto
  obtain n2 en2 ex2 E2s C2s
    where h2: "compile_edges \<Pi> lay c2 n1 = (n2, en2, ex2, E2s, C2s)"
    by (cases "compile_edges \<Pi> lay c2 n1") auto
  have ih1: "compile \<Pi> lay c1 (n + 1) = (n1, en1, ex1, set E1s, set C1s)"
    using "4.IH"(1) h1 by blast
  have ih2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, set E2s, set C2s)"
    by (metis "4.IH"(2) h1 h2)
  from "4.prems" h1 h2 ih1 ih2
  show ?case by (auto simp add: Let_def)
next
  case (5 \<Pi> lay b c n)
  obtain n1 en1 ex1 E1s C1s
    where h1: "compile_edges \<Pi> lay c (n + 1) = (n1, en1, ex1, E1s, C1s)"
    by (cases "compile_edges \<Pi> lay c (n + 1)") auto
  have ih1: "compile \<Pi> lay c (n + 1) = (n1, en1, ex1, set E1s, set C1s)"
    using "5.IH" h1 by blast
  from "5.prems" h1 ih1 show ?case by (auto simp add: Let_def)
next
  case (6 \<Pi> lay c n)
  obtain n1 en1 ex1 E1s C1s
    where h1: "compile_edges \<Pi> lay c (n + 1) = (n1, en1, ex1, E1s, C1s)"
    by (cases "compile_edges \<Pi> lay c (n + 1)") auto
  have ih1: "compile \<Pi> lay c (n + 1) = (n1, en1, ex1, set E1s, set C1s)"
    using "6.IH" h1 by blast
  from "6.prems" h1 ih1 show ?case by (auto simp add: Let_def)
next
  case (7 \<Pi> lay p n) thus ?case by (auto split: option.splits)
next
  case (8 \<Pi> lay n) thus ?case by simp
qed

lemma compile_procs_list_edges_sound:
  "compile_procs_list_edges \<Pi> ps lay n = (n', lay', Es, Cs) \<Longrightarrow>
   compile_procs_list \<Pi> ps lay n = (n', lay', set Es, set Cs)"
proof (induction ps arbitrary: lay n n' lay' Es Cs)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None
    then show ?thesis
      using Cons.prems Cons.IH by (auto split: prod.splits)
  next
    case (Some body)
    obtain n1 en1 ex1 E1s C1s
      where h1: "compile_edges \<Pi> lay body n = (n1, en1, ex1, E1s, C1s)"
      by (cases "compile_edges \<Pi> lay body n") auto
    have csound: "compile \<Pi> lay body n = (n1, en1, ex1, set E1s, set C1s)"
      using compile_edges_sound[OF h1] .
    define lay1 where
      "lay1 = (case lay p of
                 None \<Rightarrow> lay(p := Some (en1, ex1, set E1s, set C1s))
               | Some _ \<Rightarrow> lay)"
    obtain n2 lay2 Eacc Cacc
      where h2: "compile_procs_list_edges \<Pi> ps lay1 n1 = (n2, lay2, Eacc, Cacc)"
      by (cases "compile_procs_list_edges \<Pi> ps lay1 n1") auto
    have ih: "compile_procs_list \<Pi> ps lay1 n1 = (n2, lay2, set Eacc, set Cacc)"
      using Cons.IH[OF h2] .
    from Cons.prems Some h1 h2 ih csound
    show ?thesis by (auto simp add: lay1_def Let_def)
  qed
qed

lemma set_prog_cfg_edges:
  "set (prog_cfg_edges \<Pi> ps main) = edges (compile_prog \<Pi> ps main)"
proof -
  obtain n1 lay Eps Cps
    where c1: "compile_procs_list_edges \<Pi> ps (\<lambda>_. None) 0 = (n1, lay, Eps, Cps)"
    by (cases "compile_procs_list_edges \<Pi> ps (\<lambda>_. None) 0") auto
  obtain n2 en ex Ems Cms
    where c2: "compile_edges \<Pi> lay main n1 = (n2, en, ex, Ems, Cms)"
    by (cases "compile_edges \<Pi> lay main n1") auto
  have sproc: "compile_procs_list \<Pi> ps (\<lambda>_. None) 0 = (n1, lay, set Eps, set Cps)"
    using compile_procs_list_edges_sound[OF c1] .
  have smain: "compile \<Pi> lay main n1 = (n2, en, ex, set Ems, set Cms)"
    using compile_edges_sound[OF c2] .
  have lhs: "set (prog_cfg_edges \<Pi> ps main) = set Eps \<union> set Ems"
    unfolding prog_cfg_edges_def using c1 c2 by (simp add: Let_def)
  have rhs: "edges (compile_prog \<Pi> ps main) = set Eps \<union> set Ems"
    unfolding compile_prog_def compile_prog_with_regions_def
    using sproc smain by (simp add: Let_def)
  from lhs rhs show ?thesis by simp
qed

lemma set_prog_cfg_combines:
  "set (prog_cfg_combines \<Pi> ps main) = combines (compile_prog \<Pi> ps main)"
proof -
  obtain n1 lay Eps Cps
    where c1: "compile_procs_list_edges \<Pi> ps (\<lambda>_. None) 0 = (n1, lay, Eps, Cps)"
    by (cases "compile_procs_list_edges \<Pi> ps (\<lambda>_. None) 0") auto
  obtain n2 en ex Ems Cms
    where c2: "compile_edges \<Pi> lay main n1 = (n2, en, ex, Ems, Cms)"
    by (cases "compile_edges \<Pi> lay main n1") auto
  have sproc: "compile_procs_list \<Pi> ps (\<lambda>_. None) 0 = (n1, lay, set Eps, set Cps)"
    using compile_procs_list_edges_sound[OF c1] .
  have smain: "compile \<Pi> lay main n1 = (n2, en, ex, set Ems, set Cms)"
    using compile_edges_sound[OF c2] .
  have lhs: "set (prog_cfg_combines \<Pi> ps main) = set Cps \<union> set Cms"
    unfolding prog_cfg_combines_def using c1 c2 by (simp add: Let_def)
  have rhs: "combines (compile_prog \<Pi> ps main) = set Cps \<union> set Cms"
    unfolding compile_prog_def compile_prog_with_regions_def
    using sproc smain by (simp add: Let_def)
  from lhs rhs show ?thesis by simp
qed

subsection \<open>Executable predecessor lookup via compiled edge lists\<close>

text \<open>
  @{const predecessor_list} / @{const combine_predecessor_list} are defined via
  @{const cfg_edges_list} / @{const cfg_combines_list}, which use
  @{const sorted_list_of_set}.  Sorting needs @{typ edge_action} @{class linorder},
  but that instance is non-executable (defined via @{const Hilbert_Choice.Eps}).

  These list-based versions filter @{const prog_cfg_edges} /
  @{const prog_cfg_combines} directly -- no sort, no @{class linorder} on
  @{typ edge_action}.  Set-correspondence links each executable variant to the
  abstract relation used by the soundness chain.
\<close>

definition predecessor_list_prog ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list"
where
  "predecessor_list_prog \<Pi> ps main v =
     map (\<lambda>(u, a, w). (u, a)) (filter (\<lambda>(u, a, w). w = v) (prog_cfg_edges \<Pi> ps main))"

definition combine_predecessor_list_prog ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> (pp \<times> pp) list"
where
  "combine_predecessor_list_prog \<Pi> ps main v =
     map (\<lambda>(c, e, ret). (c, e))
       (filter (\<lambda>(c, e, ret). ret = v) (prog_cfg_combines \<Pi> ps main))"

lemma set_predecessor_list_prog:
  "set (predecessor_list_prog \<Pi> ps main v) = predecessors (compile_prog \<Pi> ps main) v"
  unfolding predecessor_list_prog_def predecessors_def
  by (auto simp: set_prog_cfg_edges image_iff)

lemma set_combine_predecessor_list_prog:
  "set (combine_predecessor_list_prog \<Pi> ps main v) =
   combine_predecessors (compile_prog \<Pi> ps main) v"
  unfolding combine_predecessor_list_prog_def combine_predecessors_def
  by (auto simp: set_prog_cfg_combines image_iff)

subsection \<open>S2(b) gate probe\<close>

text \<open>
  These @{command value} checks confirm that edge and predecessor enumeration
  evaluate without needing a @{class linorder} instance on @{typ edge_action}.
  Program: @{term SKIP} (two nodes, one @{const EA_Nop} edge).
\<close>

value "prog_cfg_edges (\<lambda>_. None) [] SKIP"
value "predecessor_list_prog (\<lambda>_. None) [] SKIP 0"
value "predecessor_list_prog (\<lambda>_. None) [] SKIP 1"
value "combine_predecessor_list_prog (\<lambda>_. None) [] SKIP 0"

end

