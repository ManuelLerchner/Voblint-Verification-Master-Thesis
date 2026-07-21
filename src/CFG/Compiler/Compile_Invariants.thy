theory Compile_Invariants
  imports

    CFG_Prune
begin


section \<open>Source-to-analysis compiler-correctness prototype\<close>

text \<open>
  This theory fixes the interfaces of the source-to-analysis proof before the
  compiler simulation is implemented. The graph and solver layers are stated
  independently of the matching-state relation used by the compiler proof.
\<close>

subsection \<open>Compiler input\<close>

definition wf_compile_input :: "proc_table \<Rightarrow> pname list \<Rightarrow> IMP2_Proc.com \<Rightarrow> bool" where
  "wf_compile_input \<Pi> ps main \<longleftrightarrow>
     distinct ps \<and>
     set ps = {p. \<Pi> p \<noteq> None} \<and>
     source_pi \<Pi> \<and>
     source_com main"

subsection \<open>Two-pass compiler invariants\<close>

definition layout_domain_exact ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> proc_layout \<Rightarrow> bool"
where
  "layout_domain_exact \<Pi> ps lay \<longleftrightarrow>
     (\<forall>p. (\<exists>info. lay p = Some info) \<longleftrightarrow>
       p \<in> set ps \<and> \<Pi> p \<noteq> None)"

definition compile_endpoints ::
  "proc_table \<Rightarrow> proc_layout \<Rightarrow> IMP2_Proc.com \<Rightarrow> nat
    \<Rightarrow> nat \<times> pp \<times> pp"
where
  "compile_endpoints \<Pi> lay cmd n =
    (case compile \<Pi> lay cmd n of
      (n', en, ex, E, C) \<Rightarrow> (n', en, ex))"

fun compile_endpoint_shape ::
  "proc_table \<Rightarrow> proc_layout \<Rightarrow> IMP2_Proc.com \<Rightarrow> nat
    \<Rightarrow> nat \<times> pp \<times> pp"
where
  "compile_endpoint_shape Pi lay IMP2_Proc.com.SKIP n = (n + 2, n, n + 1)"
| "compile_endpoint_shape Pi lay (IMP2_Proc.com.Assign x a) n = (n + 2, n, n + 1)"
| "compile_endpoint_shape Pi lay (IMP2_Proc.com.Seq c1 c2) n =
    (let (n1, en1, ex1) = compile_endpoint_shape Pi lay c1 n;
         (n2, en2, ex2) = compile_endpoint_shape Pi lay c2 n1
     in (n2, en1, ex2))"
| "compile_endpoint_shape Pi lay (IMP2_Proc.com.If b c1 c2) n =
    (let (n1, en1, ex1) = compile_endpoint_shape Pi lay c1 (n + 1);
         (n2, en2, ex2) = compile_endpoint_shape Pi lay c2 n1
     in (n2 + 1, n, n2))"
| "compile_endpoint_shape Pi lay (IMP2_Proc.com.While b cbody) n =
    (let (n1, en1, ex1) = compile_endpoint_shape Pi lay cbody (n + 1)
     in (n1 + 1, n, n1))"
| "compile_endpoint_shape Pi lay (IMP2_Proc.com.Scope cbody) n =
    (let (n1, en1, ex1) = compile_endpoint_shape Pi lay cbody (n + 1)
     in (n1 + 1, n, n1))"
| "compile_endpoint_shape Pi lay (IMP2_Proc.com.Call dst p actuals) n =
    (case (Pi p, lay p) of (Some decl, Some info) \<Rightarrow> (n + 2, n, n + 1) | _ \<Rightarrow> (n + 2, n, n))"
| "compile_endpoint_shape Pi lay IMP2_Proc.com.Restore n = (n, n, n)"

lemma compile_endpoints_eq_shape:
  "compile_endpoints \<Pi> lay cmd n = compile_endpoint_shape \<Pi> lay cmd n"
  by (induction cmd arbitrary: n;
      fastforce simp: compile_endpoints_def split: prod.splits option.splits)

lemma compile_endpoints_domain_eq:
  assumes same_domain:
    "\<And>p. (\<exists>info. lay1 p = Some info) \<longleftrightarrow>
          (\<exists>info. lay2 p = Some info)"
  shows "compile_endpoints \<Pi> lay1 cmd n =
    compile_endpoints \<Pi> lay2 cmd n"
proof -
  have shape:
      "compile_endpoint_shape \<Pi> lay1 cmd n =
       compile_endpoint_shape \<Pi> lay2 cmd n"  proof (induction cmd arbitrary: n)
    case SKIP
    then show ?case by simp
  next
    case (Assign x a)
    then show ?case by simp
  next
    case (Seq c1 c2)
    then show ?case by simp
  next
    case (If b c1 c2)
    then show ?case by simp
  next
    case (While b cbody)
    then show ?case by simp
  next
    case (Scope cbody)
    then show ?case by simp
  next
    case (Call dst p actuals)
    have domain:
        "(\<exists>info. lay1 p = Some info) =
         (\<exists>info. lay2 p = Some info)"
      by (rule same_domain)
    show ?case
      using domain
      apply (cases "lay1 p"; cases "lay2 p") apply(auto) by (metis option.simps(5))
  next
    case Restore
    then show ?case by simp
  qed
show ?thesis
    using shape compile_endpoints_eq_shape by metis
qed

lemma compile_endpoints_definedness:
  fixes cmd :: IMP2_Proc.com
  assumes same_domain:
    "\<And>p. (\<exists>info. lay1 p = Some info) \<longleftrightarrow>
          (\<exists>info. lay2 p = Some info)"
      and first:
    "compile \<Pi> lay1 cmd n = (n1, en1, ex1, E1, C1)"
      and second:
    "compile \<Pi> lay2 cmd n = (n2, en2, ex2, E2, C2)"
  shows "n1 = n2 \<and> en1 = en2 \<and> ex1 = ex2"
proof -
  have eq: "compile_endpoints \<Pi> lay1 cmd n =
      compile_endpoints \<Pi> lay2 cmd n"
    by (rule compile_endpoints_domain_eq[OF same_domain])
  show ?thesis
    using eq first second unfolding compile_endpoints_def by simp
qed

fun endpoint_view :: "proc_info option \<Rightarrow> (pp \<times> pp) option"
where
  "endpoint_view None = None"
| "endpoint_view (Some (en, ex, Ns, E, C)) = Some (en, ex)"

definition layouts_agree :: "proc_layout \<Rightarrow> proc_layout \<Rightarrow> bool"
where
  "layouts_agree lay1 lay2 \<longleftrightarrow>
    (\<forall>p. endpoint_view (lay1 p) = endpoint_view (lay2 p))"

lemma compile_layouts_agree:
  assumes agree: "layouts_agree lay1 lay2"
  shows "compile Pi lay1 cmd n = compile Pi lay2 cmd n"
  using agree
proof (induction cmd arbitrary: n)
  case SKIP
  show ?case by simp
next
  case Assign
  show ?case by simp
next
  case (Seq c1 c2)
  show ?case
    by (simp add: Seq.IH(1)[OF Seq.prems] Seq.IH(2)[OF Seq.prems])
next
  case If
  show ?case
    by (simp add: If.IH(1)[OF If.prems] If.IH(2)[OF If.prems])
next
  case While
  show ?case
    by (simp add: While.IH[OF While.prems])
next
  case Scope
  show ?case
    by (simp add: Scope.IH[OF Scope.prems])
next
  case (Call dst p actuals)
  have view: "endpoint_view (lay1 p) = endpoint_view (lay2 p)"
    using Call.prems unfolding layouts_agree_def by blast
  show ?case
  proof (cases "Pi p")
    case None
    then show ?thesis by simp
  next
    case (Some decl)
    show ?thesis
    proof (cases "lay1 p")
      case None
      with view show ?thesis by (cases "lay2 p") auto
    next
      case (Some info1)
      then obtain en1 ex1 Ns1 E1 C1 where info1[simp]: "info1 = (en1, ex1, Ns1, E1, C1)"
        by (cases info1)
      from view Some obtain en2 ex2 Ns2 E2 C2 where info2[simp]: "lay2 p = Some (en2, ex2, Ns2, E2, C2)"
        and ends: "en1 = en2" "ex1 = ex2"
        by (cases "lay2 p") auto
      then show ?thesis using Some ends
        by (simp split: option.splits prod.splits)
    qed
  qed
next
  case Restore
  show ?case by simp
qed

lemma compile_procs_layout_domain:
  assumes distinct: "distinct ps"
      and fresh: "\<forall>p \<in> set ps. lay p = None"
      and defined: "\<forall>p \<in> set ps. \<Pi> p \<noteq> None"
      and result: "compile_procs_layout \<Pi> ps lay n = (n', lay')"
  shows "(\<exists>info. lay' q = Some info) \<longleftrightarrow>
    (\<exists>info. lay q = Some info) \<or> q \<in> set ps"
using distinct fresh defined result
proof (induction ps arbitrary: lay n n' lay')
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  obtain decl where decl: "\<Pi> a = Some decl"
    using Cons.prems(3) by auto
  obtain n1 en ex E C where comp:
      "compile \<Pi> (known_proc_layout \<Pi> (a # ps) lay) (with_result (body decl) (result decl)) n =
        (n1, en, ex, E, C)"
    by (cases "compile \<Pi> (known_proc_layout \<Pi> (a # ps) lay) (with_result (body decl) (result decl)) n") auto
  have rec:
      "compile_procs_layout \<Pi> ps
        (lay(a := Some (en, ex, {n..<n1}, {}, {}))) n1 =
        (n', lay')"
    using Cons.prems(4) decl comp Cons.prems(2) by simp
  have fresh_tail:
      "\<forall>p \<in> set ps.
        (lay(a := Some (en, ex, {n..<n1}, {}, {}))) p = None"
    using Cons.prems(1,2) by auto
  have defined_tail: "\<forall>p \<in> set ps. \<Pi> p \<noteq> None"
    using Cons.prems(3) by auto
  have tail:
      "(\<exists>info. lay' q = Some info) \<longleftrightarrow>
       (\<exists>info. (lay(a := Some (en, ex, {n..<n1}, {}, {}))) q =
          Some info) \<or> q \<in> set ps"
    by (rule Cons.IH[OF _ fresh_tail defined_tail rec])
       (use Cons.prems(1) in auto)
  show ?case
    using tail Cons.prems(2) by auto
qed

lemma compile_procs_layout_domain_exact:
  assumes wf: "wf_compile_input \<Pi> ps main"
      and layout:
        "compile_procs_layout \<Pi> ps (\<lambda>_. None) 0 = (n, lay)"
  shows "layout_domain_exact \<Pi> ps lay"
  using wf layout
    compile_procs_layout_domain[of ps "\<lambda>_. None" \<Pi> 0 n lay]
  by (auto simp: wf_compile_input_def layout_domain_exact_def)

lemma compile_procs_layout_preserves:
  assumes result: "compile_procs_layout Pi ps lay n = (n', lay')"
      and present: "lay p = Some info"
  shows "lay' p = Some info"
  using result present
proof (induction ps arbitrary: lay n n' lay')
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "Pi a")
    case None
    have rec: "compile_procs_layout Pi ps lay n = (n', lay')"
      using Cons.prems(1) None by simp
    show ?thesis
      by (rule Cons.IH[OF rec Cons.prems(2)])
  next
    case (Some decl)
    note proc = Some
    obtain k en ex E C where comp:
        "compile Pi (known_proc_layout Pi (a # ps) lay) (with_result (body decl) (result decl)) n =
          (k, en, ex, E, C)"
      by (cases "compile Pi (known_proc_layout Pi (a # ps) lay) (with_result (body decl) (result decl)) n")
         auto
    show ?thesis
    proof (cases "lay a")
      case None
      note absent = None
      have rec:
          "compile_procs_layout Pi ps
            (lay(a := Some (en, ex, {n..<k}, {}, {}))) k =
            (n', lay')"
        using Cons.prems(1) proc comp absent by simp
      have neq: "p \<noteq> a"
        using Cons.prems(2) absent by auto
      have updated:
          "(lay(a := Some (en, ex, {n..<k}, {}, {}))) p = Some info"
        using Cons.prems(2) neq by simp
      show ?thesis
        by (rule Cons.IH[OF rec updated])
    next
      case (Some current)
      note present_a = Some
      have rec: "compile_procs_layout Pi ps lay k = (n', lay')"
        using Cons.prems(1) proc comp present_a by simp
      show ?thesis
        by (rule Cons.IH[OF rec Cons.prems(2)])
    qed
  qed
qed

lemma compile_procs_layout_member:
  assumes distinct: "distinct ps"
      and fresh: "\<forall>q \<in> set ps. in_lay q = None"
      and defined: "\<forall>q \<in> set ps. Pi q \<noteq> None"
      and result:
        "compile_procs_layout Pi ps in_lay n = (n', out_lay)"
      and member: "p \<in> set ps"
  shows "\<exists>en ex Ns.
    out_lay p = Some (en, ex, Ns, {}, {})"
  using distinct fresh defined result member
proof (induction ps arbitrary: in_lay n n' out_lay p)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  obtain head_decl where head: "Pi a = Some head_decl"
    using Cons.prems(3) by auto
  obtain k head_en head_ex head_E head_C where comp:
      "compile Pi (known_proc_layout Pi (a # ps) in_lay)
        (with_result (body head_decl) (result head_decl)) n =
        (k, head_en, head_ex, head_E, head_C)"
    by (cases "compile Pi
      (known_proc_layout Pi (a # ps) in_lay) (with_result (body head_decl) (result head_decl)) n") auto
  define next_lay where
    "next_lay =
      in_lay(a := Some (head_en, head_ex, {n..<k}, {}, {}))"
  have rec:
      "compile_procs_layout Pi ps next_lay k = (n', out_lay)"
    using Cons.prems(4) head comp Cons.prems(2)
    by (simp add: next_lay_def)
  show ?case
  proof (cases "p = a")
    case True
    have stored:
        "out_lay a =
          Some (head_en, head_ex, {n..<k}, {}, {})"
      by (rule compile_procs_layout_preserves[OF rec])
         (simp add: next_lay_def)
    then show ?thesis
      using True by blast
  next
    case False
    have fresh_tail: "\<forall>q \<in> set ps. next_lay q = None"
      using Cons.prems(1,2)
      by (auto simp: next_lay_def)
    show ?thesis
      by (rule Cons.IH[OF _ fresh_tail _ rec])
         (use Cons.prems False in auto)
  qed
qed

lemma compile_procs_bodies_preserves:
  assumes result:
    "compile_procs_bodies \<Pi> ps base_lay lay n = (n', lay', E, C)"
      and present: "lay p = Some info"
  shows "lay' p = Some info"
  using result present
proof (induction ps arbitrary: lay n n' lay' E C)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "\<Pi> a")
    case None
    have rec:
        "compile_procs_bodies \<Pi> ps base_lay lay n = (n', lay', E, C)"
      using Cons.prems(1) None by simp
    show ?thesis
      by (rule Cons.IH[OF rec Cons.prems(2)])
  next
    case (Some decl)
    note proc = Some
    obtain k en ex Ea Ca where comp:
        "compile \<Pi> base_lay (with_result (body decl) (result decl)) n = (k, en, ex, Ea, Ca)"
      by (cases "compile \<Pi> base_lay (with_result (body decl) (result decl)) n") auto
    show ?thesis
    proof (cases "lay a")
      case None
      note absent = None
      obtain Erest Crest where rec:
          "compile_procs_bodies \<Pi> ps base_lay
            (lay(a := Some (en, ex, {n..<k}, Ea, Ca))) k =
            (n', lay', Erest, Crest)"
        using Cons.prems(1) proc comp absent
        by (auto split: prod.splits)
      have neq: "p \<noteq> a"
        using Cons.prems(2) absent by auto
      have updated:
          "(lay(a := Some (en, ex, {n..<k}, Ea, Ca))) p = Some info"
        using Cons.prems(2) neq by simp
      show ?thesis
        by (rule Cons.IH[OF rec updated])
    next
      case (Some current)
      note present_a = Some
      obtain Erest Crest where rec:
          "compile_procs_bodies \<Pi> ps base_lay lay k =
            (n', lay', Erest, Crest)"
        using Cons.prems(1) proc comp present_a
        by (auto split: prod.splits)
      show ?thesis
        by (rule Cons.IH[OF rec Cons.prems(2)])
    qed
  qed
qed

lemma compile_procs_bodies_lookup:
  assumes distinct: "distinct ps"
      and fresh: "\<forall>q \<in> set ps. in_lay q = None"
      and bodies:
        "compile_procs_bodies Pi ps base_lay in_lay n =
          (n', out_lay, E, C)"
      and member: "p \<in> set ps"
      and proc: "Pi p = Some decl"
      and lookup:
        "out_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "\<exists>start finish.
    compile Pi base_lay (with_result (body decl) (result decl)) start = (finish, en, ex, Ep, Cp)"
  using distinct fresh bodies member proc lookup
proof (induction ps arbitrary: in_lay n n' out_lay E C p decl
    en ex Ns Ep Cp)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "Pi a")
    case None
    have neq: "p \<noteq> a"
      using Cons.prems(5) None by auto
    have rec:
        "compile_procs_bodies Pi ps base_lay in_lay n =
          (n', out_lay, E, C)"
      using Cons.prems(3) None by simp
    show ?thesis
      by (rule Cons.IH[OF _ _ rec])
         (use Cons.prems neq in auto)
  next
    case (Some head_decl)
    note head = Some
    obtain k head_en head_ex head_E head_C where comp:
        "compile Pi base_lay (with_result (body head_decl) (result head_decl)) n =
          (k, head_en, head_ex, head_E, head_C)"
      by (cases "compile Pi base_lay (with_result (body head_decl) (result head_decl)) n") auto
    define next_lay where
      "next_lay =
        in_lay(a := Some
          (head_en, head_ex, {n..<k}, head_E, head_C))"
    have absent: "in_lay a = None"
      using Cons.prems(2) by simp
    obtain Erest Crest where rec:
        "compile_procs_bodies Pi ps base_lay next_lay k =
          (n', out_lay, Erest, Crest)"
      using Cons.prems(3) head comp absent
      by (auto simp: next_lay_def split: prod.splits)
    show ?thesis
    proof (cases "p = a")
      case True
      have stored:
          "out_lay a = Some
            (head_en, head_ex, {n..<k}, head_E, head_C)"
        by (rule compile_procs_bodies_preserves[OF rec])
           (simp add: next_lay_def)
      have decl_eq: "decl = head_decl"
        using Cons.prems(5) head True by simp
      show ?thesis
        using comp Cons.prems(6) stored True decl_eq by auto
    next
      case False
      have fresh_tail: "\<forall>q \<in> set ps. next_lay q = None"
        using Cons.prems(1,2)
        by (auto simp: next_lay_def)
      show ?thesis
        by (rule Cons.IH[OF _ fresh_tail rec])
           (use Cons.prems False in auto)
    qed
  qed
qed

lemma compile_procs_bodies_outside:
  assumes result:
    "compile_procs_bodies Pi ps base_lay in_lay n =
      (n', out_lay, E, C)"
      and outside: "p \<notin> set ps"
      and absent: "in_lay p = None"
  shows "out_lay p = None"
  using result outside absent
  by (induction ps arbitrary: in_lay n n' out_lay E C)
     (auto split: option.splits prod.splits)

lemma compile_procs_pass_endpoint_agreement_general:
  assumes distinct: "distinct ps"
      and fresh_layout: "\<forall>q \<in> set ps. in_lay q = None"
      and fresh_bodies: "\<forall>q \<in> set ps. in_full q = None"
      and defined: "\<forall>q \<in> set ps. \<Pi> q \<noteq> None"
      and layout:
        "compile_procs_layout \<Pi> ps in_lay start = (n, base_lay)"
      and bodies:
        "compile_procs_bodies \<Pi> ps base_lay in_full start =
          (n', full_lay, E, C)"
      and member: "p \<in> set ps"
      and base:
        "base_lay p = Some (en, ex, Ns, {}, {})"
  shows "\<exists>Ns' Ep Cp.
    full_lay p = Some (en, ex, Ns', Ep, Cp)"
  using distinct fresh_layout fresh_bodies defined layout bodies member base
proof (induction ps arbitrary: in_lay in_full start n base_lay
    n' full_lay E C p en ex Ns)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  obtain decl where decl: "\<Pi> a = Some decl"
    using Cons.prems(4) by auto
  obtain k en1 ex1 E1 C1 where first:
      "compile \<Pi> (known_proc_layout \<Pi> (a # ps) in_lay) (with_result (body decl) (result decl)) start =
        (k, en1, ex1, E1, C1)"
    by (cases "compile \<Pi> (known_proc_layout \<Pi> (a # ps) in_lay) (with_result (body decl) (result decl)) start")
       auto
  define next_lay where
    "next_lay = in_lay(a := Some (en1, ex1, {start..<k}, {}, {}))"
  have layout_tail:
      "compile_procs_layout \<Pi> ps next_lay k = (n, base_lay)"
    using Cons.prems(5) decl first Cons.prems(2)
    by (simp add: next_lay_def)

  obtain k' en2 ex2 E2 C2 where second:
      "compile \<Pi> base_lay (with_result (body decl) (result decl)) start = (k', en2, ex2, E2, C2)"
    by (cases "compile \<Pi> base_lay (with_result (body decl) (result decl)) start") auto
  define next_full where
    "next_full =
      in_full(a := Some (en2, ex2, {start..<k'}, E2, C2))"
  obtain Erest Crest where bodies_tail:
      "compile_procs_bodies \<Pi> ps base_lay next_full k' =
        (n', full_lay, Erest, Crest)"
    using Cons.prems(6) decl second Cons.prems(3)
    by (auto simp: next_full_def split: prod.splits)

  have base_domain:
      "(\<exists>info. base_lay q = Some info) \<longleftrightarrow>
       (\<exists>info. in_lay q = Some info) \<or> q \<in> set (a # ps)"
    for q
    by (rule compile_procs_layout_domain[OF Cons.prems(1)
          Cons.prems(2) Cons.prems(4) Cons.prems(5)])
  have same_domain:
      "\<And>q. (\<exists>info. known_proc_layout \<Pi> (a # ps) in_lay q = Some info) \<longleftrightarrow>
            (\<exists>info. base_lay q = Some info)"
    using base_domain Cons.prems(4)
    by (auto simp: known_proc_layout_def split: option.splits)
  have endpoints: "k = k' \<and> en1 = en2 \<and> ex1 = ex2"
    by (rule compile_endpoints_definedness[OF same_domain first second])

  show ?case
  proof (cases "p = a")
    case True
    have base_head:
        "base_lay a = Some (en1, ex1, {start..<k}, {}, {})"
      by (rule compile_procs_layout_preserves[OF layout_tail])
         (simp add: next_lay_def)
    have endpoint_values: "en = en1 \<and> ex = ex1"
      using Cons.prems(8) base_head True by simp
    have full_head:
        "full_lay a = Some (en2, ex2, {start..<k'}, E2, C2)"
      by (rule compile_procs_bodies_preserves[OF bodies_tail])
         (simp add: next_full_def)
    show ?thesis
      using endpoints endpoint_values full_head True by auto
  next
    case False
    have fresh_layout_tail: "\<forall>q \<in> set ps. next_lay q = None"
      using Cons.prems(1,2) by (auto simp: next_lay_def)
    have fresh_bodies_tail: "\<forall>q \<in> set ps. next_full q = None"
      using Cons.prems(1,3) by (auto simp: next_full_def)
    have bodies_tail_aligned:
        "compile_procs_bodies \<Pi> ps base_lay next_full k =
          (n', full_lay, Erest, Crest)"
      using bodies_tail endpoints by simp
    show ?thesis
      by (rule Cons.IH[OF _ fresh_layout_tail fresh_bodies_tail _
            layout_tail bodies_tail_aligned])
         (use Cons.prems False in auto)
  qed
qed

lemma compile_procs_pass_endpoint_agreement:
  assumes wf: "wf_compile_input \<Pi> ps main"
      and layout:
        "compile_procs_layout \<Pi> ps (\<lambda>_. None) 0 = (n, base_lay)"
      and bodies:
        "compile_procs_bodies \<Pi> ps base_lay (\<lambda>_. None) 0 =
          (n', full_lay, E, C)"
      and member: "p \<in> set ps"
      and body: "\<Pi> p = Some cmd"
      and base:
        "base_lay p = Some (en, ex, Ns, {}, {})"
  shows "\<exists>Ns' Ep Cp.
    full_lay p = Some (en, ex, Ns', Ep, Cp)"
  proof (rule compile_procs_pass_endpoint_agreement_general[
      OF _ _ _ _ layout bodies member base])
    show "distinct ps"
      using wf by (auto simp: wf_compile_input_def)
    show "\<forall>q\<in>set ps. (\<lambda>_. None) q = None" by simp
    show "\<forall>q\<in>set ps. (\<lambda>_. None) q = None" by simp
    show "\<forall>q\<in>set ps. \<Pi> q \<noteq> None"
      using wf by (auto simp: wf_compile_input_def)
  qed

lemma compile_procs_pass_layouts_agree:
  assumes wf: "wf_compile_input Pi ps main"
      and layout:
        "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
          (n, base_lay)"
      and bodies:
        "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
          (n', full_lay, E, C)"
  shows "layouts_agree base_lay full_lay"
proof (unfold layouts_agree_def, intro allI)
  fix p
  show "endpoint_view (base_lay p) = endpoint_view (full_lay p)"
  proof (cases "p \<in> set ps")
    case True
    obtain cmd where body: "Pi p = Some cmd"
      using wf True
      by (auto simp: wf_compile_input_def)
    have distinct: "distinct ps"
      using wf by (auto simp: wf_compile_input_def)
    have defined: "\<forall>q\<in>set ps. Pi q \<noteq> None"
      using wf by (auto simp: wf_compile_input_def)
    have member_info:
        "\<exists>en ex Ns. base_lay p = Some (en, ex, Ns, {}, {})"
      by (rule compile_procs_layout_member[
            OF distinct _ defined layout True])
         simp
    then obtain en ex Ns where base:
        "base_lay p = Some (en, ex, Ns, {}, {})"
      by blast
    obtain Ns' Ep Cp where full:
        "full_lay p = Some (en, ex, Ns', Ep, Cp)"
      using compile_procs_pass_endpoint_agreement[
        OF wf layout bodies True body base] by blast
    show ?thesis
      using base full by simp
  next
    case False
    have base_none: "base_lay p = None"
      using compile_procs_layout_domain_exact[OF wf layout] False
      unfolding layout_domain_exact_def
      by (cases "base_lay p") auto
    have full_none: "full_lay p = None"
      by (rule compile_procs_bodies_outside[OF bodies False]) simp
    show ?thesis
      using base_none full_none by simp
  qed
qed


lemma compile_procs_list_decompose:
  assumes result:
    "compile_procs_list Pi ps (\<lambda>_. None) 0 =
      (nout, full_lay, E, C)"
  shows "\<exists>nbase base_lay.
    compile_procs_layout Pi ps (\<lambda>_. None) 0 =
      (nbase, base_lay) \<and>
    compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
      (nout, full_lay, E, C)"
proof -
  obtain nbase base_lay where layout:
      "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
        (nbase, base_lay)"
    by (cases "compile_procs_layout Pi ps (\<lambda>_. None) 0") auto
  obtain nbody body_lay Ebody Cbody where bodies:
      "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
        (nbody, body_lay, Ebody, Cbody)"
    by (cases "compile_procs_bodies Pi ps base_lay
      (\<lambda>_. None) 0") auto
  show ?thesis
    using result layout bodies
    unfolding compile_procs_list_def
    by simp
qed


lemma compile_procs_bodies_fragment:
  assumes bodies:
    "compile_procs_bodies \<Pi> ps base_lay in_lay n =
      (n', out_lay, E, C)"
      and fragment:
    "out_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "in_lay p = Some (en, ex, Ns, Ep, Cp) \<or>
    (Ep \<subseteq> E \<and> Cp \<subseteq> C)"
using assms proof (induction ps arbitrary: in_lay n n' out_lay E C)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "\<Pi> a")
    case None
    have rec:
        "compile_procs_bodies \<Pi> ps base_lay in_lay n =
          (n', out_lay, E, C)"
      using Cons.prems(1) None by simp
    show ?thesis
      by (rule Cons.IH[OF rec Cons.prems(2)])
  next
    case (Some decl)
    note proc = Some
    obtain n1 en1 ex1 E1 C1 where comp:
        "compile \<Pi> base_lay (with_result (body decl) (result decl)) n = (n1, en1, ex1, E1, C1)"
      by (cases "compile \<Pi> base_lay (with_result (body decl) (result decl)) n") auto
    show ?thesis
    proof (cases "in_lay a")
      case None
      obtain n2 lay2 E2 C2 where rec:
          "compile_procs_bodies \<Pi> ps base_lay
            (in_lay(a := Some (en1, ex1, {n..<n1}, E1, C1))) n1 =
            (n2, lay2, E2, C2)"
        by (cases "compile_procs_bodies \<Pi> ps base_lay
          (in_lay(a := Some (en1, ex1, {n..<n1}, E1, C1))) n1") auto
      have final:
          "n' = n2 \<and> out_lay = lay2 \<and> E = E1 \<union> E2 \<and> C = C1 \<union> C2"
        using Cons.prems(1) proc comp None rec by simp
      have tail:
          "(in_lay(a := Some (en1, ex1, {n..<n1}, E1, C1))) p =
             Some (en, ex, Ns, Ep, Cp) \<or>
           Ep \<subseteq> E2 \<and> Cp \<subseteq> C2"
        by (rule Cons.IH[OF rec])
           (use Cons.prems(2) final in auto)
      show ?thesis
        using tail final None by (cases "p = a") auto
    next
      case (Some old)
      note present = Some
      obtain n2 lay2 E2 C2 where rec:
          "compile_procs_bodies \<Pi> ps base_lay in_lay n1 =
            (n2, lay2, E2, C2)"
        by (cases "compile_procs_bodies \<Pi> ps base_lay in_lay n1") auto
      have final:
          "n' = n2 \<and> out_lay = lay2 \<and> E = E1 \<union> E2 \<and> C = C1 \<union> C2"
        using Cons.prems(1) proc comp present rec by simp
      have tail:
          "in_lay p = Some (en, ex, Ns, Ep, Cp) \<or>
           Ep \<subseteq> E2 \<and> Cp \<subseteq> C2"
        by (rule Cons.IH[OF rec])
           (use Cons.prems(2) final in auto)
      show ?thesis
        using tail final by auto
    qed
  qed
qed

lemma compile_procs_body_fragment_embedding:
  assumes wf: "wf_compile_input \<Pi> ps main"
      and layout:
        "compile_procs_layout \<Pi> ps (\<lambda>_. None) 0 = (n, base_lay)"
      and bodies:
        "compile_procs_bodies \<Pi> ps base_lay (\<lambda>_. None) 0 =
          (n', full_lay, E, C)"
      and fragment:
        "full_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "Ep \<subseteq> E \<and> Cp \<subseteq> C"
  using compile_procs_bodies_fragment[OF bodies fragment] by auto

lemma compile_call_defined:
  assumes proc: "\<Pi> p = Some decl"
      and layout: "lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "compile \<Pi> lay (Call dst p actuals) n =
    (n + 2, n, n + 1,
      {(n, EA_Enter (formals decl) actuals, en)},
      {(n, ex, n + 1, dst)})"
using proc layout by simp

end
