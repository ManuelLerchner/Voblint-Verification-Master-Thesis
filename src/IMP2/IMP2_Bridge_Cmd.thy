theory IMP2_Bridge_Cmd
  imports IMP2_Bridge_Expr
begin

section \<open>Command translation and backward simulation to AFP IMP2\<close>

text \<open>
  Compatibility layer for the parameterless subset of our procedure language.
  to_imp2_com translates that subset to AFP IMP2's com; backward_sim pulls every
  terminating AFP IMP2 run of a translated source command back into our
  frame-stack small-step semantics, read through proj0. bridge_com / bridge_pi
  pin down the translatable subset (nullary calls, procedures without formals or
  result).

  Our richer language --- procedures with parameters, return values, and the
  explicit runtime Restore --- is defined independently; only this subset
  reduces to AFP IMP2.
\<close>

subsection \<open>Command translation\<close>

text \<open>
  Assignment goes to an array write at the default index \<open>N 0\<close>; \<open>Call None p []\<close>
  maps to IMP2's PCall. Restore is runtime-only and never appears in source
  programs; it and the parameterised calls map to SKIP for totality and are
  never reached on translated source.

  Procedure-table translation wraps every body in \<open>Syntax.Scope\<close>: our Call
  saves/restores the caller's locals via the frame stack, and IMP2's PCall has
  no scope of its own, so the scoping lives in the translated body. Scope/Call
  entry matches IMP2 exactly: entry zeros the locals (\<open>enter_state s\<close>) and exit
  restores the caller's locals via the frame stack, mirroring IMP2's SCOPE.
\<close>

fun to_imp2_com :: "IMP2_Proc.com => Syntax.com" where
  "to_imp2_com IMP2_Proc.com.SKIP = Syntax.SKIP"
| "to_imp2_com (IMP2_Proc.com.Assign x a) = Syntax.AssignIdx x (Syntax.N 0) (to_imp2_aexp a)"
| "to_imp2_com (IMP2_Proc.com.Seq c1 c2) = Syntax.Seq (to_imp2_com c1) (to_imp2_com c2)"
| "to_imp2_com (IMP2_Proc.com.If b c1 c2) = Syntax.If (to_imp2_bexp b) (to_imp2_com c1) (to_imp2_com c2)"
| "to_imp2_com (IMP2_Proc.com.While b c) = Syntax.While (to_imp2_bexp b) (to_imp2_com c)"
| "to_imp2_com (IMP2_Proc.com.Scope c) = Syntax.Scope (to_imp2_com c)"
| "to_imp2_com (IMP2_Proc.com.Call None p []) = Syntax.PCall p"
| "to_imp2_com (IMP2_Proc.com.Call dst p actuals) = Syntax.SKIP"
| "to_imp2_com IMP2_Proc.com.Restore = Syntax.SKIP"

definition to_imp2_pi :: "proc_table => Syntax.program" where
  "to_imp2_pi \<Pi> = (%p. map_option (%decl. Syntax.Scope (to_imp2_com (body decl))) (\<Pi> p))"

subsection \<open>Assignment agreement at the default array index\<close>

text \<open>
  An assignment translates to an IMP2 array write at index 0. From an embedded
  state, IMP2's big-step produces the array updated at index 0; projecting back
  at index 0 recovers exactly our scalar update \<open>s(x := aval a s)\<close>.
\<close>

lemma to_imp2_Assign_bigstep:
  "Semantics.big_step P (to_imp2_com (IMP2_Proc.com.Assign x a), embed s)
        ((embed s)(x := ((embed s) x)(0 := IMP2_Expr.aval a s)))"
proof -
  have "Semantics.big_step P
          (Syntax.AssignIdx x (Syntax.N 0) (to_imp2_aexp a), embed s)
          ((embed s)(x := ((embed s) x)
             (Semantics.aval (Syntax.N 0) (embed s) := Semantics.aval (to_imp2_aexp a) (embed s))))"
    by (rule Semantics.AssignIdx)
  thus ?thesis by (simp add: aval_to_imp2)
qed

lemma proj0_Assign:
  "proj0 ((embed s)(x := ((embed s) x)(0 := IMP2_Expr.aval a s)))
     = s(x := IMP2_Expr.aval a s)"
  by (rule ext) (simp add: proj0_def embed_def)

subsection \<open>Translatable subset\<close>

text \<open>
  The AFP bridge covers only the parameterless subset: direct translation to
  parameterless PCall, procedures without formals or result, and nullary calls.
\<close>

fun bridge_com :: "IMP2_Proc.com => bool" where
  "bridge_com IMP2_Proc.com.SKIP = True"
| "bridge_com (IMP2_Proc.com.Assign x a) = True"
| "bridge_com (IMP2_Proc.com.Seq c1 c2) = (bridge_com c1 \<and> bridge_com c2)"
| "bridge_com (IMP2_Proc.com.If b c1 c2) = (bridge_com c1 \<and> bridge_com c2)"
| "bridge_com (IMP2_Proc.com.While b c) = bridge_com c"
| "bridge_com (IMP2_Proc.com.Scope c) = bridge_com c"
| "bridge_com (IMP2_Proc.com.Call None p []) = True"
| "bridge_com (IMP2_Proc.com.Call dst p actuals) = False"
| "bridge_com IMP2_Proc.com.Restore = False"

definition bridge_pi :: "proc_table => bool" where
  "bridge_pi \<Pi> =
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> formals decl = [] \<and> result decl = None \<and> bridge_com (body decl))"

lemma bridge_com_CallD:
  assumes "bridge_com (IMP2_Proc.com.Call dst p actuals)"
  shows "dst = None" and "actuals = []"
proof -
  from assms show "dst = None"
    by (cases dst; cases actuals) simp_all
  moreover from assms have "dst = None"
    by (cases dst; cases actuals) simp_all
  ultimately show "actuals = []"
    using assms by (cases actuals) simp_all
qed

lemma bridge_com_Call_parameterlessE[elim]:
  assumes "bridge_com (IMP2_Proc.com.Call dst p actuals)"
  obtains "dst = None" "actuals = []"
  using assms bridge_com_CallD by blast

subsection \<open>Backward simulation: IMP2 big-step into our small-step\<close>

text \<open>
  Every terminating AFP IMP2 run of a translated source command is reproduced by
  our frame-stack small-step semantics, read back through proj0. The proof is by
  rule induction on IMP2's big-step derivation; each rule maps to the matching
  pcompletes combinator. bridge_pi pins down that procedure bodies are in the
  translatable subset; the runtime-only IMP2 commands (ArrayCpy, CLEAR,
  Assign_Locals, PScope) are never in the range of to_imp2_com and hence vacuous.
\<close>

lemma backward_sim_aux:
  assumes sp: "bridge_pi \<Pi>"
  shows "big_step Pg (cm, S) T ==> Pg = to_imp2_pi \<Pi> ==> cm = to_imp2_com c
          ==> bridge_com c ==> pcompletes \<Pi> c (proj0 S) (proj0 T)"
proof (induction arbitrary: c rule: big_step_induct)
  case (Skip Pg s)
  hence "c = IMP2_Proc.com.SKIP" by (cases c) auto
  thus ?case by (simp add: pcompletes_skip)
next
  case (AssignIdx Pg x i a s)
  then obtain a0 where c: "c = IMP2_Proc.com.Assign x a0"
      and ae: "a = to_imp2_aexp a0" and ie: "i = Syntax.N 0"
    by (cases c) auto
  have run: "pcompletes \<Pi> (IMP2_Proc.com.Assign x a0) (proj0 s)
               ((proj0 s)(x := IMP2_Expr.aval a0 (proj0 s)))"
    by (rule pcompletes_assign)
  have res: "proj0 (s(x := (s x)(Semantics.aval i s := Semantics.aval a s)))
               = (proj0 s)(x := IMP2_Expr.aval a0 (proj0 s))"
    using ae ie by (auto simp: proj0_def aval_to_imp2_sim fun_eq_iff)
  show ?case using c run res by (simp add: fun_upd_def)
next
  case (ArrayCpy Pg x y s)
  thus ?case by (cases c) auto
next
  case (ArrayClear Pg x s)
  thus ?case by (cases c) auto
next
  case (Assign_Locals Pg l s)
  thus ?case by (cases c) auto
next
  case (Seq Pg cm1 s1 s2 cm2 s3)
  then obtain a b where c: "c = IMP2_Proc.com.Seq a b"
      and 1: "cm1 = to_imp2_com a" and 2: "cm2 = to_imp2_com b"
    by (cases c) auto
  from Seq.prems c have sa: "bridge_com a" and sb: "bridge_com b" by auto
  have r1: "pcompletes \<Pi> a (proj0 s1) (proj0 s2)"
    using Seq.IH(1)[OF Seq.prems(1) 1 sa] .
  have r2: "pcompletes \<Pi> b (proj0 s2) (proj0 s3)"
    using Seq.IH(2)[OF Seq.prems(1) 2 sb] .
  from r1 r2 have "pcompletes \<Pi> (IMP2_Proc.com.Seq a b) (proj0 s1) (proj0 s3)"
    by (rule pcompletes_Seq)
  thus ?case using c by simp
next
  case (IfTrue b s Pg cm1 t cm2)
  then obtain b0 a d where c: "c = IMP2_Proc.com.If b0 a d"
      and be: "b = to_imp2_bexp b0" and 1: "cm1 = to_imp2_com a"
      and 2: "cm2 = to_imp2_com d"
    by (cases c) auto
  from IfTrue.prems c have sa: "bridge_com a" by auto
  have guard: "IMP2_Expr.bval b0 (proj0 s)"
    using IfTrue.hyps(1) be by (auto simp: bval_to_imp2_sim)
  have bodyrun: "pcompletes \<Pi> a (proj0 s) (proj0 t)"
    using IfTrue.IH[OF IfTrue.prems(1) 1 sa] .
  from guard bodyrun have "pcompletes \<Pi> (IMP2_Proc.com.If b0 a d) (proj0 s) (proj0 t)"
    by (rule pcompletes_IfTrue)
  thus ?case using c by simp
next
  case (IfFalse b s Pg cm2 t cm1)
  then obtain b0 a d where c: "c = IMP2_Proc.com.If b0 a d"
      and be: "b = to_imp2_bexp b0" and 1: "cm1 = to_imp2_com a"
      and 2: "cm2 = to_imp2_com d"
    by (cases c) auto
  from IfFalse.prems c have sd: "bridge_com d" by auto
  have guard: "\<not> IMP2_Expr.bval b0 (proj0 s)"
    using IfFalse.hyps(1) be by (auto simp: bval_to_imp2_sim)
  have bodyrun: "pcompletes \<Pi> d (proj0 s) (proj0 t)"
    using IfFalse.IH[OF IfFalse.prems(1) 2 sd] .
  from guard bodyrun have "pcompletes \<Pi> (IMP2_Proc.com.If b0 a d) (proj0 s) (proj0 t)"
    by (rule pcompletes_IfFalse)
  thus ?case using c by simp
next
  case (Scope Pg cm0 s s')
  then obtain a where c: "c = IMP2_Proc.com.Scope a" and 0: "cm0 = to_imp2_com a"
    by (cases c) auto
  from Scope.prems c have sa: "bridge_com a" by auto
  have body: "pcompletes \<Pi> a (enter_state (proj0 s)) (proj0 s')"
    using Scope.IH[OF Scope.prems(1) 0 sa] by (simp add: proj0_null_combine)
  have "pcompletes \<Pi> (IMP2_Proc.com.Scope a) (proj0 s)
          (IMP2_Globals.combine_states (proj0 s) (proj0 s'))"
    using body by (rule pcompletes_Scope)
  hence "pcompletes \<Pi> (IMP2_Proc.com.Scope a) (proj0 s)
          (proj0 (Semantics.combine_states s s'))"
    by (simp add: proj0_combine_states)
  thus ?case using c by simp
next
  case (WhileFalse b s Pg cm0)
  then obtain b0 a where c: "c = IMP2_Proc.com.While b0 a"
      and be: "b = to_imp2_bexp b0" and 0: "cm0 = to_imp2_com a"
    by (cases c) auto
  have guard: "\<not> IMP2_Expr.bval b0 (proj0 s)"
    using WhileFalse.hyps(1) be by (auto simp: bval_to_imp2_sim)
  from guard have "pcompletes \<Pi> (IMP2_Proc.com.While b0 a) (proj0 s) (proj0 s)"
    by (rule pcompletes_WhileFalse)
  thus ?case using c by simp
next
  case (WhileTrue b s1 Pg cm0 s2 s3)
  then obtain b0 a where c: "c = IMP2_Proc.com.While b0 a"
      and be: "b = to_imp2_bexp b0" and ce: "cm0 = to_imp2_com a"
    by (cases c) auto
  from WhileTrue.prems c have sa: "bridge_com a" by auto
  have guard: "IMP2_Expr.bval b0 (proj0 s1)"
    using WhileTrue.hyps(1) be by (auto simp: bval_to_imp2_sim)
  have bodyrun: "pcompletes \<Pi> a (proj0 s1) (proj0 s2)"
    using WhileTrue.IH(1)[OF WhileTrue.prems(1) ce sa] .
  have eqw: "Syntax.While b cm0 = to_imp2_com (IMP2_Proc.com.While b0 a)"
    using be ce by simp
  have sw: "bridge_com (IMP2_Proc.com.While b0 a)" using sa by simp
  have looprun: "pcompletes \<Pi> (IMP2_Proc.com.While b0 a) (proj0 s2) (proj0 s3)"
    using WhileTrue.IH(2)[OF WhileTrue.prems(1) eqw sw] .
  from guard bodyrun looprun
  have "pcompletes \<Pi> (IMP2_Proc.com.While b0 a) (proj0 s1) (proj0 s3)"
    by (rule pcompletes_WhileTrue)
  thus ?case using c by simp
next
  case (PCall Pg p cbody s t)
  then have c: "c = IMP2_Proc.com.Call None p []" by (cases c) auto
  from PCall.hyps(1) PCall.prems(1) obtain decl where pip: "\<Pi> p = Some decl"
      and cb: "cbody = Syntax.Scope (to_imp2_com (body decl))"
    by (auto simp: to_imp2_pi_def split: option.splits)
  from sp pip have noargs: "formals decl = []" "result decl = None" "bridge_com (body decl)"
    by (auto simp: bridge_pi_def)
  have eq: "cbody = to_imp2_com (IMP2_Proc.com.Scope (body decl))" using cb by simp
  have sc0: "bridge_com (IMP2_Proc.com.Scope (body decl))" using noargs(3) by simp
  have scoperun: "pcompletes \<Pi> (IMP2_Proc.com.Scope (body decl)) (proj0 s) (proj0 t)"
    using PCall.IH[OF PCall.prems(1) eq sc0] .
  have pip_noargs: "\<Pi> p = Some (proc_decl_of [] (body decl) None)"
    using pip noargs
    by (cases decl; simp add: proc_decl_of_def)
  have "pcompletes \<Pi> (IMP2_Proc.com.Call None p []) (proj0 s) (proj0 t)"
    using pip_noargs scoperun by (rule pcompletes_Scope_Call_parameterless)
  thus ?case using c by simp
next
  case (PScope Pg pi' cm0 s t)
  thus ?case by (cases c) auto
qed

text \<open>
  Headline restatement: the analyzer's soundness is expressible against AFP
  IMP2's standard concrete semantics. Whenever the translated source program
  terminates under IMP2 big-step, our small-step semantics reaches the same
  final store (read back through proj0). Composed with trace-native pipeline
  soundness, this transfers soundness to AFP IMP2 with no further analyzer
  obligation.
\<close>

theorem backward_sim:
  assumes bs: "big_step (to_imp2_pi \<Pi>) (cm, S) T"
      and sp: "bridge_pi \<Pi>"
      and cc: "cm = to_imp2_com c"
      and sc: "bridge_com c"
  shows "pcompletes \<Pi> c (proj0 S) (proj0 T)"
  using backward_sim_aux[OF sp bs refl cc sc] .

corollary big_step_imp_pcompletes:
  assumes run: "big_step (to_imp2_pi \<Pi>) (to_imp2_com c, S) T"
      and sp: "bridge_pi \<Pi>"
      and sc: "bridge_com c"
  shows "pcompletes \<Pi> c (proj0 S) (proj0 T)"
  using backward_sim[OF run sp refl sc] .

lemma ex_big_step_imp_ex_pcompletes:
  assumes sp: "bridge_pi \<Pi>"
      and sc: "bridge_com c"
      and run: "big_step (to_imp2_pi \<Pi>) (to_imp2_com c, S) T"
  shows "\<exists>t. pcompletes \<Pi> c (proj0 S) t"
  using big_step_imp_pcompletes[OF run sp sc] by blast

text \<open>
  Concrete Semantics equates big-step termination with reaching a final
  small-step configuration. Here @{term pcompletes_iff_small_termination} is the
  small-step side (reach @{term pfinal}); @{term ex_big_step_imp_ex_pcompletes}
  is the big-to-small direction. The converse (every @{term pcompletes} run comes
  from a @{term big_step}) is forward simulation (Track A, open).
\<close>

subsection \<open>Executable examples\<close>

value "bridge_com (IMP2_Proc.com.Call None ''p'' [])"

value "to_imp2_com IMP2_Proc.com.SKIP"
value "to_imp2_com (IMP2_Proc.com.Scope IMP2_Proc.com.SKIP)"
value "to_imp2_com (IMP2_Proc.com.Seq IMP2_Proc.com.SKIP IMP2_Proc.com.SKIP)"

end
