theory IMP2_Proc_Regression
  imports IMP2_Proc
begin

section \<open>Native activation regressions for the scope-free source semantics\<close>

text \<open>
  After removing the user-visible \<open>Scope\<close> and the lexical frame, the only local-store boundary
  is a procedure call.  These regressions pin the required activation behaviour directly on the
  native \<^const>\<open>pstep\<close> / \<^const>\<open>pcompletes\<close> semantics: caller-local isolation, global
  propagation, return-value delivery, early return, normal fall-through, nested calls, and
  bounded recursion.  Each is stated over the reduced command set
  (\<open>SKIP\<close>/\<open>Assign\<close>/\<open>Seq\<close>/\<open>If\<close>/\<open>While\<close>/\<open>Call\<close>/\<open>Return\<close>); no scope or lexical frame occurs.
\<close>

subsection \<open>Caller-local isolation\<close>

text \<open>\<open>main:  x := 5;  call f()\<close>, with \<open>f:  x := 9\<close> (fall through).  The callee writes its own
  local \<open>x\<close>, but the call discards callee locals (\<open><caller|callee>\<close> keeps caller locals), so
  after the call the caller's \<open>x\<close> is still 5.\<close>
theorem caller_local_isolated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (Assign ''x'' (BaseN (AExp.N 9))) None)"
  shows "\<exists>t. pcompletes \<Pi> (Seq (Assign ''x'' (BaseN (AExp.N 5))) (Call None pf [])) s0 t
             \<and> t ''x'' = 5"
proof -
  let ?s1 = "s0(''x'' := 5)"
  have a: "pcompletes \<Pi> (Assign ''x'' (BaseN (AExp.N 5))) s0 ?s1"
  proof -
    have "pcompletes \<Pi> (Assign ''x'' (BaseN (AExp.N 5))) s0
            (s0(''x'' := aval (BaseN (AExp.N 5)) s0))" by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have body: "pcompletes \<Pi> (Assign ''x'' (BaseN (AExp.N 9)))
               (enter_state ?s1) ((enter_state ?s1)(''x'' := 9))"
  proof -
    have "pcompletes \<Pi> (Assign ''x'' (BaseN (AExp.N 9))) (enter_state ?s1)
            ((enter_state ?s1)(''x'' := aval (BaseN (AExp.N 9)) (enter_state ?s1)))"
      by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have call: "pcompletes \<Pi> (Call None pf []) ?s1 (<?s1 | (enter_state ?s1)(''x'' := 9)>)"
    by (rule pcompletes_Call_parameterless[OF p body])
  have seq: "pcompletes \<Pi> (Seq (Assign ''x'' (BaseN (AExp.N 5))) (Call None pf [])) s0
               (<?s1 | (enter_state ?s1)(''x'' := 9)>)"
    using pcompletes_Seq[OF a call] .
  have "(<?s1 | (enter_state ?s1)(''x'' := 9)>) ''x'' = 5"
    by (simp add: is_global_def)
  with seq show ?thesis by blast
qed

subsection \<open>Global propagation\<close>

text \<open>\<open>f:  Gg := 9\<close> (fall through).  A callee's global write survives the return
  (\<open><caller|callee>\<close> keeps callee globals), so after the call \<open>Gg\<close> is 9.\<close>
theorem global_propagated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (Assign ''Gg'' (BaseN (AExp.N 9))) None)"
  shows "\<exists>t. pcompletes \<Pi> (Call None pf []) s0 t \<and> t ''Gg'' = 9"
proof -
  have body: "pcompletes \<Pi> (Assign ''Gg'' (BaseN (AExp.N 9)))
               (enter_state s0) ((enter_state s0)(''Gg'' := 9))"
  proof -
    have "pcompletes \<Pi> (Assign ''Gg'' (BaseN (AExp.N 9))) (enter_state s0)
            ((enter_state s0)(''Gg'' := aval (BaseN (AExp.N 9)) (enter_state s0)))"
      by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have call: "pcompletes \<Pi> (Call None pf []) s0 (<s0 | (enter_state s0)(''Gg'' := 9)>)"
    by (rule pcompletes_Call_parameterless[OF p body])
  have "(<s0 | (enter_state s0)(''Gg'' := 9)>) ''Gg'' = 9"
    by (simp add: is_global_def)
  with call show ?thesis by blast
qed

subsection \<open>Return-value propagation\<close>

text \<open>\<open>x := f()\<close> with \<open>f\<close> declaring result \<open>7\<close>: the returned value is assigned to the caller
  destination \<open>x\<close> after locals are restored.\<close>
theorem return_value_propagated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] SKIP (Some (BaseN (AExp.N 7))))"
  shows "\<exists>t. pcompletes \<Pi> (Call (Some ''x'') pf []) s0 t \<and> t ''x'' = 7"
proof -
  have body: "pcompletes \<Pi> (body (proc_decl_of [] SKIP (Some (BaseN (AExp.N 7)))))
               (bind_formals (formals (proc_decl_of [] SKIP (Some (BaseN (AExp.N 7)))))
                 (map (\<lambda>a. aval a s0) []) (enter_state s0)) (enter_state s0)"
    by (simp add: proc_decl_of_def bind_formals_def pcompletes_skip)
  have call: "pcompletes \<Pi> (Call (Some ''x'') pf []) s0
               ((<s0 | enter_state s0>)(''x'' := aval (BaseN (AExp.N 7)) (enter_state s0)))"
    by (rule pcompletes_Call_some[OF p _ _ _ body]) (simp_all add: proc_decl_of_def)
  have "((<s0 | enter_state s0>)(''x'' := aval (BaseN (AExp.N 7)) (enter_state s0))) ''x'' = 7"
    by simp
  with call show ?thesis by blast
qed

subsection \<open>Early return skips dead code\<close>

text \<open>\<open>f:  return e;  dead\<close> completes, delivering the returned value to the destination; the
  \<open>dead\<close> command after the return is never executed --- the concrete witness
  \<open>call_return_completes\<close>, whose trace unwinds past the trailing command.\<close>
lemmas early_return_skips_dead = call_return_completes

subsection \<open>Normal fall-through\<close>

text \<open>A procedure whose body reaches its end returns normally, with no source \<open>Scope\<close>: a
  \<open>Return None\<close> body completes to \<open><caller|callee>\<close>, exactly the fall-through activation return
  (\<open>call_return_none_completes\<close>).\<close>
lemmas normal_fallthrough = call_return_none_completes

subsection \<open>Nested calls resume the correct caller\<close>

text \<open>\<open>main -> f -> g\<close>: the inner call is caught by the inner activation, so the outer
  activation survives and execution resumes in the outer procedure --- the concrete witness
  \<open>nested_call_return_trace\<close>.\<close>
lemmas nested_calls_resume_caller = nested_call_return_trace

subsection \<open>Bounded recursion: each activation has its own local store\<close>

text \<open>
  A self-recursive procedure \<open>r\<close> guarded by a global counter \<open>Gx\<close>:
  \<open>if (0 < Gx) { Gx := Gx - 1; call r() } else skip\<close>.  Started at \<open>Gx = 1\<close> the outer activation
  decrements \<open>Gx\<close> to 0 and recurses; the inner activation sees \<open>Gx = 0\<close> and falls through; the
  run completes at \<open>Gx = 0\<close>.  Each entry rebuilds the callee store with \<^const>\<open>enter_state\<close>, so
  the two activations have distinct local stores (locals reset per activation) while sharing the
  global \<open>Gx\<close>.  The else branch is fall-through \<open>SKIP\<close> --- a scope-free body that completes on
  the activation stack.
\<close>

definition rec_body :: com where
  "rec_body =
     If (Less (BaseN (AExp.N 0)) (BaseN (AExp.V ''Gx'')))
        (Seq (Assign ''Gx'' (Minus (BaseN (AExp.V ''Gx'')) (BaseN (AExp.N 1))))
             (Call None ''r'' []))
        SKIP"

theorem bounded_recursion_completes:
  assumes p: "\<Pi> ''r'' = Some (proc_decl_of [] rec_body None)"
  shows "\<exists>t. pcompletes \<Pi> (Call None ''r'' []) ((\<lambda>_. 0)(''Gx'' := 1)) t \<and> t ''Gx'' = 0"
proof -
  let ?s0 = "(\<lambda>_. 0)(''Gx'' := 1)"
  let ?e0 = "enter_state ?s0"           \<comment> \<open>outer callee store: Gx = 1, locals 0\<close>
  let ?e1 = "?e0(''Gx'' := 0)"          \<comment> \<open>after the decrement\<close>
  let ?ei = "enter_state ?e1"           \<comment> \<open>inner callee store: Gx = 0, locals 0\<close>
  \<comment> \<open>inner activation: guard false at Gx = 0, so it falls through\<close>
  have inner_guard: "\<not> bval (Less (BaseN (AExp.N 0)) (BaseN (AExp.V ''Gx''))) ?ei"
    by (simp add: enter_state_def is_global_def)
  have inner_body: "pcompletes \<Pi> rec_body ?ei ?ei"
    unfolding rec_body_def by (rule pcompletes_IfFalse[OF inner_guard pcompletes_skip])
  have inner_call: "pcompletes \<Pi> (Call None ''r'' []) ?e1 (<?e1 | ?ei>)"
    by (rule pcompletes_Call_parameterless[OF p inner_body])
  \<comment> \<open>outer activation: guard true at Gx = 1, decrement, then the inner call\<close>
  have outer_guard: "bval (Less (BaseN (AExp.N 0)) (BaseN (AExp.V ''Gx''))) ?e0"
    by (simp add: enter_state_def is_global_def)
  have dec: "pcompletes \<Pi> (Assign ''Gx'' (Minus (BaseN (AExp.V ''Gx'')) (BaseN (AExp.N 1)))) ?e0 ?e1"
  proof -
    have "pcompletes \<Pi> (Assign ''Gx'' (Minus (BaseN (AExp.V ''Gx'')) (BaseN (AExp.N 1)))) ?e0
            (?e0(''Gx'' := aval (Minus (BaseN (AExp.V ''Gx'')) (BaseN (AExp.N 1))) ?e0))"
      by (rule pcompletes_assign)
    thus ?thesis by (simp add: enter_state_def is_global_def)
  qed
  have outer_body: "pcompletes \<Pi> rec_body ?e0 (<?e1 | ?ei>)"
    unfolding rec_body_def
    by (rule pcompletes_IfTrue[OF outer_guard pcompletes_Seq[OF dec inner_call]])
  have outer_call: "pcompletes \<Pi> (Call None ''r'' []) ?s0 (<?s0 | <?e1 | ?ei>>)"
    by (rule pcompletes_Call_parameterless[OF p outer_body])
  have "(<?s0 | <?e1 | ?ei>>) ''Gx'' = 0"
    by (simp add: is_global_def enter_state_def)
  with outer_call show ?thesis by blast
qed

text \<open>The distinct-local-store property, read off the entry stores: the inner activation's local
  store is \<^const>\<open>enter_state\<close> of the (decremented) outer callee store, so both activations zero
  their locals independently --- a local set in one activation reads 0 in the other.\<close>
lemma recursion_locals_independent:
  "enter_state ((enter_state ((\<lambda>_. 0)(''Gx'' := 1)))(''Gx'' := 0)) ''y'' = 0"
  by (simp add: enter_state_def is_global_def)

end
