theory VIMP_Special
  imports VIMP_Expr VIMP_Globals
begin

section \<open>Special calls\<close>

text \<open>
  VIMP's analogue of Goblint's library-function dispatch, as a closed
  enumeration rather than an open table. Classification is two-level, as in
  Goblint: \<open>special_table\<close> resolves a callee name to a shape descriptor and
  \<open>classify_special\<close> applies the descriptor to the actuals, so no consumer
  re-checks arity. A special call never enters an activation.
\<close>

datatype special_desc = SD_Nondet_Int | SD_Min | SD_Max

datatype special_call =
    Nondet_Int
  | Min exp exp
  | Max exp exp

instance special_call :: countable
  by countable_datatype

fun classify_special :: "special_desc \<Rightarrow> exp list \<Rightarrow> special_call option" where
  "classify_special SD_Nondet_Int [] = Some Nondet_Int"
| "classify_special SD_Min [a, b] = Some (Min a b)"
| "classify_special SD_Max [a, b] = Some (Max a b)"
| "classify_special _ _ = None"

text \<open>Shared by \<open>pstep\<close>'s \<open>Special\<close> rule and the CFG's \<open>special_step\<close>, so the two
  concrete semantics cannot drift. \<open>Nondet_Int\<close> admits every integer.\<close>
fun special_result :: "special_call \<Rightarrow> store \<Rightarrow> int \<Rightarrow> bool" where
  "special_result Nondet_Int s v = True"
| "special_result (Min a b) s v = (v = min (aval a s) (aval b s))"
| "special_result (Max a b) s v = (v = max (aval a s) (aval b s))"

lemma special_result_ex [simp]: "\<exists>v. special_result sc s v"
  by (cases sc) auto

text \<open>Every \<open>special_pname_*\<close> is an ordinary identifier, so a source program could
  declare a colliding procedure; \<open>wf_source_program\<close> rejects that instead of
  letting special-call semantics shadow the declaration.\<close>
definition special_pname_nondet_int :: pname where
  "special_pname_nondet_int = STR ''__voblint_nondet_int''"

definition special_pname_min :: pname where
  "special_pname_min = STR ''min''"

definition special_pname_max :: pname where
  "special_pname_max = STR ''max''"

definition special_table :: "pname \<Rightarrow> special_desc option" where
  "special_table p =
     (if      p = special_pname_nondet_int then Some SD_Nondet_Int
      else if p = special_pname_min        then Some SD_Min
      else if p = special_pname_max        then Some SD_Max
      else None)"

end

