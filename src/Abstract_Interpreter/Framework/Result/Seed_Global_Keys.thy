theory Seed_Global_Keys
  imports DG_Constraint_Trees CFG_Enumeration Routed_Call_Trees
    "Voblint_VIMP.VIMP_Program"
    "Voblint_Domain.Reachability_Lift"
begin

section \<open>Naming the global unknowns a routed solve produces\<close>

text \<open>
  A routed solve stores one analysis-wide global plus, for every procedure and
  every context it is entered at, one seed unknown holding the state on entry.
  This theory enumerates those keys and gives each a display label. It is
  generic in the key, context and carrier types: nothing here inspects a state,
  so it sits below any choice of state representation.
\<close>

text \<open>
  Which keys a routed unit-context solve can write, taking the two constructors as
  arguments the way \<^const>\<open>routed_entry_seed_tree\<close> already does. Every domain declares its own
  \<open>gk\<close>, but they agree on the shape the routed spine imposes --- a shared slot and one
  seed per callee entry --- so the enumeration is a fact about that spine, not about
  any domain, and does not need restating once per \<open>gk\<close>.

  \<^const>\<open>prog_main_name\<close> is included: \<open>main\<close> compiles through the same procedure
  wrapper as any other, and a procedure nothing calls simply reads
  \<^const>\<open>Bot\<close> rather than being absent.
\<close>

definition seed_global_keys ::
    "'k \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> (pp \<Rightarrow> 'c list) \<Rightarrow> (pname \<Rightarrow> 'c \<Rightarrow> String.literal)
     \<Rightarrow> imp_prog \<Rightarrow> ('k \<times> String.literal \<times> (('d, 'd) dg_state \<Rightarrow> 'd)) list" where
  "seed_global_keys gk0 seed ctxs label p =
     (gk0, STR ''Global'', globs)
       # concat
           (map (\<lambda>f. map (\<lambda>c. (seed (FunctionEntry f) c, label f c, locals))
                         (ctxs (FunctionEntry f)))
                (prog_main_name # prog_procs p))"

text \<open>
  At the unit context every entry has exactly one seed, so the context list is a
  constant and the label is the procedure name alone. A context-sensitive caller
  passes the contexts its solved table covers instead, which needs no order on the
  context type.
\<close>

definition unit_seed_global_keys ::
    "'k \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'k) \<Rightarrow> imp_prog
     \<Rightarrow> ('k \<times> String.literal \<times> (('d, 'd) dg_state \<Rightarrow> 'd)) list" where
  "unit_seed_global_keys gk0 seed =
     seed_global_keys gk0 seed (\<lambda>_. [()]) (\<lambda>f _. STR ''enter '' + f)"
end
