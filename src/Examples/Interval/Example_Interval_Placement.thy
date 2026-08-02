theory Example_Interval_Placement
  imports "Voblint_Analysis.Ivl_Exec"
begin

hide_const phase.N

section \<open>Interval placement slice with independent global policies\<close>

text \<open>
  The program has two declared globals with independent placement.  The procedure
  call binds a formal, introduces the implicit local \<open>tmp\<close>, and returns into the
  caller-local \<open>answer\<close>.  Neither global name relies on the historical \<open>G\<close>
  prefix convention.
\<close>

definition placement_prog :: imp_prog where
  "placement_prog = program {
     global balance, request_count;
     void add(x) {
       tmp := balance + x;
       balance := tmp;
       request_count := request_count + 1;
       return balance
     }
     void main() { answer := add(3) }
   }"

definition placement_owner :: pname where
  "placement_owner = ''add''"

fun placement_keep_local :: "scoped_location => bool" where
  "placement_keep_local (owner, Local_Location x) = True"
| "placement_keep_local (owner, Global_Location x) = (x = ''balance'')"

fun placement_publish_side :: "scoped_location => bool" where
  "placement_publish_side (owner, Local_Location x) = False"
| "placement_publish_side (owner, Global_Location x) = (x = ''request_count'')"

lemma placement_keep_local_global_invariant:
  "placement_global_invariant placement_keep_local"
  unfolding placement_global_invariant_def by simp

lemma placement_publish_side_global_invariant:
  "placement_global_invariant placement_publish_side"
  unfolding placement_global_invariant_def by simp

definition placement_state :: "ivl resolved_st_q" where
  "placement_state =
    update_resolved_st_q
      (update_resolved_st_q cinit_ivl_st (Global_Location ''balance'')
        (Ivl (Fin 10) (Fin 10)))
      (Global_Location ''request_count'') (Ivl (Fin 4) (Fin 4))"

definition placement_local_state :: "ivl resolved_st_q" where
  "placement_local_state =
    project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      placement_keep_local placement_state"

definition placement_side_state :: "ivl resolved_st_q" where
  "placement_side_state =
    project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      placement_publish_side placement_state"

subsection \<open>Source storage and finite call scope\<close>

lemma placement_storage:
  "storage_of placement_prog ''add'' ''balance'' = GlobalVar"
  "storage_of placement_prog ''add'' ''request_count'' = GlobalVar"
  "storage_of placement_prog ''add'' ''x'' = LocalVar ''add''"
  "storage_of placement_prog ''add'' ''tmp'' = LocalVar ''add''"
  "storage_of placement_prog prog_main_name ''answer'' = LocalVar prog_main_name"
  by eval+

lemma placement_add_scope:
  "Global_Location ''balance'' \<in> set (scope_locations placement_prog placement_owner)"
  "Global_Location ''request_count'' \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location ''x'' \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location ''tmp'' \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location ret_var \<in> set (scope_locations placement_prog placement_owner)"
  by eval+

lemma placement_main_scope:
  "Local_Location ''answer'' \<in>
    set (scope_locations placement_prog prog_main_name)"
  by eval

subsection \<open>Selective executable projection\<close>

lemma placement_local_projection:
  "lookup_resolved_st_q placement_local_state (Global_Location ''balance'') =
    Ivl (Fin 10) (Fin 10)"
  "lookup_resolved_st_q placement_local_state (Global_Location ''request_count'') = bot"
  "lookup_resolved_st_q placement_side_state (Global_Location ''balance'') = bot"
  "lookup_resolved_st_q placement_side_state (Global_Location ''request_count'') =
    Ivl (Fin 4) (Fin 4)"
  by eval+

lemma placement_local_formal:
  "lookup_resolved_st_q placement_local_state (Local_Location ''x'') =
    Ivl MinInf PlusInf"
  "lookup_resolved_st_q placement_local_state (Local_Location ''tmp'') =
    Ivl MinInf PlusInf"
  by eval+

lemma placement_join_recovers_globals:
  "lookup_resolved_st_q
    (placement_local_state \<squnion> placement_side_state)
    (Global_Location ''balance'') =
    lookup_resolved_st_q placement_state (Global_Location ''balance'')"
  "lookup_resolved_st_q
    (placement_local_state \<squnion> placement_side_state)
    (Global_Location ''request_count'') =
    lookup_resolved_st_q placement_state (Global_Location ''request_count'')"
  by eval+

lemma placement_classic_projection:
  "lookup_resolved_st_q
    (project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      Exec_Placement.classic_keep_local placement_state)
    (Global_Location ''balance'') =
    lookup_resolved_st_q (restrict_local_resolved_q placement_state)
      (Global_Location ''balance'')"
  "lookup_resolved_st_q
    (project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      Exec_Placement.classic_publish_side placement_state)
    (Global_Location ''request_count'') =
    lookup_resolved_st_q (restrict_global_resolved_q placement_state)
      (Global_Location ''request_count'')"
  by eval+

end

