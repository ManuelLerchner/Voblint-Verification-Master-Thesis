(* src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy *)
theorem (in collect_sem) gactivation_collect_sound:
  assumes "gactivation_coverage ev rv conv glob g S cover adm c\<^sub>0"
  shows "gactivation_collect adm c\<^sub>0 g S v c \<subseteq> cover v c"
