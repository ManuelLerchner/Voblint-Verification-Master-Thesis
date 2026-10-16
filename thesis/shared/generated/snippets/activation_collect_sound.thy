(* src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy *)
theorem activation_collect_sound:
  assumes "activation_coverage \<kappa> g S cover adm c\<^sub>0"
  shows "\<A>\<^bsub>\<kappa>,adm,c\<^sub>0,g,S\<^esub> v c \<subseteq> cover v c"
