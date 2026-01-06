theory Dining_Philosophers
  imports Main
begin

lemma logic_of_forks:
  assumes "L1 \<and> R0 \<Longrightarrow> False"
      and "L2 \<and> R1 \<Longrightarrow> False"
      and "L3 \<and> R2 \<Longrightarrow> False"
      and "L4 \<and> R3 \<Longrightarrow> False"
      and "L0 \<and> R4 \<Longrightarrow> False"
  shows True
  by simp


lemma deadlock_is_starvation:
  fixes L0 L1 L2 L3 L4 R0 R1 R2 R3 R4 :: bool
  assumes exclusive:
    "\<not>(L1 \<and> R0)"
    "\<not>(L2 \<and> R1)"
    "\<not>(L3 \<and> R2)"
    "\<not>(L4 \<and> R3)"
    "\<not>(L0 \<and> R4)"
  assumes everyone_holds_left:
    "L0" "L1" "L2" "L3" "L4"
  shows
    "\<not>R0 \<and> \<not>R1 \<and> \<not>R2 \<and> \<not>R3 \<and> \<not>R4"
  using assms by auto


lemma waiting_breaks_deadlock:
  fixes L0 L1 L2 L3 L4 R0 R1 R2 R3 R4 :: bool
  assumes exclusive:
    "\<not>(L1 \<and> R0)"
    "\<not>(L2 \<and> R1)"
    "\<not>(L3 \<and> R2)"
    "\<not>(L4 \<and> R3)"
    "\<not>(L0 \<and> R4)"
  assumes P4_waits: "\<not>L4"
  assumes others_hold_left:
    "L0" "L1" "L2" "L3"
  shows "\<not>(L4 \<and> R3)"
  using assms by auto

end
