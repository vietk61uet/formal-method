theory Dining_Philosophers_Manual
  imports Main
begin

lemma logic_of_forks:
  assumes "L1 \<and> R0 \<Longrightarrow> False"
      and "L2 \<and> R1 \<Longrightarrow> False"
      and "L3 \<and> R2 \<Longrightarrow> False"
      and "L4 \<and> R3 \<Longrightarrow> False"
      and "L0 \<and> R4 \<Longrightarrow> False"
  shows True
  by (rule TrueI)

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
  shows "\<not>R0 \<and> \<not>R1 \<and> \<not>R2 \<and> \<not>R3 \<and> \<not>R4"
proof (rule conjI)
  show "\<not>R0"
  proof (rule notI)
    assume "R0"
    with `L1` have "L1 \<and> R0" by (rule conjI)
    with `\<not>(L1 \<and> R0)` show "False" by (rule notE)
  qed
next
  show "\<not>R1 \<and> \<not>R2 \<and> \<not>R3 \<and> \<not>R4"
  proof (rule conjI)
    show "\<not>R1"
    proof (rule notI)
      assume "R1"
      with `L2` have "L2 \<and> R1" by (rule conjI)
      with `\<not>(L2 \<and> R1)` show "False" by (rule notE)
    qed
  next
    show "\<not>R2 \<and> \<not>R3 \<and> \<not>R4"
    proof (rule conjI)
      show "\<not>R2"
      proof (rule notI)
        assume "R2"
        with `L3` have "L3 \<and> R2" by (rule conjI)
        with `\<not>(L3 \<and> R2)` show "False" by (rule notE)
      qed
    next
      show "\<not>R3 \<and> \<not>R4"
      proof (rule conjI)
        show "\<not>R3"
        proof (rule notI)
          assume "R3"
          with `L4` have "L4 \<and> R3" by (rule conjI)
          with `\<not>(L4 \<and> R3)` show "False" by (rule notE)
        qed
      next
        show "\<not>R4"
        proof (rule notI)
          assume "R4"
          with `L0` have "L0 \<and> R4" by (rule conjI)
          with `\<not>(L0 \<and> R4)` show "False" by (rule notE)
        qed
      qed
    qed
  qed
qed

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
proof (rule notI)
  assume "L4 \<and> R3"
  hence "L4" by (rule conjunct1)
  with `\<not>L4` show "False" by (rule notE)
qed

end
