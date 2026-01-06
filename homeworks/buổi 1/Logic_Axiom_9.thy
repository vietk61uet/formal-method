theory Logic_Axiom_9
  imports Main
begin

(*a\<Rightarrow>(b\<Rightarrow>a)*)
lemma axiom_9:
  shows "a \<longrightarrow> (b \<longrightarrow> a)"
proof (rule impI)
  assume "a"
  show "b \<longrightarrow> a"
  proof (rule impI)
    assume "b"
    show "a"
      by assumption
  qed
qed             