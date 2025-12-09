theory Logic_Axiom_12
  imports Main
begin

(*a \<Rightarrow> a\<and>b == a\<Rightarrow>b == a\<or>b \<Rightarrow> b*)
lemma axiom_12:
  shows "a \<longrightarrow> (a \<and> b) = a \<longrightarrow> b = a \<or> b \<longrightarrow> b"
  by auto

end