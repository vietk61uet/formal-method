theory Logic_Axiom_13
  imports Main
begin

(*(\<not>a\<Rightarrow>\<not>b) \<and> (a # b) \<or> (a\<and>c \<Rightarrow> b\<and>c)*)
lemma axiom_13:
  shows "(~a \<longrightarrow> b) \<and> (a \<noteq>  b) \<or> ((a \<and> c) \<longrightarrow> (b \<and> c))"
  by auto

end