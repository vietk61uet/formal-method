theory Logic_Axiom_16
  imports Main
begin

(*(a\<Rightarrow>b\<Rightarrow>\<not>a) \<or> (b\<and>c \<Rightarrow> a\<and>c)*)

lemma axiom_16:
  shows "(a \<longrightarrow> b \<longrightarrow> ~a) \<or> ((b \<and> c) \<longrightarrow> (a \<and> c))"
  by auto

end