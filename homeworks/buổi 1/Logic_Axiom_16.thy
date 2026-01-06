theory Logic_Axiom_16
  imports Main
begin

(*(a\<Rightarrow>b\<Rightarrow>\<not>a) \<or> (b\<and>c \<Rightarrow> a\<and>c)*)

lemma axiom_16:
  shows "(a \<longrightarrow> b \<longrightarrow> ~a) \<or> ((b \<and> c) \<longrightarrow> (a \<and> c))"
proof (cases a)
  assume "a"
  have "(b \<and> c) \<longrightarrow> (a \<and> c)"
  proof (rule impI)
    assume "b \<and> c"
    then have "c" by (rule conjunct2)
    from `a` and `c` show "a \<and> c" by (rule conjI)
  qed
  then show ?thesis by (rule disjI2)
next
  assume "\<not>a"

  have "a \<longrightarrow> b \<longrightarrow> \<not>a"
  proof (rule impI)+
    assume "a"
    from `\<not>a` and `a` show "\<not>a" by contradiction
  qed
  then show ?thesis by (rule disjI1)
qed

end