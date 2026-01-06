theory Logic_Axiom_14
  imports Main
begin

(*(a \<Rightarrow> a\<and>b) \<or> (b \<Rightarrow> a\<and>b)*)

lemma axiom_14:
  shows "(a \<longrightarrow> (a \<and> b)) \<or> (b \<longrightarrow> (a \<and> b))"
proof (cases a)
  assume "a"
  show ?thesis
  proof (cases b)
    assume "b"
    have "a \<longrightarrow> (a \<and> b)"
    proof (rule impI)
      assume "a"
      from `a` and `b` show "a \<and> b" by (rule conjI)
    qed
    then show ?thesis by (rule disjI1)
  next
    assume "\<not>b"
    have "b \<longrightarrow> (a \<and> b)"
    proof (rule impI)
      assume "b"
      with `\<not>b` show "a \<and> b" by contradiction
    qed
    then show ?thesis by (rule disjI2)
  qed
next
  assume "\<not>a"
  show ?thesis
  proof (cases b)
    assume "b"
    have "a \<longrightarrow> (a \<and> b)"
    proof (rule impI)
      assume "a"
      with `\<not>a` show "a \<and> b" by contradiction
    qed
    then show ?thesis by (rule disjI1)
  next
    assume "\<not>b"
    have "a \<longrightarrow> (a \<and> b)"
    proof (rule impI)
      assume "a"
      with `\<not>a` show "a \<and> b" by contradiction
    qed
    then show ?thesis by (rule disjI1)
  qed
qed

end