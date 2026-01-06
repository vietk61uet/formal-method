theory Logic_Axiom_15
  imports Main
begin


(*(a\<Rightarrow>b) \<and> (c\<Rightarrow>d) \<and> (a\<or>c) \<Rightarrow> (b\<or>d)*)
lemma axiom_15:
  shows "(a \<longrightarrow> b) \<and> (c \<longrightarrow> d) \<and> (a \<or> c ) \<longrightarrow> (b \<or> d)"
proof (rule impI)
  assume H: "(a \<longrightarrow> b) \<and> (c \<longrightarrow> d) \<and> (a \<or> c)"
  from H have "a \<longrightarrow> b" by (rule conjunct1)
  from H have "(c \<longrightarrow> d) \<and> (a \<or> c)" by (rule conjunct2)
  then have "c \<longrightarrow> d" by (rule conjunct1)
  from H have "(c \<longrightarrow> d) \<and> (a \<or> c)" by (rule conjunct2)
  then have "a \<or> c" by (rule conjunct2)

  from `a \<or> c` show "b \<or> d"
  proof (rule disjE)
    assume "a"
    with `a \<longrightarrow> b` have "b" by (rule mp)
    then show "b \<or> d" by (rule disjI1)
  next
    assume "c"
    with `c \<longrightarrow> d` have "d" by (rule mp)
    then show "b \<or> d" by (rule disjI2)
  qed
qed

end