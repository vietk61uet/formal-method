theory Logic_Axiom_11
  imports Main
begin

(*a\<and>b \<or> a\<and>\<not>b == a*)

lemma axiom_11:
  shows "(a \<and> b) \<or> (a \<and> ~b) \<longleftrightarrow> a"
proof (rule iffI)
  assume "(a \<and> b) \<or> (a \<and> \<not>b)"
  then show "a"
  proof (rule disjE)
    assume "a \<and> b"
    then show "a" by (rule conjE)
  next
    assume "a \<and> \<not>b"
    then show "a" by (rule conjE)
  qed
next
  assume "a"
  then show "(a \<and> b) \<or> (a \<and> \<not>b)"
  proof (cases b)
    assume "b"
    with `a` have "a \<and> b" by (rule conjI)
    then show "(a \<and> b) \<or> (a \<and> \<not>b)" by (rule disjI1)
  next
    assume "\<not>b"
    with `a` have "a \<and> \<not>b" by (rule conjI)
    then show "(a \<and> b) \<or> (a \<and> \<not>b)" by (rule disjI2)
  qed
qed

end
