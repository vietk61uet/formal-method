theory Logic_Axiom_12
  imports Main
begin

(* Part 1: a \<longrightarrow> (a \<and> b) \<longleftrightarrow> a \<longrightarrow> b *)
lemma part1:
  shows "(a \<longrightarrow> (a \<and> b)) \<longleftrightarrow> (a \<longrightarrow> b)"
proof (rule iffI)
  assume "a \<longrightarrow> (a \<and> b)"
  show "a \<longrightarrow> b"
  proof (rule impI)
    assume "a"
    with `a \<longrightarrow> (a \<and> b)` have "a \<and> b" by (rule mp)
    then show "b" by (rule conjE)
  qed
next
  assume "a \<longrightarrow> b"
  show "a \<longrightarrow> (a \<and> b)"
  proof (rule impI)
    assume "a"
    with `a \<longrightarrow> b` have "b" by (rule mp)
    from `a` and `b` show "a \<and> b" by (rule conjI)
  qed
qed

(* Part 2: a \<longrightarrow> b \<longleftrightarrow> a \<or> b \<longrightarrow> b *)
lemma part2:
  shows "(a \<longrightarrow> b) \<longleftrightarrow> (a \<or> b \<longrightarrow> b)"
proof (rule iffI)
  assume "a \<longrightarrow> b"
  show "a \<or> b \<longrightarrow> b"
  proof (rule impI)
    assume "a \<or> b"
    then show "b"
    proof (rule disjE)
      assume "a"
      with `a \<longrightarrow> b` show "b" by (rule mp)
    next
      assume "b"
      then show "b" .
    qed
  qed
next
  assume "a \<or> b \<longrightarrow> b"
  show "a \<longrightarrow> b"
  proof (rule impI)
    assume "a"
    then have "a \<or> b" by (rule disjI1)
    with `a \<or> b \<longrightarrow> b` show "b" by (rule mp)
  qed
qed


(*a \<Rightarrow> a\<and>b == a\<Rightarrow>b == a\<or>b \<Rightarrow> b*)
lemma axiom_12:
  shows "a \<longrightarrow> (a \<and> b) = a \<longrightarrow> b = a \<or> b \<longrightarrow> b"
  using part1 part2 by auto

end