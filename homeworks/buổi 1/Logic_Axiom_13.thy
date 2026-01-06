theory Logic_Axiom_13
  imports Main
begin

lemma axiom_13:
  shows "((\<not>a \<longrightarrow> b) \<and> (a \<noteq> b)) \<or> ((a \<and> c) \<longrightarrow> (b \<and> c))"
proof (cases "a \<and> c")
  case False
  (* (a \<and> c) \<longrightarrow> (b \<and> c) là đúng vì tiền đề không xảy ra *)
  have "(a \<and> c) \<longrightarrow> (b \<and> c)"
  proof (rule impI)
    assume "a \<and> c"
    from False and this show "b \<and> c" by contradiction
  qed
  thus ?thesis by (rule disjI2)

next
  case True
  have a: a by (rule conjunct1[OF True])
  have c: c by (rule conjunct2[OF True])

  show ?thesis
  proof (cases b)
    case True
    have "(a \<and> c) \<longrightarrow> (b \<and> c)"
    proof (rule impI)
      assume "a \<and> c"
      from True have b: b .
      from b c show "b \<and> c" by (rule conjI)
    qed
    thus ?thesis by (rule disjI2)

  next
    case False
    have nab: "\<not>a \<longrightarrow> b"
    proof (rule impI)
      assume "\<not>a"
      from False show b by contradiction
    qed
    have anb: "a \<noteq> b"
    proof (rule neqI)
      assume "a = b"
      from a False this show False by contradiction
    qed

    from nab anb have "(\<not>a \<longrightarrow> b) \<and> (a \<noteq> b)"
      by (rule conjI)
    thus ?thesis by (rule disjI1)
  qed
qed

end
