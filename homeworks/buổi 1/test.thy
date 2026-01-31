theory Debug_Example
  imports Main
begin

(* Bài gốc với auto *)
lemma original:
  shows "(a \<and> \<not>b) \<longrightarrow> a \<or> b"
  by auto

(* Dùng try0 để xem suggestions *)
lemma with_try0:
  shows "(a \<and> \<not>b) \<longrightarrow> a \<or> b"
  by try0
  (* Output: Try this: by blast, by simp, ... *)

(* Dùng sledgehammer suggestion *)
lemma with_sledgehammer:
  shows "(a \<and> \<not>b) \<longrightarrow> a \<or> b"
  by (metis disjI1 conjunct1 impI)

(* Viết lại thủ công để hiểu *)
lemma manual:
  shows "(a \<and> \<not>b) \<longrightarrow> a \<or> b"
proof
  assume "a \<and> \<not>b"
  then have "a" by (rule conjunct1)
  then show "a \<or> b" by (rule disjI1)
qed

end