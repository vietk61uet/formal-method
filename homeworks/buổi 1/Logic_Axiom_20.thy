theory Logic_Axiom_20
  imports Main
begin

(* Cách 1: Chia 4 trường hợp (Kiểu bảng chân trị) - Rất dễ hiểu *)
lemma complex_logic_simplified:
  shows "(¬a ⟶ b) ∧ (a ≠ b) ∨ ((a ∧ c) ⟶ (b ∧ c))"
proof (cases a)
  assume "a"
  show ?thesis
  proof (cases b)
    assume "b"
    -- "TH1: a=T, b=T. Chứng minh vế phải"
    have "(a ∧ c) ⟶ (b ∧ c)"
      using `a` `b` by (rule impI, erule conjE, intro conjI)
    then show ?thesis by (rule disjI2)
  next
    assume "¬b"
    -- "TH2: a=T, b=F. Chứng minh vế trái"
    have "(¬a ⟶ b) ∧ (a ≠ b)"
    proof (rule conjI)
      show "¬a ⟶ b" by (rule impI, contradiction)
      show "a ≠ b" using `a` `¬b` by (rule iffI, contradiction, contradiction)
    qed
    then show ?thesis by (rule disjI1)
  qed
next
  assume "¬a"
  show ?thesis
  proof (cases b)
    assume "b"
    -- "TH3: a=F, b=T. Chứng minh vế trái"
    have "(¬a ⟶ b) ∧ (a ≠ b)"
    proof (rule conjI)
      show "¬a ⟶ b" by (rule impI, fact)
      show "a ≠ b" using `¬a` `b` by (rule iffI, contradiction, contradiction)
    qed
    then show ?thesis by (rule disjI1)
  next
    assume "¬b"
    -- "TH4: a=F, b=F. Chứng minh vế phải"
    have "(a ∧ c) ⟶ (b ∧ c)"
      by (rule impI, erule conjE, contradiction)
    then show ?thesis by (rule disjI2)
  qed
qed

(* Cách 2: Apply script (đã sửa lỗi) *)
lemma complex_logic_apply_fixed:
  shows "(¬a ⟶ b) ∧ (a ≠ b) ∨ ((a ∧ c) ⟶ (b ∧ c))"
  apply (cases a)
   apply (cases b)
    apply (rule disjI2, rule impI, erule conjE, assumption) -- "a=T, b=T"
   apply (rule disjI1, rule conjI, rule impI, contradiction, rule iffI, contradiction, contradiction) -- "a=T, b=F"
  apply (cases b)
   apply (rule disjI1, rule conjI, rule impI, assumption, rule iffI, contradiction, contradiction) -- "a=F, b=T"
  apply (rule disjI2, rule impI, erule conjE, contradiction) -- "a=F, b=F"
  done

end
