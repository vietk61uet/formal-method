theory Logic_Axiom_21
  imports Main
begin

lemma linearity_of_implication_variant:
  shows "(a ⟶ (a ∧ b)) ∨ (b ⟶ (a ∧ b))"
proof (cases a)
  assume "a"
  show ?thesis
  proof (cases b)
    assume "b"
    -- "Case 1: a=T, b=T. Both implications are true."
    have "a ⟶ (a ∧ b)"
    proof (rule impI)
      assume "a"
      from `a` and `b` show "a ∧ b" by (rule conjI)
    qed
    then show ?thesis by (rule disjI1)
  next
    assume "¬b"
    -- "Case 2: a=T, b=F. We check if b ⟶ (a ∧ b) holds."
    -- "Since b is False, b ⟶ Anything is True."
    have "b ⟶ (a ∧ b)"
    proof (rule impI)
      assume "b"
      with `¬b` show "a ∧ b" by contradiction
    qed
    then show ?thesis by (rule disjI2)
  qed
next
  assume "¬a"
  show ?thesis
  proof (cases b)
    assume "b"
    -- "Case 3: a=F, b=T. We check if a ⟶ (a ∧ b) holds."
    -- "Since a is False, a ⟶ Anything is True."
    have "a ⟶ (a ∧ b)"
    proof (rule impI)
      assume "a"
      with `¬a` show "a ∧ b" by contradiction
    qed
    then show ?thesis by (rule disjI1)
  next
    assume "¬b"
    -- "Case 4: a=F, b=F. Both implications are vacuously true."
    have "a ⟶ (a ∧ b)"
    proof (rule impI)
      assume "a"
      with `¬a` show "a ∧ b" by contradiction
    qed
    then show ?thesis by (rule disjI1)
  qed
qed

(* Apply script version *)
lemma "(a ⟶ (a ∧ b)) ∨ (b ⟶ (a ∧ b))"
  apply (cases a)
   apply (cases b)
    apply (rule disjI1, rule impI, rule conjI, assumption, assumption) -- "T, T"
   apply (rule disjI2, rule impI, erule notE, assumption) -- "T, F"
  apply (rule disjI1, rule impI, erule notE, assumption) -- "F, ?"
  done

end
