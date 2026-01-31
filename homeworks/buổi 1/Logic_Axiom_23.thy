theory Logic_Axiom_23
  imports Main
begin

lemma complex_disjunction_proof:
  shows "(a ⟶ b ⟶ ¬a) ∨ ((b ∧ c) ⟶ (a ∧ c))"
proof (cases a)
  assume "a"
  -- "Case 1: a is True. We prove the right side: (b ∧ c) ⟶ (a ∧ c)"
  have "(b ∧ c) ⟶ (a ∧ c)"
  proof (rule impI)
    assume "b ∧ c"
    then have "c" by (rule conjunct2)
    from `a` and `c` show "a ∧ c" by (rule conjI)
  qed
  then show ?thesis by (rule disjI2)
next
  assume "¬a"
  -- "Case 2: a is False. We prove the left side: a ⟶ b ⟶ ¬a"
  have "a ⟶ b ⟶ ¬a"
  proof (rule impI)+
    assume "a"
    -- "Contradiction: we have ¬a and a"
    from `¬a` and `a` show "¬a" by contradiction
  qed
  then show ?thesis by (rule disjI1)
qed

(* Simple apply script *)
lemma "(a ⟶ b ⟶ ¬a) ∨ ((b ∧ c) ⟶ (a ∧ c))"
  apply (cases a)
   apply (rule disjI2, rule impI, rule conjI, assumption, erule conjunct2) -- "Case a=True"
  apply (rule disjI1, rule impI, rule impI, assumption) -- "Case a=False (trivial)"
  done

end
