theory Logic_Axiom_18
  imports Main
begin

lemma redundancy_law:
  shows "(a ∧ b) ∨ (a ∧ ¬b) ⟷ a"
proof (rule iffI)
  -- "Forward direction: (a ∧ b) ∨ (a ∧ ¬b) ⟹ a"
  assume "(a ∧ b) ∨ (a ∧ ¬b)"
  then show "a"
  proof (rule disjE)
    -- "Case 1: a ∧ b"
    assume "a ∧ b"
    then show "a" by (rule conjE)
  next
    -- "Case 2: a ∧ ¬b"
    assume "a ∧ ¬b"
    then show "a" by (rule conjE)
  qed
next
  -- "Backward direction: a ⟹ (a ∧ b) ∨ (a ∧ ¬b)"
  assume "a"
  then show "(a ∧ b) ∨ (a ∧ ¬b)"
  proof (cases b)
    -- "Case 1: b is true"
    assume "b"
    with `a` have "a ∧ b" by (rule conjI)
    then show "(a ∧ b) ∨ (a ∧ ¬b)" by (rule disjI1)
  next
    -- "Case 2: b is false (¬b)"
    assume "¬b"
    with `a` have "a ∧ ¬b" by (rule conjI)
    then show "(a ∧ b) ∨ (a ∧ ¬b)" by (rule disjI2)
  qed
qed

(* Alternative proof using apply script *)
lemma redundancy_law_apply:
  shows "(a ∧ b) ∨ (a ∧ ¬b) ⟷ a"
  apply (rule iffI)
   apply (erule disjE)
    apply (erule conjE, assumption)
   apply (erule conjE, assumption)
  apply (case_tac b)
   apply (rule disjI1, rule conjI, assumption, assumption)
  apply (rule disjI2, rule conjI, assumption, assumption)
  done

end
