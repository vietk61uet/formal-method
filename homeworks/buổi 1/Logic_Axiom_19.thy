theory Logic_Axiom_19
  imports Main
begin

(* Part 1: a ⟶ (a ∧ b) ⟷ a ⟶ b *)
lemma part1:
  shows "(a ⟶ (a ∧ b)) ⟷ (a ⟶ b)"
proof (rule iffI)
  assume "a ⟶ (a ∧ b)"
  show "a ⟶ b"
  proof (rule impI)
    assume "a"
    with `a ⟶ (a ∧ b)` have "a ∧ b" by (rule mp)
    then show "b" by (rule conjE)
  qed
next
  assume "a ⟶ b"
  show "a ⟶ (a ∧ b)"
  proof (rule impI)
    assume "a"
    with `a ⟶ b` have "b" by (rule mp)
    from `a` and `b` show "a ∧ b" by (rule conjI)
  qed
qed

(* Part 2: a ⟶ b ⟷ a ∨ b ⟶ b *)
lemma part2:
  shows "(a ⟶ b) ⟷ (a ∨ b ⟶ b)"
proof (rule iffI)
  assume "a ⟶ b"
  show "a ∨ b ⟶ b"
  proof (rule impI)
    assume "a ∨ b"
    then show "b"
    proof (rule disjE)
      assume "a"
      with `a ⟶ b` show "b" by (rule mp)
    next
      assume "b"
      then show "b" .
    qed
  qed
next
  assume "a ∨ b ⟶ b"
  show "a ⟶ b"
  proof (rule impI)
    assume "a"
    then have "a ∨ b" by (rule disjI1)
    with `a ∨ b ⟶ b` show "b" by (rule mp)
  qed
qed

(* The final chain as requested by the user *)
lemma logic_chain:
  shows "(a ⟶ (a ∧ b)) = (a ⟶ b)"
    and "(a ⟶ b) = (a ∨ b ⟶ b)"
  using part1 part2 by auto

end
