theory Logic_Axiom_1
  imports Main
begin

(*a ∧ ¬b ⇒ a∨b*)
lemma logic_axiom_1:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  by (simp add: impI disjI1) 

end