theory Logic_Axiom_2
  imports Main
begin


(*(a⇒b)⇒a = a*)
(*
a⇒b ≡ ¬a ∨ b.
(¬a∨b) ⇒ a ≡ ¬(¬a∨b) ∨ a ≡ (a ∧ ¬b) ∨ a ≡ a ∨ (a ∧ ¬b) ≡ a
*)

lemma implication_axiom_auto:
  shows "((a \<longrightarrow>  b) \<longrightarrow>  a) = a"
  by auto

end
