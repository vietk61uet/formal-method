theory Logic_Axiom_8
  imports Main
begin

(*(a⇒b) ∧ (¬a ⇒ b) = b*)  
lemma axiom_8:
shows "(a ⟶ b) ∧ (¬a ⟶ b) \<longleftrightarrow> b"
  apply (rule iffI)
   apply (erule conjE)    
   apply (cases a)
    apply (erule impE)
     apply assumption
    apply assumption
   apply (erule_tac P="¬a" in impE)
    apply assumption
   apply assumption
  apply (rule conjI)
  apply (rule impI)
  apply assumption
  apply (rule impI)
  apply assumption   
  done
  

end