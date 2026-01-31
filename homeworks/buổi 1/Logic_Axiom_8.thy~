theory Logic_Axiom_8
  imports Main
begin

lemma axiom_1:
  shows "False \<or> b = b"
  by auto

lemma axiom_2:                          
  shows "(a \<and> ~a) \<or> b = b"
  using axiom_1 by auto

lemma axiom_3:
  shows "(a \<or> b) \<and> (~a \<or> b) = b"
  using axiom_2 by blast

(*(a⇒b) ∧ (¬a ⇒ b) = b*)  
lemma axiom_8:
  shows "(a \<longrightarrow> b) \<and> (~a \<longrightarrow> b) = b"
  using axiom_3 by auto

end