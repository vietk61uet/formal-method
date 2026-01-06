theory Logic_Axiom_7
  imports Main
begin

(*(a \<Rightarrow> \<not>a) \<Rightarrow> \<not>a*)

lemma axiom_auto:
  shows "(a \<longrightarrow> ~a) \<longrightarrow> ~a"
  apply (rule impI)
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done
end