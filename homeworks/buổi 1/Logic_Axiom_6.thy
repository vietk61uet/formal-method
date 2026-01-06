theory Logic_Axiom_6
  imports Main
begin

(*a=b \<or> a=c \<or> b=c*)

lemma equality_for_bool:
  assumes "a = b"
  shows "(a = b) \<or> (a = c) \<or> (b = c)"
  apply (rule disjI1)
  apply (rule assms)
  done
  

end