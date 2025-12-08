theory Logic_Axiom_5
  imports Main
begin

(*\<not>(a \<and> \<not>(a\<or>b))*)

lemma axiom_auto:
  shows "(~(a \<and> ~(a \<or> b)))"
  by auto

end