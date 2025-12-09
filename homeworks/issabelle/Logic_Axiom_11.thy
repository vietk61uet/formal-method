theory Logic_Axiom_11
  imports Main
begin

(*a\<and>b \<or> a\<and>\<not>b == a*)

lemma axiom_11:
  shows "(a \<and> b) \<or> (a \<and> ~b) = a"
  by auto

end
