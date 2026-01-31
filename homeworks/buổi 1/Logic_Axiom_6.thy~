theory Logic_Axiom_6
  imports Main
begin

(*a=b \<or> a=c \<or> b=c*)

lemma equality_for_bool:
  shows "((a::bool) = b) \<or> (a = c) \<or> (b = c)"
  by auto

lemma equality_when_a_equals_b:
  assumes "a = b"
  shows "(a = b) \<or> (a = c) \<or> (b = c)"
  using assms by auto (*using assumes*)

end