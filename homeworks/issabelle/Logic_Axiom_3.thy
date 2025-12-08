theory Logic_Axiom_3
  imports Main
begin

(*
a ∧ ¬a ⇒ b
*)

lemma implication_axiom_auto:
  shows "(a \<and>  ~a) \<longrightarrow> b"
  by auto
                       
end
