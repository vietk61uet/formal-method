theory Logic_Axiom_22
  imports Main
begin

lemma constructive_dilemma:
  shows "(a ⟶ b) ∧ (c ⟶ d) ∧ (a ∨ c) ⟶ (b ∨ d)"
proof (rule impI)
  assume "H: (a ⟶ b) ∧ (c ⟶ d) ∧ (a ∨ c)"
  
  (* Deconstruct assumptions correctly *)
  (* H is (a ⟶ b) ∧ ((c ⟶ d) ∧ (a ∨ c)) due to right associativity *)
  from H have "a ⟶ b" by (rule conjunct1)
  
  from H have "(c ⟶ d) ∧ (a ∨ c)" by (rule conjunct2)
  then have "c ⟶ d" by (rule conjunct1)
  
  from H have "(c ⟶ d) ∧ (a ∨ c)" by (rule conjunct2)
  then have "a ∨ c" by (rule conjunct2)
  
  (* Perform case analysis on a ∨ c *)
  from `a ∨ c` show "b ∨ d"
  proof (rule disjE)
    assume "a"
    -- "Case 1: a is true"
    with `a ⟶ b` have "b" by (rule mp)
    then show "b ∨ d" by (rule disjI1)
  next
    assume "c"
    -- "Case 2: c is true"
    with `c ⟶ d` have "d" by (rule mp)
    then show "b ∨ d" by (rule disjI2)
  qed
qed

(* Apply script version *)
lemma constructive_dilemma_apply:
  shows "(a ⟶ b) ∧ (c ⟶ d) ∧ (a ∨ c) ⟶ (b ∨ d)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule disjE)
   apply (erule impE, assumption, rule disjI1, assumption) -- "Case a -> b implies b -> b v d"
  apply (rotate_tac 1) -- "Bring c -> d to front"
  apply (erule impE, assumption, rule disjI2, assumption) -- "Case c -> d implies d -> b v d"
  done

end
