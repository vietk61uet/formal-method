theory Logic_Axiom_17
  imports Main
begin

lemma implication_law:
  shows "a ⟶ (b ⟶ a)"
proof (rule impI)
  assume "a"
  show "b ⟶ a"
  proof (rule impI)
    assume "b"
    show "a" by fact
  qed
qed

(* Alternative proof using apply script for simplicity in explanation *)
lemma implication_law_simple:
  shows "a ⟶ (b ⟶ a)"
  apply (rule impI)    -- "Assume a, goal becomes b ⟶ a"
  apply (rule impI)    -- "Assume b, goal becomes a"
  apply assumption     -- "Goal a is already an assumption"
  done

end
