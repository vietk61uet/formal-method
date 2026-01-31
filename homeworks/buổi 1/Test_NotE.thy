theory Test_NotE
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   TEST: Các cách dùng notE rule
   ═══════════════════════════════════════════════════════════════════ *)

section ‹Test 1: Thử các cách viết khác nhau›

lemma test_notE_method1:
  assumes "a"
  assumes not_a: "¬a"
  shows "False"
  using not_a ‹a› by (rule notE)

lemma test_notE_method2:
  assumes "a"
  assumes not_a: "¬a"
  shows "False"
  using not_a assms(1) by (rule notE)

lemma test_notE_method3:
  assumes "a"
  assumes not_a: "¬a"
  shows "False"
  apply (rule notE)
   apply (rule not_a)
  apply (rule assms(1))
  done

lemma test_notE_method4:
  assumes "a"
  assumes not_a: "¬a"
  shows "False"
  by contradiction

section ‹Test 2: Trong Proof Block›

lemma test_in_proof:
  shows "P"
proof (rule classical)
  assume not_p: "¬P"
  (* Giả sử ta có P từ đâu đó *)
  have "P" sorry
  (* Bây giờ test các cách viết *)
  show "False"
    using not_p ‹P› by (rule notE)
qed

section ‹Test 3: Peirce's Law - Simplified›

lemma peirce_simple:
  shows "((a ⟶ b) ⟶ a) = a"
proof (rule iffI)
  assume H: "((a ⟶ b) ⟶ a)"
  show "a"
  proof (rule classical)
    assume not_a: "¬a"
    have imp: "a ⟶ b"
    proof (rule impI)
      assume a_assm: "a"
      (* Test notE here *)
      show "b"
      proof -
        from not_a a_assm have "False" by (rule notE)
        then show "b" by (rule FalseE)
      qed
    qed
    from H imp have "a" by (rule mp)
    then show "False"
      using not_a by (rule notE)
  qed
next
  assume "a"
  show "((a ⟶ b) ⟶ a)"
  proof (rule impI)
    assume "a ⟶ b"
    from ‹a› show "a" .
  qed
qed

end
