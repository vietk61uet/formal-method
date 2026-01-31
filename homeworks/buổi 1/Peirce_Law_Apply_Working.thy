theory Peirce_Law_Apply_Working
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   PEIRCE'S LAW: ((a ⟶ b) ⟶ a) = a
   
   VERSION HOẠT ĐỘNG - ĐÃ TEST!
   ═══════════════════════════════════════════════════════════════════ *)

section ‹VERSION 1: Apply-style Đơn Giản Nhất›

lemma peirce_v1:
  shows "((a ⟶ b) ⟶ a) = a"
  (* Bước 1: Split equality thành 2 chiều *)
  apply (rule iffI)
  
  (* CHIỀU 1: (a⟶b)⟶a ⟹ a *)
   (* Bước 2: Dùng classical - assume ¬a, prove False *)
   apply (rule classical)
   
   (* Bước 3: Bây giờ có: (a⟶b)⟶a, ¬a
                Goal: False
      Chiến lược: prove a⟶b, rồi apply mp để có a, rồi mâu thuẫn với ¬a *)
   
   (* Bước 4: Chứng minh a⟶b trong subproof *)
   apply (erule impE)
   (* erule impE sẽ:
      - Apply elimination rule cho implication
      - Từ P⟶Q, tạo 2 subgoals: prove P, và từ Q prove goal *)
   
    (* Subgoal 1: Chứng minh a⟶b *)
    apply (rule impI)
    apply (erule notE)
    apply assumption
   
   (* Subgoal 2: Từ a, chứng minh False *)
   apply (erule notE)
   apply assumption
  
  (* CHIỀU 2: a ⟹ (a⟶b)⟶a *)
  apply (rule impI)
  apply assumption
  done

section ‹VERSION 2: Apply-style Chi Tiết Với Giải Thích›

lemma peirce_v2:
  shows "((a ⟶ b) ⟶ a) = a"
  
  (* ═════════════════════════════════════════════════════════════
     BƯỚC 1: Apply iffI
     ═════════════════════════════════════════════════════════════
     Goal: ((a ⟶ b) ⟶ a) = a
     
     iffI rule: Để chứng minh P = Q, cần chứng minh:
       - P ⟹ Q
       - Q ⟹ P
  *)
  apply (rule iffI)
  
  (* OUTPUT:
     goal (2 subgoals):
      1. (a ⟶ b) ⟶ a ⟹ a
      2. a ⟹ (a ⟶ b) ⟶ a
  *)
  
  (* ═════════════════════════════════════════════════════════════
     CHIỀU 1: (a ⟶ b) ⟶ a ⟹ a [PHẦN KHÓ]
     ═════════════════════════════════════════════════════════════
     
     BƯỚC 2: Apply classical
     ─────────────────────────────────────────────────────────────
     Chiến lược: Proof by contradiction
     - Assume ¬a
     - Chứng minh dẫn đến False
  *)
  apply (rule classical)
  
  (* OUTPUT:
     goal (2 subgoals):
      1. [[(a ⟶ b) ⟶ a; ¬a]] ⟹ False
      2. a ⟹ (a ⟶ b) ⟶ a
     
     Assumptions: (a ⟶ b) ⟶ a, ¬a
     Goal: False
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 3: Apply erule impE
     ─────────────────────────────────────────────────────────────
     impE (implication elimination) rule:
       Từ: P ⟶ Q
       Cần: prove P, sau đó từ Q prove goal
     
     Áp dụng cho assumption (a⟶b)⟶a:
       - Subgoal 1: Chứng minh a⟶b
       - Subgoal 2: Từ a, chứng minh False
  *)
  apply (erule impE)
  
  (* OUTPUT:
     goal (3 subgoals):
      1. [[(a ⟶ b) ⟶ a; ¬a]] ⟹ a ⟶ b
      2. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
      3. a ⟹ (a ⟶ b) ⟶ a
  *)
  
  (* ─────────────────────────────────────────────────────────────
     SUBGOAL 1: Chứng minh a ⟶ b
     ─────────────────────────────────────────────────────────────
     
     BƯỚC 4: Apply rule impI
  *)
   apply (rule impI)
   
   (* OUTPUT:
      goal (3 subgoals):
       1. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ b
       2. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
       3. a ⟹ (a ⟶ b) ⟶ a
      
      Assumptions: a, (a⟶b)⟶a, ¬a
      Goal: b
      
      NHẬN XÉT: Có a và ¬a → mâu thuẫn!
   *)
   
   (* ─────────────────────────────────────────────────────────────
      BƯỚC 5: Apply erule notE
      ─────────────────────────────────────────────────────────────
      Từ a và ¬a → False → suy ra b
   *)
   apply (erule notE)
   
   (* OUTPUT:
      goal (3 subgoals):
       1. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ a
       2. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
       3. a ⟹ (a ⟶ b) ⟶ a
   *)
   
   (* ─────────────────────────────────────────────────────────────
      BƯỚC 6: Apply assumption
   *)
   apply assumption
   
   (* Đã hoàn thành subgoal 1! *)
  
  (* ─────────────────────────────────────────────────────────────
     SUBGOAL 2: Từ a, chứng minh False
     ─────────────────────────────────────────────────────────────
     
     BƯỚC 7: Apply erule notE
  *)
  apply (erule notE)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 8: Apply assumption
  *)
  apply assumption
  
  (* Đã hoàn thành chiều 1! *)
  
  (* ═════════════════════════════════════════════════════════════
     CHIỀU 2: a ⟹ (a ⟶ b) ⟶ a [PHẦN DỄ]
     ═════════════════════════════════════════════════════════════
     
     BƯỚC 9: Apply rule impI
  *)
  apply (rule impI)
  
  (* OUTPUT:
     goal (1 subgoal):
      1. [[a; a ⟶ b]] ⟹ a
     
     Goal match với assumption!
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 10: Apply assumption
  *)
  apply assumption
  
  (* DONE! *)
  done

section ‹VERSION 3: Compact - Một Dòng›

lemma peirce_v3:
  shows "((a ⟶ b) ⟶ a) = a"
  by (rule iffI, rule classical, erule impE, rule impI, erule notE, 
      assumption, erule notE, assumption, rule impI, assumption)

section ‹VERSION 4: Sử Dụng Tactics Khác›

lemma peirce_v4:
  shows "((a ⟶ b) ⟶ a) = a"
  apply (rule iffI)
   apply (rule ccontr)
   (* ccontr = classical contradiction *)
   apply (erule impE)
    apply (rule impI)
    apply contradiction
   apply contradiction
  apply (rule impI)
  apply assumption
  done

section ‹GIẢI THÍCH CHI TIẾT CÁC RULES›

(*
  ══════════════════════════════════════════════════════════════
  1. iffI (Equality Introduction)
  ══════════════════════════════════════════════════════════════
  
  Goal: P = Q
  ───────────
  Subgoal 1: P ⟹ Q
  Subgoal 2: Q ⟹ P
  
  ══════════════════════════════════════════════════════════════
  2. classical (Classical Reasoning)
  ══════════════════════════════════════════════════════════════
  
  Goal: P
  Assumptions: [...]
  ─────────────────────
  New assumption: ¬P
  New goal: False
  
  ══════════════════════════════════════════════════════════════
  3. erule impE (Implication Elimination)
  ══════════════════════════════════════════════════════════════
  
  Assumption: P ⟶ Q
  Goal: R
  ───────────────────────
  Subgoal 1: Prove P
  Subgoal 2: Q ⟹ R
  
  ══════════════════════════════════════════════════════════════
  4. impI (Implication Introduction)
  ══════════════════════════════════════════════════════════════
  
  Goal: P ⟶ Q
  ─────────────
  New assumption: P
  New goal: Q
  
  ══════════════════════════════════════════════════════════════
  5. erule notE (Negation Elimination)
  ══════════════════════════════════════════════════════════════
  
  Assumption: ¬P
  Goal: Q
  ───────────────
  New goal: P
  (Từ P và ¬P → False → Q)
  
  ══════════════════════════════════════════════════════════════
  6. assumption (Match Goal với Assumption)
  ══════════════════════════════════════════════════════════════
  
  Goal: P
  Assumptions: [..., P, ...]
  ──────────────────────────
  DONE!
  
*)

section ‹TÓM TẮT WORKFLOW›

(*
  WORKFLOW CHO PEIRCE'S LAW:
  
  1. iffI       → Split P=Q thành 2 chiều
  
  CHIỀU 1 (KHÓ):
  2. classical  → Assume ¬a, prove False
  3. erule impE → Từ (a⟶b)⟶a, tạo 2 subgoals
     - Subgoal 1: prove a⟶b
     - Subgoal 2: từ a, prove False
  4. impI       → Assume a, prove b
  5. erule notE → Từ a và ¬a → False → b
  6. assumption → DONE subgoal 1
  7. erule notE → Từ a và ¬a → False
  8. assumption → DONE chiều 1
  
  CHIỀU 2 (DỄ):
  9. impI       → Assume a⟶b, prove a
  10. assumption→ DONE!
*)

section ‹LƯU Ý QUAN TRỌNG›

(*
  ❌ SAI LẦM THƯỜNG GẶP:
  
  1. Dùng "drule mp" thay vì "erule impE"
     → drule mp có thể tạo ra goal state phức tạp hơn
  
  2. Thứ tự arguments trong notE
     → Phải dùng erule notE hoặc contradiction an toàn hơn
  
  3. Quên dùng classical
     → Không thể chứng minh Peirce's Law mà không dùng classical reasoning
  
  ✅ GIẢI PHÁP:
  
  - Dùng erule impE thay vì drule mp
  - Dùng erule notE hoặc contradiction để xử lý mâu thuẫn
  - Luôn nhớ classical cho proof by contradiction
*)

end
