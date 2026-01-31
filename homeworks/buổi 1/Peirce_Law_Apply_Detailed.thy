theory Peirce_Law_Apply_Detailed
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   PEIRCE'S LAW: ((a ⟶ b) ⟶ a) = a
   
   PHƯƠNG PHÁP: Apply-style với giải thích từng bước
   ═══════════════════════════════════════════════════════════════════ *)

section ‹PHÂN TÍCH BAN ĐẦU›

(*
  GOAL: ((a ⟶ b) ⟶ a) = a
  
  Đây là Peirce's Law - một trong những định lý khó nhất!
  
  CHIẾN LƯỢC TỔNG QUÁT:
  1. Dùng iffI vì goal có dạng P = Q
  2. Chứng minh 2 chiều:
     - Chiều 1: ((a ⟶ b) ⟶ a) ⟹ a  (KHÓ - cần classical)
     - Chiều 2: a ⟹ ((a ⟶ b) ⟶ a)  (DỄ - trivial)
*)

section ‹PROOF TỪNG BƯỚC - APPLY STYLE›

lemma peirce_law_apply_detailed:
  shows "((a ⟶ b) ⟶ a) = a"
  
  (* ═════════════════════════════════════════════════════════════
     BƯỚC 1: Apply iffI
     ═════════════════════════════════════════════════════════════
     
     GOAL CŨ: ((a ⟶ b) ⟶ a) = a
     
     Q: Goal có dạng gì?
     A: P = Q (equality)
     
     Q: Cần rule gì?
     A: iffI (if and only if introduction)
     
     GIẢI THÍCH: iffI sẽ split thành 2 subgoals:
       Subgoal 1: ((a ⟶ b) ⟶ a) ⟹ a        (chiều xuôi)
       Subgoal 2: a ⟹ ((a ⟶ b) ⟶ a)        (chiều ngược)
  *)
  apply (rule iffI)
  
  (* OUTPUT SAU BƯỚC 1:
     proof (prove)
     goal (2 subgoals):
      1. (a ⟶ b) ⟶ a ⟹ a
      2. a ⟹ (a ⟶ b) ⟶ a
  *)
  
  (* ═════════════════════════════════════════════════════════════
     SUBGOAL 1: ((a ⟶ b) ⟶ a) ⟹ a
     
     ĐÂY LÀ PHẦN KHÓ NHẤT!
     Có: (a ⟶ b) ⟶ a
     Cần chứng minh: a
     
     Làm sao chứng minh a từ (a ⟶ b) ⟶ a ???
     → Dùng CLASSICAL REASONING (proof by contradiction)
     ═════════════════════════════════════════════════════════════
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 2: Apply classical
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: (a ⟶ b) ⟶ a ⟹ a
     
     Q: Làm sao chứng minh a?
     A: Dùng classical (proof by contradiction)
     
     GIẢI THÍCH: classical rule cho phép ta:
       - Assume ¬a (ngược lại với điều cần chứng minh)
       - Chứng minh dẫn đến mâu thuẫn (False)
       - Từ đó suy ra a phải đúng!
     
     classical rule:
       To prove: P
       Method: Assume ¬P, then prove False
  *)
  apply (rule classical)
  
  (* OUTPUT SAU BƯỚC 2:
     goal (2 subgoals):
      1. [[(a ⟶ b) ⟶ a; ¬a]] ⟹ False
      2. a ⟹ (a ⟶ b) ⟶ a
     
     PHÂN TÍCH SUBGOAL 1:
     Assumptions:
       - H1: (a ⟶ b) ⟶ a
       - H2: ¬a
     Goal: False (mâu thuẫn)
     
     CHIẾN LƯỢC:
     1. Tạo ra (a ⟶ b)
     2. Apply modus ponens: H1 + (a ⟶ b) → có a
     3. Mâu thuẫn giữa a và ¬a → False!
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 3: Apply drule mp
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: [[(a ⟶ b) ⟶ a; ¬a]] ⟹ False
     
     Q: Làm sao derive a từ (a ⟶ b) ⟶ a?
     A: Dùng modus ponens (mp)
     
     mp rule:
       Có: P ⟶ Q
       Có: P
       ──────────
       Suy ra: Q
     
     Trong trường hợp này:
       Có: (a ⟶ b) ⟶ a   [assumption]
       Cần: a ⟶ b        [phải chứng minh!]
       ──────────────
       Suy ra: a
     
     GIẢI THÍCH drule:
       - drule = destructive rule (apply rule vào assumption)
       - drule mp: Từ assumption P⟶Q, tạo ra subgoal để chứng minh P
  *)
  apply (drule mp)
  
  (* OUTPUT SAU BƯỚC 3:
     goal (2 subgoals):
      1. [[(a ⟶ b) ⟶ a; ¬a]] ⟹ a ⟶ b
      2. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
      3. a ⟹ (a ⟶ b) ⟶ a
     
     PHÂN TÍCH:
     Bây giờ có 3 subgoals:
       Subgoal 1: Chứng minh a ⟶ b
       Subgoal 2: Từ a và ¬a, chứng minh False
       Subgoal 3: Chiều 2 của iffI (chưa đến)
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 4: Apply rule impI (cho subgoal 1)
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: [[(a ⟶ b) ⟶ a; ¬a]] ⟹ a ⟶ b
     
     Q: Goal có dạng gì?
     A: P ⟶ Q (implication)
     
     Q: Cần rule gì?
     A: impI (implication introduction)
     
     GIẢI THÍCH: impI sẽ:
       - Assume a (tiền đề)
       - Cần chứng minh b (kết luận)
  *)
  apply (rule impI)
  
  (* OUTPUT SAU BƯỚC 4:
     goal (2 subgoals):
      1. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ b
      2. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
      3. a ⟹ (a ⟶ b) ⟶ a
     
     PHÂN TÍCH SUBGOAL 1:
     Assumptions:
       - a       [vừa assume]
       - (a ⟶ b) ⟶ a
       - ¬a      [từ classical]
     Goal: b
     
     NHẬN XÉT: Ta có CẢ a VÀ ¬a → MÂU THUẪN!
     Từ mâu thuẫn → False → suy ra bất kỳ thứ gì (ex falso quodlibet)
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 5: Apply erule FalseE
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ b
     
     Q: Làm sao chứng minh b từ mâu thuẫn?
     A: Chứng minh False trước, rồi dùng FalseE
     
     GIẢI THÍCH:
       - FalseE: Từ False, suy ra bất kỳ thứ gì
       - erule FalseE: Tìm cách chứng minh False từ assumptions
  *)
  apply (erule FalseE)
  
  (* OUTPUT SAU BƯỚC 5:
     goal (2 subgoals):
      1. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
      2. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
      3. a ⟹ (a ⟶ b) ⟶ a
     
     NHẬN XÉT: Subgoal 1 và 2 giống nhau!
     Cả 2 đều cần chứng minh False từ a và ¬a
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 6: Apply erule notE (cho subgoal 1)
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
     
     Q: Làm sao chứng minh False?
     A: Có a và ¬a → dùng notE
     
     notE rule:
       Có: ¬P
       Có: P
       ──────────
       Suy ra: False
     
     GIẢI THÍCH erule notE:
       - erule = elimination rule
       - notE: Từ ¬P và P → False
       - erule notE sẽ tìm ¬P trong assumptions, tạo subgoal chứng minh P
  *)
  apply (erule notE)
  
  (* OUTPUT SAU BƯỚC 6:
     goal (2 subgoals):
      1. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ a
      2. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
      3. a ⟹ (a ⟶ b) ⟶ a
     
     PHÂN TÍCH SUBGOAL 1:
     Assumptions: a, (a ⟶ b) ⟶ a, ¬a
     Goal: a
     
     Goal match với assumption đầu tiên! → Dùng assumption
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 7: Apply assumption
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ a
     
     Q: Goal có trong assumptions không?
     A: Có! assumption đầu tiên chính là a
     
     GIẢI THÍCH assumption:
       - Tìm trong assumptions có fact nào match với goal không
       - Nếu có → DONE!
  *)
  apply assumption
  
  (* OUTPUT SAU BƯỚC 7:
     goal (2 subgoals):
      1. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
      2. a ⟹ (a ⟶ b) ⟶ a
     
     TIẾN TRIỂN: Đã giải xong subgoal đầu tiên!
     Bây giờ còn 2 subgoals.
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 8: Apply erule notE (cho subgoal 1 còn lại)
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ False
     
     Tương tự bước 6, dùng notE để chứng minh False từ a và ¬a
  *)
  apply (erule notE)
  
  (* OUTPUT SAU BƯỚC 8:
     goal (2 subgoals):
      1. [[a; (a ⟶ b) ⟶ a; ¬a]] ⟹ a
      2. a ⟹ (a ⟶ b) ⟶ a
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 9: Apply assumption
     ─────────────────────────────────────────────────────────────
     
     Tương tự bước 7
  *)
  apply assumption
  
  (* OUTPUT SAU BƯỚC 9:
     goal (1 subgoal):
      1. a ⟹ (a ⟶ b) ⟶ a
     
     TIẾN TRIỂN: Đã hoàn thành CHIỀU 1 (phần khó)!
     Bây giờ còn CHIỀU 2 (phần dễ)
  *)
  
  (* ═════════════════════════════════════════════════════════════
     SUBGOAL 2: a ⟹ ((a ⟶ b) ⟶ a)
     
     ĐÂY LÀ PHẦN DỄ!
     Có: a
     Cần chứng minh: (a ⟶ b) ⟶ a
     
     CHIẾN LƯỢC:
     1. Apply impI → assume (a ⟶ b)
     2. Cần chứng minh a, mà ta đã có a sẵn rồi!
     ═════════════════════════════════════════════════════════════
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 10: Apply rule impI
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: a ⟹ (a ⟶ b) ⟶ a
     
     Q: Goal có dạng gì?
     A: P ⟶ Q (implication)
     
     Q: Cần rule gì?
     A: impI
  *)
  apply (rule impI)
  
  (* OUTPUT SAU BƯỚC 10:
     goal (1 subgoal):
      1. [[a; a ⟶ b]] ⟹ a
     
     PHÂN TÍCH:
     Assumptions: a, a ⟶ b
     Goal: a
     
     Goal match với assumption đầu tiên!
  *)
  
  (* ─────────────────────────────────────────────────────────────
     BƯỚC 11: Apply assumption
     ─────────────────────────────────────────────────────────────
     
     GOAL CŨ: [[a; a ⟶ b]] ⟹ a
     
     Goal match với assumption!
  *)
  apply assumption
  
  (* OUTPUT SAU BƯỚC 11:
     No subgoals!
     
     🎉 DONE! Đã chứng minh xong!
  *)
  done

section ‹PROOF NGẮN GỌN - KHÔNG GIẢI THÍCH›

lemma peirce_law_apply_short:
  shows "((a ⟶ b) ⟶ a) = a"
  apply (rule iffI)
   apply (rule classical)
   apply (drule mp)
    apply (rule impI)
    apply (erule FalseE)
    apply (erule notE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (rule impI)
  apply assumption
  done

section ‹TÓM TẮT WORKFLOW›

(*
  ══════════════════════════════════════════════════════════════
  QUY TRÌNH APPLY - PEIRCE'S LAW
  ══════════════════════════════════════════════════════════════
  
  1. iffI          → Split P=Q thành 2 chiều
  
  CHIỀU 1: (a⟶b)⟶a ⟹ a (KHÓ)
    2. classical → Assume ¬a, prove False
    3. drule mp  → Apply modus ponens, cần chứng minh a⟶b
    4. impI      → Assume a, prove b
    5. FalseE    → Từ False suy ra b
    6. notE      → Từ a và ¬a suy ra False
    7. assumption→ Goal = assumption
    8. notE      → Lại dùng notE cho subgoal còn lại
    9. assumption→ DONE chiều 1
  
  CHIỀU 2: a ⟹ (a⟶b)⟶a (DỄ)
    10. impI     → Assume a⟶b
    11. assumption→ DONE!
  
  ══════════════════════════════════════════════════════════════
*)

section ‹BẢNG TRA CỨU RULES DÙNG›

(*
  ╔═══════════════════════════════════════════════════════════════╗
  ║  Rule      │  Khi nào dùng           │  Hiệu quả           ║
  ╠═══════════════════════════════════════════════════════════════╣
  ║  iffI      │  Goal: P = Q            │  Split thành 2 chiều║
  ║  classical │  Chứng minh P khó       │  Assume ¬P → False  ║
  ║  drule mp  │  Có P⟶Q trong assump │  Tạo subgoal prove P║
  ║  impI      │  Goal: P ⟶ Q           │  Assume P, prove Q  ║
  ║  erule FalseE│ Cần chứng minh từ False│ Tạo subgoal False ║
  ║  erule notE│  Có ¬P trong assump    │  Tạo subgoal prove P║
  ║  assumption│  Goal trong assump     │  Match & DONE       ║
  ╚═══════════════════════════════════════════════════════════════╝
*)

end
