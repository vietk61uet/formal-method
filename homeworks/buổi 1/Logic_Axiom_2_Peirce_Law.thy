theory Logic_Axiom_2_Peirce_Law
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   PEIRCE'S LAW: ((a ⟶ b) ⟶ a) = a
   
   Đây là một trong những công thức khó nhất!
   Cần dùng CLASSICAL REASONING (proof by contradiction)
   ═══════════════════════════════════════════════════════════════════ *)

section ‹PHÂN TÍCH VẤN ĐỀ›

(*
   Goal: ((a ⟶ b) ⟶ a) = a
   
   Q: Goal có dạng gì?
   A: P = Q (equality/iff)
   
   Q: Cần rule gì?
   A: iffI (cần chứng minh 2 chiều)
   
   iffI rule:
   ─────────────────────────────────
   To prove: P = Q
   Need to prove:
     1. P ⟹ Q  (chiều xuôi)
     2. Q ⟹ P  (chiều ngược)
*)

section ‹CHIỀU 2 (DỄ): a ⟹ ((a ⟶ b) ⟶ a)›

(*
   Nếu đã có "a", thì chứng minh (a ⟶ b) ⟶ a rất dễ!
   
   Proof sketch:
   1. Assume: a                    [given]
   2. Show: (a ⟶ b) ⟶ a           [goal]
   3. Apply impI → assume (a ⟶ b), prove a
   4. Ta đã có a từ bước 1! → Trivial!
*)

lemma direction_2_easy:
  assumes "a"
  shows "((a ⟶ b) ⟶ a)"
proof (rule impI)
  assume "a ⟶ b"
  from assms show "a" .  (* Trivial - ta đã có a! *)
qed

section ‹CHIỀU 1 (KHÓ): ((a ⟶ b) ⟶ a) ⟹ a›

(*
   ĐÂY LÀ PHẦN KHÓ NHẤT!
   
   Có: ((a ⟶ b) ⟶ a)
   Cần chứng minh: a
   
   ❓ Làm sao chứng minh "a" từ "((a ⟶ b) ⟶ a)"???
   
   💡 GIẢI PHÁP: Dùng CLASSICAL REASONING (Proof by contradiction)
   
   Ý tưởng:
   1. Giả sử ¬a (ngược lại với điều cần chứng minh)
   2. Chứng minh dẫn đến mâu thuẫn (False)
   3. Vậy a phải đúng!
   
   classical rule:
   ───────────────────────────────
   To prove: P
   Method: Assume ¬P, derive False
*)

lemma direction_1_hard:
  assumes H: "((a ⟶ b) ⟶ a)"
  shows "a"
proof (rule classical)
  (* Assume ngược lại: giả sử ¬a *)
  assume not_a: "¬a"
  
  (*
     BÂY GIỜ TA CÓ:
     - Assumption 1: ((a ⟶ b) ⟶ a)    [from H]
     - Assumption 2: ¬a               [from classical]
     
     MỤC TIÊU: Chứng minh False (mâu thuẫn)
     
     CHIẾN LƯỢC:
     1. Tạo ra (a ⟶ b)
     2. Apply modus ponens: H + (a ⟶ b) → có "a"
     3. Mâu thuẫn với ¬a!
  *)
  
  (* BƯỚC 1: Chứng minh a ⟶ b *)
  have imp: "a ⟶ b"
  proof (rule impI)
    assume "a"
    (*
       BÂY GIỜ TA CÓ:
       - a       [vừa assume]
       - ¬a      [từ not_a]
       
       → Mâu thuẫn! → False
       → Từ False, suy ra bất kỳ thứ gì (ex falso quodlibet)
    *)
    show "b"
    proof -
      from not_a ‹a› have "False" by (rule notE)
      then show "b" by (rule FalseE)
    qed
  qed
  
  (* BƯỚC 2: Apply modus ponens *)
  from H imp have "a" by (rule mp)
  (*
     mp (modus ponens) rule:
     ─────────────────────────
     From: P ⟶ Q
     From: P
     Get: Q
     
     Trong trường hợp này:
     From: (a ⟶ b) ⟶ a   [H]
     From: a ⟶ b         [imp]
     Get: a
  *)
  
  (* BƯỚC 3: Mâu thuẫn! *)
  from ‹a› not_a show "False" by (rule notE)
  (*
     Ta có:
     - a     [vừa derive từ mp]
     - ¬a    [từ not_a]
     
     → Mâu thuẫn! → False
     → Classical reasoning thành công!
  *)
qed

section ‹PROOF ĐẦY ĐỦ›

lemma peirce_law:
  shows "((a ⟶ b) ⟶ a) = a"
proof (rule iffI)
  (* ═══════════════════════════════════════════════════════════
     CHIỀU 1: ((a ⟶ b) ⟶ a) ⟹ a
     ═══════════════════════════════════════════════════════════ *)
  assume H: "((a ⟶ b) ⟶ a)"
  show "a"
  proof (rule classical)
    assume not_a: "¬a"
    
    (* Chứng minh a ⟶ b *)
    have imp: "a ⟶ b"
    proof (rule impI)
      assume "a"
      from not_a ‹a› have "False" by (rule notE)
      from ‹False› show "b" by (rule FalseE)
    qed
    
    (* Modus ponens *)
    from H imp have "a" by (rule mp)
    
    (* Mâu thuẫn *)
    from not_a ‹a› show "False" by (rule notE)
  qed
  
next
  (* ═══════════════════════════════════════════════════════════
     CHIỀU 2: a ⟹ ((a ⟶ b) ⟶ a)
     ═══════════════════════════════════════════════════════════ *)
  assume "a"
  show "((a ⟶ b) ⟶ a)"
  proof (rule impI)
    assume "a ⟶ b"
    from ‹a› show "a" .  (* Trivial *)
  qed
qed

section ‹CÁCH 2: Apply-style›

lemma peirce_law_apply:
  shows "((a ⟶ b) ⟶ a) = a"
  apply (rule iffI)
  (* Chiều 1 *)
   apply (rule classical)
   apply (drule mp)
    apply (rule impI)
    apply (drule notE, assumption)
    apply (erule FalseE)
   apply (erule notE, assumption)
  (* Chiều 2 *)
  apply (rule impI)
  apply assumption
  done

section ‹VISUALIZATION›

(*
  PROOF TREE CHO CHIỀU 1:
  
  Goal: ((a ⟶ b) ⟶ a) ⟹ a
       │
       │ (apply classical - assume ¬a)
       ├─────────────────────────────────┐
       │                                 │
  Assumptions: ((a ⟶ b) ⟶ a), ¬a       Goal: False
       │
       │ (need to derive a)
       │ (strategy: prove (a ⟶ b) then apply mp)
       │
       ├─────────────────────────────────┐
       │                                 │
  Sub-goal: a ⟶ b                      │
       │                                 │
       │ (apply impI - assume a)         │
       │                                 │
  Assumptions: a, ¬a                    │
       │                                 │
       │ (contradiction!)                │
       │                                 │
  Have: False                            │
       │                                 │
       │ (ex falso quodlibet)            │
       │                                 │
  Proved: b                              │
       │                                 │
  Proved: a ⟶ b                         │
       │                                 │
       └─────────────────────────────────┤
                                         │
  Now apply mp:                          │
    From: (a ⟶ b) ⟶ a                  │
    From: a ⟶ b                        │
    Get: a                               │
                                         │
  Now we have: a AND ¬a                 │
       │                                 │
       │ (contradiction!)                │
       └─────────────────────────────────┤
                                         │
  Proved: False                          QED
*)

section ‹TÓM TẮT: Các Rules Quan Trọng›

(*
  ╔═══════════════════════════════════════════════════════════════╗
  ║  Rule         │  Khi nào dùng                                 ║
  ╠═══════════════════════════════════════════════════════════════╣
  ║  iffI         │  Chứng minh equality P = Q                    ║
  ║  classical    │  Chứng minh P bằng assume ¬P → derive False  ║
  ║  impI         │  Chứng minh implication P ⟶ Q               ║
  ║  mp           │  Modus ponens: từ P⟶Q và P → có Q           ║
  ║  notE         │  Từ ¬P và P → có False                       ║
  ║  FalseE       │  Từ False → suy ra bất kỳ thứ gì            ║
  ╚═══════════════════════════════════════════════════════════════╝
*)

end
