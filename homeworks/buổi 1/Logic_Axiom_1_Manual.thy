theory Logic_Axiom_1_Manual
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   BÀI TẬP: (a ∧ ¬b) ⟶ a ∨ b
   
   PHƯƠNG PHÁP: Phân tích HOÀN TOÀN THỦ CÔNG
   ═══════════════════════════════════════════════════════════════════ *)

section ‹BƯỚC 1: Phân Tích Goal›

(* 
   Initial Goal: (a ∧ ¬b) ⟶ a ∨ b
   
   Q: Goal có dạng gì?
   A: P ⟶ Q (implication)
   
   Q: Cần rule gì để chứng minh implication?
   A: impI (Implication Introduction)
   
   impI rule:
   ─────────────────
   To prove: P ⟶ Q
   Need to: Assume P, then prove Q
*)

section ‹BƯỚC 2: Apply impI›

lemma logic_axiom_1_step_by_step:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
proof (rule impI)
  (* Sau khi apply impI:
     New goal: a ∨ b
     Assumptions: a ∧ ¬b
  *)
  
  assume H: "a ∧ ¬b"
  
  (* 
     BƯỚC 3: Phân tích goal mới
     
     Current Goal: a ∨ b
     
     Q: Goal có dạng gì?
     A: P ∨ Q (disjunction)
     
     Q: Cần rule gì?
     A: disjI1 (chứng minh vế trái) HOẶC disjI2 (chứng minh vế phải)
     
     Q: Ta có assumption gì?
     A: a ∧ ¬b
     
     Q: Từ a ∧ ¬b, ta có thể lấy được gì?
     A: Lấy được "a" (bằng conjunct1) hoặc "¬b" (bằng conjunct2)
     
     Q: Cần chứng minh a ∨ b, nên chọn vế nào?
     A: Chọn vế trái (a) vì ta có thể lấy được "a" từ assumption!
  *)
  
  (* BƯỚC 4: Lấy "a" từ assumption "a ∧ ¬b" *)
  from H have left_part: "a" by (rule conjunct1)
  
  (* 
     conjunct1 rule:
     ─────────────
     From: P ∧ Q
     Get: P
  *)
  
  (* BƯỚC 5: Từ "a", chứng minh "a ∨ b" bằng disjI1 *)
  from left_part show "a ∨ b" by (rule disjI1)
  
  (* 
     disjI1 rule:
     ─────────────
     From: P
     Prove: P ∨ Q
  *)
qed

(* ═══════════════════════════════════════════════════════════════════
   PROOF TREE VISUALIZATION:
   
   (a ∧ ¬b) ⟶ a ∨ b           [Goal]
         │
         │ (apply impI)
         ↓
   Assume: a ∧ ¬b
   Prove: a ∨ b               [New Goal]
         │
         │ (extract "a" using conjunct1)
         ↓
   Have: a                    [Intermediate fact]
         │
         │ (apply disjI1)
         ↓
   Proved: a ∨ b              [QED]
   ═══════════════════════════════════════════════════════════════════ *)

section ‹Cách 2: Apply-style (ngắn gọn hơn)›

lemma logic_axiom_1_apply:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  apply (rule impI)      (* Goal: (a ∧ ¬b) ⟹ a ∨ b *)
  apply (erule conjE)    (* Split conjunction, goals: [a, ¬b] ⟹ a ∨ b *)
  apply (rule disjI1)    (* Goal: a (from assumption) *)
  apply assumption       (* Match với assumption "a" *)
  done

(* 
   GIẢI THÍCH erule conjE:
   ─────────────────────────
   - erule = elimination rule + tự động xóa assumption đã dùng
   - conjE = conjunction elimination (split P ∧ Q thành P và Q riêng biệt)
*)

section ‹Cách 3: Ultra-compact (một dòng)›

lemma logic_axiom_1_compact:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  by (rule impI, erule conjE, rule disjI1, assumption)

(* 
   Giải thích:
   - rule impI: assume tiền đề
   - erule conjE: split conjunction
   - rule disjI1: chọn chứng minh vế trái của disjunction
   - assumption: goal match với assumption
*)

section ‹BẢNG TRA CỨU: Câu hỏi → Rule›

(*
  ╔═══════════════════════════════════════════════════════════════════╗
  ║  CÂU HỎI                          │  RULE                         ║
  ╠═══════════════════════════════════════════════════════════════════╣
  ║  Goal dạng P ⟶ Q?                │  impI                         ║
  ║  Goal dạng P ∧ Q?                │  conjI                        ║
  ║  Goal dạng P ∨ Q?                │  disjI1 hoặc disjI2          ║
  ║  Goal dạng ¬P?                   │  notI                         ║
  ║  Goal dạng P = Q?                │  iffI                         ║
  ║─────────────────────────────────────────────────────────────────║
  ║  Có assumption P ∧ Q, lấy P?     │  conjunct1                    ║
  ║  Có assumption P ∧ Q, lấy Q?     │  conjunct2                    ║
  ║  Có assumption P ∧ Q, split?     │  conjE (dùng erule)          ║
  ║  Có assumption P ∨ Q?            │  disjE (case analysis)       ║
  ║  Có assumption P ⟶ Q và P?      │  mp (modus ponens)           ║
  ║  Có assumption ¬P và P?          │  notE (contradiction)        ║
  ╚═══════════════════════════════════════════════════════════════════╝
*)

end
