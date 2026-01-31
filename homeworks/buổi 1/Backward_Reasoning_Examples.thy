theory Backward_Reasoning_Examples
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   BACKWARD REASONING - Không cần sledgehammer!
   
   Phương pháp: Nhìn Goal → Chọn Rule → Xem Goal mới → Lặp lại
   ═══════════════════════════════════════════════════════════════════ *)

section ‹Ví dụ 1: (a ∧ ¬b) ⟶ a ∨ b - CHI TIẾT TỪNG BƯỚC›

subsection ‹Bước 0: Phân tích ban đầu›

(*
  GOAL: (a ∧ ¬b) ⟶ a ∨ b
  
  Q1: Goal có dạng gì?
  A1: P ⟶ Q (implication)
  
  Q2: Cần rule gì?
  A2: impI (Implication Introduction)
*)

subsection ‹Bước 1: Apply impI›

lemma step1:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  apply (rule impI)
  (*
    OUTPUT WINDOW:
    proof (prove)
    goal (1 subgoal):
     1. a ∧ ¬b ⟹ a ∨ b
    
    PHÂN TÍCH:
    - Assumption: a ∧ ¬b
    - Goal: a ∨ b
  *)
  oops

subsection ‹Bước 2: Apply disjI1›

lemma step2:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  apply (rule impI)
  apply (rule disjI1)
  (*
    OUTPUT WINDOW:
    goal (1 subgoal):
     1. a ∧ ¬b ⟹ a
    
    PHÂN TÍCH:
    - Assumption: a ∧ ¬b
    - Goal: a (đơn giản hơn!)
    - Làm sao lấy "a" từ "a ∧ ¬b"? → conjunct1
  *)
  oops

subsection ‹Bước 3: Lấy a từ conjunction›

lemma step3:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  apply (rule impI)
  apply (rule disjI1)
  apply (erule conjE)
  (*
    OUTPUT WINDOW:
    goal (1 subgoal):
     1. [a; ¬b] ⟹ a
    
    PHÂN TÍCH:
    - Assumptions: a, ¬b (đã split!)
    - Goal: a
    - Goal match với assumption → dùng "assumption"
  *)
  apply assumption
  done

subsection ‹Proof hoàn chỉnh - Apply style›

lemma example1_apply:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  apply (rule impI)
  apply (rule disjI1)
  apply (erule conjE)
  apply assumption
  done

subsection ‹Proof hoàn chỉnh - Isar style›

lemma example1_isar:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
proof (rule impI)
  assume "a ∧ ¬b"
  from ‹a ∧ ¬b› have "a" by (rule conjunct1)
  from ‹a› show "a ∨ b" by (rule disjI1)
qed

section ‹Ví dụ 2: a ∨ b ⟶ b ∨ a - Case Analysis›

subsection ‹Phân tích›

(*
  GOAL: a ∨ b ⟶ b ∨ a
  
  Bước 1: Goal dạng P⟶Q → impI
    → New goal: a∨b ⟹ b∨a
  
  Bước 2: Assumption dạng P∨Q → Cần case split (disjE)
    → Case 1: a ⟹ b∨a
    → Case 2: b ⟹ b∨a
  
  Bước 3:
    - Case 1: Từ a, prove b∨a → disjI2 (vế phải)
    - Case 2: Từ b, prove b∨a → disjI1 (vế trái)
*)

subsection ‹Apply style›

lemma example2_apply:
  shows "a ∨ b ⟶ b ∨ a"
  apply (rule impI)
  (* Goal: a∨b ⟹ b∨a *)
  
  apply (erule disjE)
  (* Split thành 2 cases:
     Case 1: a ⟹ b∨a
     Case 2: b ⟹ b∨a *)
  
  (* Case 1 *)
   apply (rule disjI2)
   apply assumption
  
  (* Case 2 *)
  apply (rule disjI1)
  apply assumption
  done

subsection ‹Isar style›

lemma example2_isar:
  shows "a ∨ b ⟶ b ∨ a"
proof (rule impI)
  assume "a ∨ b"
  from ‹a ∨ b› show "b ∨ a"
  proof (rule disjE)
    assume "a"
    from ‹a› show "b ∨ a" by (rule disjI2)
  next
    assume "b"
    from ‹b› show "b ∨ a" by (rule disjI1)
  qed
qed

section ‹Ví dụ 3: (a ∧ ¬a) ⟶ b - Contradiction›

subsection ‹Phân tích›

(*
  GOAL: (a ∧ ¬a) ⟶ b
  
  Bước 1: Goal dạng P⟶Q → impI
    → New goal: a∧¬a ⟹ b
  
  Bước 2: Có assumption a∧¬a (mâu thuẫn!)
    → Lấy a (conjunct1)
    → Lấy ¬a (conjunct2)
  
  Bước 3: Từ a và ¬a → False (notE)
  
  Bước 4: Từ False → b (FalseE - ex falso quodlibet)
*)

subsection ‹Apply style›

lemma example3_apply:
  shows "(a ∧ ¬a) ⟶ b"
  apply (rule impI)
  apply (erule conjE)
  (* Bây giờ có: a, ¬a *)
  apply (erule notE)
  (* False! Từ False suy ra mọi thứ *)
  apply assumption
  done

subsection ‹Isar style - Cách 1: Chi tiết›

lemma example3_isar_detailed:
  shows "(a ∧ ¬a) ⟶ b"
proof (rule impI)
  assume "a ∧ ¬a"
  from ‹a ∧ ¬a› have left: "a" by (rule conjunct1)
  from ‹a ∧ ¬a› have right: "¬a" by (rule conjunct2)
  show "b"
  proof -
    from right left have "False" by (rule notE)
    then show "b" by (rule FalseE)
  qed
qed

subsection ‹Isar style - Cách 2: Dùng contradiction›

lemma example3_isar_simple:
  shows "(a ∧ ¬a) ⟶ b"
proof (rule impI)
  assume "a ∧ ¬a"
  then show "b" by contradiction
qed

section ‹Ví dụ 4: a ∧ b ⟶ b ∧ a - Commutativity›

subsection ‹Phân tích›

(*
  GOAL: a∧b ⟶ b∧a
  
  Bước 1: impI
    → Goal: a∧b ⟹ b∧a
  
  Bước 2: Goal dạng P∧Q → conjI
    → Split thành 2 subgoals:
      Subgoal 1: a∧b ⟹ b
      Subgoal 2: a∧b ⟹ a
  
  Bước 3: 
    - Subgoal 1: Lấy b từ a∧b (conjunct2)
    - Subgoal 2: Lấy a từ a∧b (conjunct1)
*)

lemma example4:
  shows "a ∧ b ⟶ b ∧ a"
proof (rule impI)
  assume "a ∧ b"
  show "b ∧ a"
  proof (rule conjI)
    from ‹a ∧ b› show "b" by (rule conjunct2)
  next
    from ‹a ∧ b› show "a" by (rule conjunct1)
  qed
qed

section ‹Ví dụ 5: a ∧ (b ∨ c) ⟶ (a ∧ b) ∨ (a ∧ c) - Distribution›

subsection ‹Phân tích phức tạp›

(*
  GOAL: a ∧ (b ∨ c) ⟶ (a ∧ b) ∨ (a ∧ c)
  
  Bước 1: impI
  Bước 2: Split assumption a∧(b∨c) → có a và (b∨c)
  Bước 3: Case split trên b∨c
    Case 1: b → Chứng minh (a∧b)∨(a∧c) bằng disjI1
    Case 2: c → Chứng minh (a∧b)∨(a∧c) bằng disjI2
*)

lemma example5:
  shows "a ∧ (b ∨ c) ⟶ (a ∧ b) ∨ (a ∧ c)"
proof (rule impI)
  assume "a ∧ (b ∨ c)"
  from ‹a ∧ (b ∨ c)› have a_fact: "a" by (rule conjunct1)
  from ‹a ∧ (b ∨ c)› have "b ∨ c" by (rule conjunct2)
  from ‹b ∨ c› show "(a ∧ b) ∨ (a ∧ c)"
  proof (rule disjE)
    assume "b"
    from a_fact ‹b› have "a ∧ b" by (rule conjI)
    from ‹a ∧ b› show "(a ∧ b) ∨ (a ∧ c)" by (rule disjI1)
  next
    assume "c"
    from a_fact ‹c› have "a ∧ c" by (rule conjI)
    from ‹a ∧ c› show "(a ∧ b) ∨ (a ∧ c)" by (rule disjI2)
  qed
qed

section ‹TÓM TẮT WORKFLOW›

(*
  ══════════════════════════════════════════════════════════
  QUY TRÌNH BACKWARD REASONING:
  ══════════════════════════════════════════════════════════
  
  1. Đọc GOAL
  2. Tự hỏi: "Goal có dạng gì?"
     - P ⟶ Q? → impI
     - P ∧ Q? → conjI
     - P ∨ Q? → disjI1 hoặc disjI2
     - ¬P? → notI
     - P = Q? → iffI
  
  3. Apply rule → Xem OUTPUT WINDOW
  4. Goal mới là gì? Có assumptions gì?
  5. Lặp lại từ bước 2
  6. Cho đến khi: Goal = Assumption (trivial)
  
  ══════════════════════════════════════════════════════════
*)

end
