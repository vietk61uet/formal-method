theory Debug_Auto_Example
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   VÍ DỤ THỰC HÀNH: Xem Auto làm gì từng bước
   ═══════════════════════════════════════════════════════════════════ *)

section ‹Ví dụ 1: (a ∧ ¬b) ⟶ a ∨ b›

(* ────────────────────────────────────────────────────────────────── *)
subsection ‹Bước 1: Proof ban đầu với auto›

lemma example_auto:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  by auto

(* ────────────────────────────────────────────────────────────────── *)
subsection ‹Bước 2: Dùng sledgehammer để xem gợi ý›

lemma example_sledgehammer:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  (* Uncomment dòng dưới và chạy: *)
  (* sledgehammer *)
  (* Output sẽ cho: by (metis impI conjunct1 disjI1) *)
  by auto

(* ────────────────────────────────────────────────────────────────── *)
subsection ‹Bước 3: Apply từng bước và XEM OUTPUT WINDOW›

lemma example_step_by_step:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
  (* 
    HƯỚNG DẪN:
    1. Uncomment từng dòng apply theo thứ tự
    2. Sau mỗi dòng, nhìn vào OUTPUT WINDOW (Ctrl+E Ctrl+O)
    3. Xem goal thay đổi thế nào
  *)
  
  (* Apply bước 1: impI *)
  apply (rule impI)
  (* 
    OUTPUT:
    proof (prove)
    goal (1 subgoal):
     1. a ∧ ¬b ⟹ a ∨ b
    
    GIẢI THÍCH: Goal đã thay đổi!
    - Đã assume tiền đề (a ∧ ¬b)
    - Cần chứng minh kết luận (a ∨ b)
  *)
  
  (* Apply bước 2: disjI1 *)
  apply (rule disjI1)
  (* 
    OUTPUT:
    proof (prove)
    goal (1 subgoal):
     1. a ∧ ¬b ⟹ a
    
    GIẢI THÍCH:
    - Chọn chứng minh vế trái của disjunction
    - Bây giờ chỉ cần chứng minh "a"
  *)
  
  (* Apply bước 3: conjunct1 *)
  apply (rule conjunct1)
  (* 
    OUTPUT:
    proof (prove)
    goal (1 subgoal):
     1. a ∧ ¬b ⟹ a ∧ ¬b
    
    GIẢI THÍCH:
    - Cần chứng minh a ∧ ¬b
    - Mà ta đã có a ∧ ¬b trong assumption!
  *)
  
  (* Apply bước 4: assumption *)
  apply assumption
  (* 
    OUTPUT:
    No subgoals!
    
    GIẢI THÍCH: DONE! Goal match với assumption
  *)
  done

(* ────────────────────────────────────────────────────────────────── *)
subsection ‹Bước 4: Convert sang Structured Proof›

lemma example_isar:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
proof (rule impI)
  assume H: "a ∧ ¬b"
  (* Từ assumption H, lấy "a" *)
  from H have "a" by (rule conjunct1)
  (* Từ "a", chứng minh "a ∨ b" *)
  from ‹a› show "a ∨ b" by (rule disjI1)
qed

(* ────────────────────────────────────────────────────────────────── *)
subsection ‹Bước 5: Proof hoàn chỉnh với giải thích›

lemma example_explained:
  shows "(a ∧ ¬b) ⟶ a ∨ b"
proof (rule impI)
  (* Goal ban đầu: (a ∧ ¬b) ⟶ a ∨ b
     Sau impI: Assume (a ∧ ¬b), prove a ∨ b *)
  
  assume conjunction: "a ∧ ¬b"
  (* assumption: a ∧ ¬b
     goal: a ∨ b *)
  
  from conjunction have left_part: "a" by (rule conjunct1)
  (* Lấy phần trái của conjunction
     Bây giờ có: a *)
  
  from left_part show "a ∨ b" by (rule disjI1)
  (* Từ a, chứng minh a ∨ b bằng cách chọn vế trái
     DONE! *)
qed

section ‹Ví dụ 2: a ∨ b ⟶ b ∨ a (Phức tạp hơn)›

lemma swap_disjunction_auto:
  shows "a ∨ b ⟶ b ∨ a"
  by auto

lemma swap_disjunction_manual:
  shows "a ∨ b ⟶ b ∨ a"
  (* Dùng sledgehammer sẽ suggest: *)
  (* by (metis impI disjE disjI1 disjI2) *)
  
  apply (rule impI)
  (* Goal: a ∨ b ⟹ b ∨ a *)
  
  apply (erule disjE)
  (* Split thành 2 cases:
     Case 1: a ⟹ b ∨ a
     Case 2: b ⟹ b ∨ a *)
  
  (* Case 1: Có a, cần chứng minh b ∨ a *)
   apply (rule disjI2)
   apply assumption
  
  (* Case 2: Có b, cần chứng minh b ∨ a *)
  apply (rule disjI1)
  apply assumption
  done

lemma swap_disjunction_isar:
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

section ‹Ví dụ 3: Sử dụng Tracing›

(*
  HƯỚNG DẪN: Enable tracing để xem chi tiết
  
  1. Uncomment dòng declare [[simp_trace=true]]
  2. Chạy lemma
  3. Xem Trace window (View → Dockables → Trace)
  4. Xem từng bước simp làm gì
  5. Uncomment declare [[simp_trace=false]] khi xong
*)

(* declare [[simp_trace=true]] *)

lemma tracing_example:
  shows "(a ∧ b) ∧ c ⟷ a ∧ (b ∧ c)"
  by auto
  (* Trace window sẽ hiển thị các bước simp *)

(* declare [[simp_trace=false]] *)

section ‹Tóm Tắt Workflow›

(*
  WORKFLOW: Từ Auto → Manual
  ═══════════════════════════════════════════════════════════
  
  1️⃣ Viết proof với "by auto"
  
  2️⃣ Chạy sledgehammer
     → Xem output: by (metis rule1 rule2 rule3)
  
  3️⃣ Viết lại với apply-style:
     apply (rule rule1)
     apply (rule rule2)
     ...
  
  4️⃣ Xem Output window sau mỗi apply
     → Hiểu goal thay đổi thế nào
  
  5️⃣ Convert sang Isar structured proof
     → Dễ đọc, dễ hiểu hơn
  
  6️⃣ Thêm comments giải thích
     → Để sau này đọc lại hiểu
  
  ═══════════════════════════════════════════════════════════
*)

end
