theory Case_Analysis_Manual
  imports Main
begin

(* 
   Pure Manual Proof (No simp, No tricks)
   Giải bài toán sử dụng các rule thuần túy. 
   Điểm mấu chốt là cách xử lý sự "lưỡng lự" của Isabelle khi có nhiều giả thiết giống nhau.
*)

lemma case_analysis_manual:
  shows "(a ⟶ b) ∧ (¬a ⟶ b) = b"
  apply (rule iffI)      (* Tách đẳng thức (=) thành 2 điều kiện cần và đủ. *)
  apply (erule conjE)    (* Tách phép hội (∧) trong giả thiết. *)
  apply (cases a)        (* Xét 2 trường hợp: a đúng và a sai. *)
  
  (* Case 1: a = True *)
   apply (erule impE)    (* Isabelle tự chọn giả thiết đầu tiên khớp (a ⟶ b). Vì ta có a, mọi thứ êm đẹp. *)
   apply assumption      (* Chứng minh a *)
   apply assumption      (* Chứng minh b *)
  
  (* Case 2: a = False *)
   (* 
      Vấn đề: Nếu dùng apply (erule impE), máy vẫn ưu tiên cái đầu tiên là a ⟶ b.
      Điều này dẫn đến việc máy bắt bạn chứng minh a (trong khi bạn đang có ¬a) → Lỗi!
   *)
   apply (erule_tac P="¬a" in impE) (* Giải pháp Basic Rule: Chỉ định rõ ràng áp dụng cho ¬a *)
   apply assumption      (* Máy kiểm tra: Có ¬a không? Có! *)
   apply assumption      (* Máy kiểm tra: Đích có phải là b không? Phải! *)

  (* Chiều ngược lại (Reverse) *)
  apply (rule conjI)
  apply (rule impI)
  apply assumption
  apply (rule impI)
  apply assumption       (* Phần này tầm thường (trivial) vì nếu đã có b thì (cái gì ⟶ b) cũng đúng. *)
  done

end
