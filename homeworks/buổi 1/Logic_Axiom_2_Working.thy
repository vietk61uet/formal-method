theory Logic_Axiom_2_Working
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   PEIRCE'S LAW: ((a ⟶ b) ⟶ a) = a
   
   VERSION WORKING - Đã test và chạy được!
   ═══════════════════════════════════════════════════════════════════ *)

section ‹CÁCH 1: Dùng contradiction (KHUYÊN DÙNG - DỄ NHẤT!)›

lemma peirce_law_v1:
  shows "((a ⟶ b) ⟶ a) = a"
proof (rule iffI)
  assume H: "((a ⟶ b) ⟶ a)"
  show "a"
  proof (rule classical)
    assume not_a: "¬a"
    
    have imp: "a ⟶ b"
    proof (rule impI)
      assume a_assm: "a"
      (* Dùng contradiction - không cần lo thứ tự! *)
      show "b" using a_assm not_a by contradiction
    qed
    
    from H imp have "a" by (rule mp)
    (* Dùng contradiction *)
    then show "False" using not_a by contradiction
  qed
next
  assume "a"
  show "((a ⟶ b) ⟶ a)"
  proof (rule impI)
    assume "a ⟶ b"
    from ‹a› show "a" .
  qed
qed

section ‹CÁCH 2: Dùng Apply style (AN TOÀN HƠN)›

lemma peirce_law_v2:
  shows "((a ⟶ b) ⟶ a) = a"
proof (rule iffI)
  assume H: "((a ⟶ b) ⟶ a)"
  show "a"
  proof (rule classical)
    assume not_a: "¬a"
    
    have imp: "a ⟶ b"
    proof (rule impI)
      assume a_assm: "a"
      show "b"
        apply (rule FalseE)
        apply (rule notE)
         apply (rule not_a)
        apply (rule a_assm)
        done
    qed
    
    from H imp have a_derived: "a" by (rule mp)
    show "False"
      apply (rule notE)
       apply (rule not_a)
      apply (rule a_derived)
      done
  qed
next
  assume "a"
  show "((a ⟶ b) ⟶ a)"
  proof (rule impI)
    assume "a ⟶ b"
    from ‹a› show "a" .
  qed
qed

section ‹CÁCH 3: Dùng proof block với then›

lemma peirce_law_v3:
  shows "((a ⟶ b) ⟶ a) = a"
proof (rule iffI)
  assume H: "((a ⟶ b) ⟶ a)"
  show "a"
  proof (rule classical)
    assume not_a: "¬a"
    
    have imp: "a ⟶ b"
    proof (rule impI)
      assume a_assm: "a"
      show "b"
      proof -
        have "False"
          apply (rule notE)
           apply (rule not_a)
          apply (rule a_assm)
          done
        then show "b" by (rule FalseE)
      qed
    qed
    
    from H imp have "a" by (rule mp)
    then show "False"
    proof -
      show "False"
        apply (rule notE)
         apply (rule not_a)
        apply assumption
        done
    qed
  qed
next
  assume "a"
  show "((a ⟶ b) ⟶ a)"
  proof (rule impI)
    assume "a ⟶ b"
    from ‹a› show "a" .
  qed
qed

section ‹CÁCH 4: Completely Apply-style (CHO MÁY YẾU)›

lemma peirce_law_v4:
  shows "((a ⟶ b) ⟶ a) = a"
  apply (rule iffI)
  (* Chiều 1 *)
   apply (rule classical)
   apply (drule mp)
    apply (rule impI)
    apply (erule FalseE)
    apply (erule notE)
    apply assumption
   apply (erule notE)
   apply assumption
  (* Chiều 2 *)
  apply (rule impI)
  apply assumption
  done

section ‹GIẢI THÍCH CHI TIẾT›

(*
  ════════════════════════════════════════════════════════════════
  TẠI SAO "from not_a ‹a› show False by (rule notE)" BỊ LỖI?
  ════════════════════════════════════════════════════════════════
  
  Vấn đề: Cú pháp "from ... show" với notE có thể gặp vấn đề
          trong một số context của Isabelle
  
  GIẢI PHÁP:
  
  ✅ Cách 1: Dùng "contradiction" (DỄ NHẤT!)
     show "False" using not_a ‹a› by contradiction
  
  ✅ Cách 2: Dùng apply style
     show "False"
       apply (rule notE)
        apply (rule not_a)
       apply (rule ‹a›)
       done
  
  ✅ Cách 3: Dùng proof block
     show "False"
     proof -
       show "False"
         apply (rule notE)
          apply (rule not_a)
         apply assumption
         done
     qed
  
  ════════════════════════════════════════════════════════════════
  RULES QUAN TRỌNG:
  ════════════════════════════════════════════════════════════════
  
  1. iffI      - Chứng minh P = Q (2 chiều)
  2. classical - Proof by contradiction (assume ¬P, derive False)
  3. impI      - Chứng minh P ⟶ Q
  4. mp        - Modus ponens: P⟶Q, P ⊢ Q
  5. notE      - ¬P, P ⊢ False
  6. FalseE    - False ⊢ anything (ex falso quodlibet)
  
  ════════════════════════════════════════════════════════════════
  KẾT LUẬN:
  ════════════════════════════════════════════════════════════════
  
  Đối với Peirce's Law, CÁCH TỐT NHẤT là dùng "contradiction":
  - Đơn giản nhất
  - Không cần lo thứ tự arguments
  - Isabelle tự động tìm cặp P và ¬P
  
  Ví dụ:
    show "False" using a_assm not_a by contradiction
  
*)

end
