theory Pure_Inference_Rules_Guide
  imports Main
begin

(* ═══════════════════════════════════════════════════════════════════
   HƯỚNG DẪN: Chứng minh chỉ dùng INFERENCE RULES thuần túy
   ═══════════════════════════════════════════════════════════════════ *)

section \<open>1. Logic_Axiom_1: (a ∧ ¬b) ⟶ a ∨ b\<close>

(* ─────────────────────────────────────────────────────────────────── *)
subsection \<open>Cách 1: Structured Isar (KHUYÊN DÙNG)\<close>

lemma logic_axiom_1_isar:
  shows "(a \<and> ~b) \<longrightarrow> a \<or> b"
proof (rule impI)
  assume "a \<and> ~b"
  from \<open>a \<and> ~b\<close> have "a" by (rule conjunct1)
  from \<open>a\<close> show "a \<or> b" by (rule disjI1)
qed

(* ─────────────────────────────────────────────────────────────────── *)
subsection \<open>Cách 2: Apply-style với rules rõ ràng\<close>

lemma logic_axiom_1_apply:
  shows "(a \<and> ~b) \<longrightarrow> a \<or> b"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done

end
