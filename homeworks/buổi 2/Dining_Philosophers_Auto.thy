theory Dining_Philosophers_Auto
  imports Main
begin

section ‹1. Cấu hình hệ thống (Locale)›

locale Dining =
  fixes N :: nat
  assumes N_gt_1: "N > 1"
begin

type_synonym philosopher = nat
type_synonym state = "philosopher set"

section ‹2. Định nghĩa hàng xóm (Neighbors)›

definition right :: "philosopher ⇒ philosopher" where
  "right i = (i + 1) mod N"

definition left :: "philosopher ⇒ philosopher" where
  "left i = (i + N - 1) mod N"

lemma right_neq_self [simp]:
  assumes "i < N"
  shows "right i ≠ i"
proof -
  have "(i + 1) mod N ≠ i"
  proof
    assume eq: "(i + 1) mod N = i"
    have "i + 1 < N ∨ i + 1 ≥ N" by auto
    then show False
    proof
      assume "i + 1 < N"
      then have "(i + 1) mod N = i + 1" by simp
      with eq have "i + 1 = i" by simp
      thus False by simp
    next
      assume "i + 1 ≥ N"
      with assms have "i + 1 = N" by auto
      then have "(i + 1) mod N = 0" by simp
      with eq have "i = 0" by simp
      with \<open>i + 1 = N\<close> have "N = 1" by simp
      thus False using N_gt_1 by simp
    qed
  qed
  thus ?thesis unfolding right_def by simp
qed

lemma left_neq_self [simp]:
  assumes "i < N"
  shows "left i ≠ i"
proof -
  have "(i + N - 1) mod N = (if i = 0 then N - 1 else i - 1)"
    using assms N_gt_1 by (auto simp: mod_if)
  thus ?thesis unfolding left_def using assms N_gt_1 by auto
qed

lemma left_right_inverse [simp]:
  assumes "i < N"
  shows "right (left i) = i" "left (right i) = i"
  using assms N_gt_1
  unfolding right_def left_def
  by (auto simp: mod_if)

section ‹3. Trạng thái và Bước chuyển (Transitions)›

definition init :: state where
  "init = {}"

inductive transitions :: "state ⇒ state ⇒ bool" where
  exit:
    "i ∈ s ⟹ transitions s (s - {i})"
| enter:
    "⟦ i ∉ s; i < N; right i ∉ s; left i ∉ s ⟧
     ⟹ transitions s (insert i s)"

inductive_set reachable :: "state set" where
  init_reachable:
    "init ∈ reachable"
| step_reachable:
    "⟦ s ∈ reachable; transitions s s' ⟧
     ⟹ s' ∈ reachable"

section ‹4. Tính an toàn (Safety Invariant)›

definition safe :: "state ⇒ bool" where
  "safe s ≡
     (∀i∈s. i < N) ∧
     (∀i∈s. right i ∉ s ∧ left i ∉ s)"

section ‹5. Bảo toàn tính an toàn›

lemma safe_exit:
  assumes "safe s" "i ∈ s"
  shows "safe (s - {i})"
  using assms unfolding safe_def by auto

lemma safe_enter:
  assumes safe_s: "safe s"
      and i_not_s: "i ∉ s" 
      and i_valid: "i < N"
      and Ri_not_s: "right i ∉ s" 
      and Li_not_s: "left i ∉ s"
  shows "safe (insert i s)"
proof -
  have valid: "∀j∈insert i s. j < N"
    using safe_s i_valid unfolding safe_def by auto
  
  have no_conflict: "∀j∈insert i s. right j ∉ insert i s ∧ left j ∉ insert i s"
  proof (intro ballI)
    fix j assume j_in: "j ∈ insert i s" (* pick j from s *)
    show "right j ∉ insert i s ∧ left j ∉ insert i s"
    proof (cases "j = i")
      case True (* case j is i *)
      then have "right j = right i" "left j = left i" by auto
      with Ri_not_s Li_not_s i_valid show ?thesis by auto
    next
      case False (* case j is not i *)
      hence j_s: "j ∈ s" using j_in by simp
      hence j_v: "j < N" using safe_s unfolding safe_def by auto
      from j_s safe_s have Rj_s: "right j ∉ s" and Lj_s: "left j ∉ s" 
        unfolding safe_def by auto
      
      have "right j ≠ i" (* check right neighbor of j is not i *)
      proof
        assume "right j = i"
        hence "j = left i" using j_v left_right_inverse(2) by metis
        thus False using Li_not_s j_s by simp
      qed
      
      have "left j ≠ i" (* check left neighbor of j is not i *)
      proof
        assume "left j = i"
        hence "j = right i" using j_v left_right_inverse(1) by metis
        thus False using Ri_not_s j_s by simp
      qed
      
      from Rj_s Lj_s \<open>right j ≠ i\<close> \<open>left j ≠ i\<close> show ?thesis by auto
    qed
  qed
  
  from valid no_conflict show ?thesis unfolding safe_def by blast
qed

section ‹6. Định lý chính (Safety)›

theorem safety_invariant:
  assumes "s ∈ reachable"
  shows "safe s"
  using assms
proof (induction rule: reachable.induct)
  case init_reachable
  show ?case unfolding safe_def init_def by auto
next
  case (step_reachable s s')
  from \<open>transitions s s'\<close> show ?case
  proof (cases rule: transitions.cases)
    case (exit i)
    thus ?thesis using step_reachable.IH safe_exit by blast
  next
    case (enter i)
    thus ?thesis using step_reachable.IH safe_enter by blast
  qed
qed

end (* locale Dining *)

end