theory Logic_Axiom_4
  imports Main
begin

lemma axiom_4:
  shows "(a \<longrightarrow> b) \<or> (b \<longrightarrow> a)"
  apply (cases a)          (* 1. Case analysis on a *)
   apply (rule disjI2)     (* 2. Case a=True: choose b\<longrightarrow>a *)
   apply (rule impI)       (* 3. Assume b, prove a *)
   apply assumption        (* 4. a is in assumptions *)
  apply (rule disjI1)      (* 5. Case a=False: choose a\<longrightarrow>b *)
  apply (rule impI)        (* 6. Assume a, prove b *)
  apply (erule notE)       (* 7. Use contradiction \<not>a and a *)
  apply assumption         (* 8. DONE! *)
  done

end