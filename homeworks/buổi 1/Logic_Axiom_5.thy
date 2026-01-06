theory Logic_Axiom_5
  imports Main
begin

(*\<not>(a \<and> \<not>(a\<or>b))*)

lemma axiom_auto:
  shows "\<not>(a \<and> \<not>(a \<or> b))"
  apply (rule notI)        (* 1. Assume a \<and> \<not>(a \<or> b), prove False *)
  apply (erule conjE)      (* 2. Split into a and \<not>(a \<or> b) *)
  apply (erule notE)       (* 3. Use \<not>(a \<or> b) to create contradiction *)
  apply (rule disjI1)      (* 4. From a, derive a \<or> b *)
  apply assumption         (* 5. DONE! *)
  done

end