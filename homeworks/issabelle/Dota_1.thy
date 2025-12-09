theory Dota_1
  imports Main
begin

(*
- p: worthy of playing DotA 2 (đáng chơi DotA 2)
- w: worthy of watching DotA 2 (đáng xem DotA 2)
- r: worthy of reading articles about DotA 2

Given statements:
  1. \<not>p \<rightarrow> w  (If not worthy of playing, then worthy of watching)
  2. \<not>w \<rightarrow> r  (If not worthy of watching, then worthy of reading)
  3. At most one activity can be done at a time (mutual exclusivity)

a) \<not>r
b) p or w
*)
lemma step_1_portation:
  shows "((\<not>p \<longrightarrow> w) \<and> (\<not>p \<and> \<not>w \<longrightarrow> r) \<and> \<not>(p \<and> w) 
          \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> w))
         \<longleftrightarrow>
         ((\<not>p \<longrightarrow> w) \<and> (\<not>p \<longrightarrow> (\<not>w \<longrightarrow> r)) \<and> \<not>(p \<and> w)
           \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> w))"
  by auto

lemma step_2_distribution:
  shows "((\<not>p \<longrightarrow> w) \<and> (\<not>p \<longrightarrow> (\<not>w \<longrightarrow> r)) \<and> \<not>(p \<and> w)
           \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> w)) 
        \<longleftrightarrow>
          ((\<not>p \<longrightarrow> w) \<and> ((\<not>w \<longrightarrow> r)) \<and> \<not>(p \<and> w)
           \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> w))"
  using step_1_portation by auto

lemma step_3_distribution:
  shows "((\<not>p \<longrightarrow> w) \<and> (\<not>w \<longrightarrow> r)) \<and> \<not>(p \<and> w) 
          \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> w)
        \<longleftrightarrow>        
         ((\<not>p \<longrightarrow> w \<and> (\<not>w \<longrightarrow> r)) \<and> \<not>(p \<and> w)
         \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> w))"
  using step_2_distribution by auto

lemma step_4_use_w_as_context:
  shows "((\<not>p \<longrightarrow> w \<and> (\<not>w \<longrightarrow> r)) \<and> \<not>(p \<and> w)
         \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> w))
         \<longleftrightarrow>
         ((\<not>p \<longrightarrow> w) \<and> ( \<not>p \<and>  \<not>w) \<and> \<not>(p \<and> r) 
        \<and> \<not>(r \<and> w))"
  using step_3_distribution by auto

lemma step_5_double_implication:
  shows "((\<not>p \<longrightarrow> w) \<and> ( \<not>p \<and>  \<not>w) \<and> \<not>(p \<and> r) 
        \<and> \<not>(r \<and> w))
        \<longleftrightarrow>
        ((\<not>p \<longrightarrow> w) \<and> (w \<longrightarrow> \<not> p)  \<and> \<not>(p \<and> r) 
        \<and> \<not>(r \<and> w))"
  using step_4_use_w_as_context by auto

lemma step_6_replace_w_with_not_p:
  shows "((\<not>p \<longrightarrow> w) \<and> (w \<longrightarrow> \<not> p)  \<and> \<not>(p \<and> r) 
        \<and> \<not>(r \<and> w))
      \<longleftrightarrow>
    ((\<not> p = w) \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> \<not>p))"
  using step_5_double_implication by auto

lemma step_7_duality_twice:
  shows "((\<not> p = w) \<and> \<not>(p \<and> r) \<and> \<not>(r \<and> \<not>p)
       \<longleftrightarrow>
       ((\<not> p = w) \<and> (\<not>p \<or> \<not>r) \<and> (\<not>r \<or> p)))"
  using step_6_replace_w_with_not_p by auto

lemma step_8_noncontradiction_identity:
  shows "((\<not> p = w) \<and> (\<not>p \<or> \<not>r) \<and> (\<not>r \<or> p))
      \<longleftrightarrow>
       ((p \<noteq> w) \<and> (\<not>r \<or> (\<not>p \<and> p)))"
  using step_7_duality_twice by auto

lemma step_9_speicaialize:
  shows "((p \<noteq> w) \<and> (\<not>r \<or> (\<not>p \<and> p)))
        \<longleftrightarrow>
          ((p \<noteq> w) \<and> \<not> r)"
  using step_8_noncontradiction_identity by auto

lemma step_10_finish:
  shows "((p \<noteq> w) \<and> \<not> r) \<longrightarrow>  \<not>r"
  using step_9_speicaialize by auto

end