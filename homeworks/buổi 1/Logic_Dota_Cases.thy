theory Logic_Dota_Cases
  imports Main
begin

(* 
  - p: play dota
  - w: watch dota
  - r: read dota
*)

locale dota_logic =
  fixes p w r :: bool
  assumes h1: "\<not>p \<longrightarrow> w"
      and h2: "\<not>w \<longrightarrow> r"
      and excl_pw: "\<not>(p \<and> w)"
      and excl_pr: "\<not>(p \<and> r)"
      and excl_wr: "\<not>(w \<and> r)"
begin

lemma problem_1_not_r: "\<not>r"
proof (rule notI)
  assume "r"
  show "False"
  proof (cases w)
    assume "w"
    from excl_wr \<open>w\<close> \<open>r\<close> show "False" by auto
  next
    assume "\<not>w"
    have "p"
    proof (rule ccontr)
      assume "\<not>p"
      from h1 this have "w" by (rule mp)
      with `\<not>w` show "False" by contradiction
    qed
    from excl_pr `p` `r` show "False" by auto
  qed
qed

lemma problem_2_is_watching: "w"
proof (rule ccontr)
  assume "\<not>w"
  from h2 `\<not>w` have "r" by (rule mp)
  with problem_1_not_r show "False" by contradiction
qed

end

end
