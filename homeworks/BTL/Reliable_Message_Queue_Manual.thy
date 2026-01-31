theory Reliable_Message_Queue_Manual
  imports Main
begin

type_synonym msg = nat

record mq_state =
  queue    :: "msg list"
  process  :: "msg set"
  retry    :: "msg set"
  finish   :: "msg set"

definition initial_state :: "mq_state" where
  "initial_state = \<lparr> queue = [], process = {}, retry = {}, finish = {} \<rparr>"

definition unique_message_in_queue :: "mq_state \<Rightarrow> bool" where
  "unique_message_in_queue s \<equiv> distinct (queue s)"

definition no_interaction :: "mq_state \<Rightarrow> bool" where
  "no_interaction s \<equiv>
     set (queue s) \<inter> process s = {} \<and> set (queue s) \<inter> retry s   = {} \<and>
     set (queue s) \<inter> finish s  = {} \<and> process s \<inter> retry s       = {} \<and>
     process s \<inter> finish s      = {} \<and> retry s \<inter> finish s        = {}"

definition unique_message :: "mq_state \<Rightarrow> bool" where
  "unique_message s \<equiv> no_interaction s \<and> unique_message_in_queue s"

inductive step :: "mq_state \<Rightarrow> mq_state \<Rightarrow> bool" where
  enqueue:"step s s'"
 if "m \<notin> set (queue s)" and "m \<notin> process s" and "m \<notin> retry s" and "m \<notin> finish s" and "s' = s \<lparr> queue := queue s @ [m] \<rparr>"
| dequeue:"step s s'"
 if "queue s = m # qs" and "s' = s \<lparr> queue := qs,process := process s \<union> {m} \<rparr>"
| success: "step s s'"
 if "m \<in> process s" and "s' = s \<lparr> process := process s - {m}, finish := finish s \<union> {m} \<rparr>"
| fail:"step s s'"
 if "m \<in> process s"and "s' = s \<lparr> process := process s - {m},retry := retry s \<union> {m} \<rparr>"
| retry:"step s s'"
if "m \<in> retry s" and "s' = s \<lparr> retry := retry s - {m}, queue := queue s @ [m] \<rparr>"


(*fun fun_test :: "msg list \<Rightarrow> msg \<Rightarrow> msg list" where
  "fun_test s m =
     (if m \<notin> set s then s @ [m]
      else s)"

value "fun_test []"
value "fun_test [] a::string"*)


inductive reachable :: "mq_state \<Rightarrow> bool" where
  init: "reachable initial_state"
| step: "\<lbrakk> reachable s; step s s' \<rbrakk> \<Longrightarrow> reachable s'"

lemma initial_inv:"unique_message initial_state"
proof -
  have in_queue:
    "unique_message_in_queue initial_state"
    unfolding unique_message_in_queue_def initial_state_def
    by simp

  have interaction:
    "no_interaction initial_state"
    unfolding no_interaction_def initial_state_def
    by simp

  have combine:
    "unique_message initial_state \<longleftrightarrow> no_interaction initial_state \<and> unique_message_in_queue initial_state"
    unfolding unique_message_def by simp

  from in_queue interaction combine show ?thesis
    by auto
qed

lemma step_preserves_inv:
  assumes "step s s'"
      and "unique_message s"
  shows "unique_message s'"
using assms
proof (induction rule: step.induct)                                                                       
  case (enqueue s m)
  then show ?case
    unfolding unique_message_def no_interaction_def unique_message_in_queue_def
    by auto
next
  case (dequeue s qs m)
  then show ?case
    unfolding unique_message_def no_interaction_def unique_message_in_queue_def
    by auto
next
  case (success s m)
  then show ?case
    unfolding unique_message_def no_interaction_def unique_message_in_queue_def
    by auto
next
  case (fail s m)
  then show ?case
    unfolding unique_message_def no_interaction_def unique_message_in_queue_def
    by auto
next
  case (retry s m)
  then show ?case
    unfolding unique_message_def no_interaction_def unique_message_in_queue_def
    by auto
qed

lemma reachable_inv:
  assumes "reachable s"
  shows "unique_message s"
using assms
proof (induction rule: reachable.induct)
  case init
  show ?case
  using initial_inv by simp
next
  case (step s s')
  then show ?case
  using step_preserves_inv by simp
qed

theorem exactly_once:
  assumes "reachable s" 
  shows 
    "m \<in> set (queue s) \<Longrightarrow> m \<notin> process s \<and> m \<notin> retry s \<and> m \<notin> finish s" 
    "m \<in> process s \<Longrightarrow> m \<notin> set (queue s) \<and> m \<notin> retry s \<and> m \<notin> finish s" 
    "m \<in> retry s \<Longrightarrow> m \<notin> set (queue s) \<and> m \<notin> process s \<and> m \<notin> finish s" 
    "m \<in> finish s \<Longrightarrow> m \<notin> set (queue s) \<and> m \<notin> process s \<and> m \<notin> retry s" 
proof -
  from assms 
  have "unique_message s" 
    by (rule reachable_inv) 
  then show 
    "m \<in> set (queue s) \<Longrightarrow> m \<notin> process s \<and> m \<notin> retry s \<and> m \<notin> finish s"
    "m \<in> process s \<Longrightarrow> m \<notin> set (queue s) \<and> m \<notin> retry s \<and> m \<notin> finish s"
    "m \<in> retry s \<Longrightarrow> m \<notin> set (queue s) \<and> m \<notin> process s \<and> m \<notin> finish s"
    "m \<in> finish s \<Longrightarrow> m \<notin> set (queue s) \<and> m \<notin> process s \<and> m \<notin> retry s"
    unfolding unique_message_def no_interaction_def unique_message_in_queue_def
    by auto
qed

end
