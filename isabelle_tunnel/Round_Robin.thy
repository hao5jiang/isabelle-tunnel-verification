theory Round_Robin
  imports Tunnel_Liveness
begin

text \<open>A deterministic closed-loop scheduler under continuous demand.
  Slots alternate between A and B. One slot completes at most one enabled
  protocol action. Outside trains request again on their next slot. A
  blocked slot is idle. This is a discrete model, not a real-time bound.\<close>

fun other where "other A = B" | "other B = A"

definition dispatch :: "train \<Rightarrow> state \<Rightarrow> state" where
  "dispatch i s = (case loc s i of
     Outside \<Rightarrow> s\<lparr>loc := (loc s)(i := Waiting)\<rparr>
   | Waiting \<Rightarrow> (if permit s i then s\<lparr>loc := (loc s)(i := Inside)\<rparr>
       else if \<not> permit s A \<and> \<not> permit s B
       then s\<lparr>permit := (permit s)(i := True)\<rparr> else s)
   | Inside \<Rightarrow> s\<lparr>loc := (loc s)(i := Outside),
       permit := (permit s)(i := False)\<rparr>)"

definition tick :: "state \<times> train \<Rightarrow> state \<times> train" where
  "tick c = (dispatch (snd c) (fst c), other (snd c))"

fun rr_run :: "nat \<Rightarrow> state \<times> train \<Rightarrow> state \<times> train" where
  "rr_run 0 c = c"
| "rr_run (Suc n) c = tick (rr_run n c)"

lemma train_all: "(\<forall>i::train. P i) \<longleftrightarrow> P A \<and> P B"
  by (metis train.exhaust)

theorem dispatch_refines: "step s (dispatch i s)"
proof (cases "loc s i")
  case Outside
  show ?thesis using step.request[OF Outside] by (simp add: dispatch_def Outside)
next
  case Inside
  show ?thesis using step.leave[OF Inside] by (simp add: dispatch_def Inside)
next
  case Waiting
  show ?thesis
  proof (cases "permit s i")
    case True
    show ?thesis using step.enter[OF Waiting True]
      by (simp add: dispatch_def Waiting True)
  next
    case False
    show ?thesis
    proof (cases "\<not> permit s A \<and> \<not> permit s B")
      case True
      then have all: "\<forall>j. \<not> permit s j" by (simp add: train_all)
      show ?thesis using step.grant[OF Waiting all]
        by (simp add: dispatch_def Waiting False True)
    next
      case no: False
      show ?thesis by (simp add: dispatch_def Waiting False no step.idle)
    qed
  qed
qed

theorem tick_refines: "step (fst c) (fst (tick c))"
  by (simp add: tick_def dispatch_refines)

theorem rr_reachable:
  assumes "reachable (fst c)"
  shows "reachable (fst (rr_run n c))"
  using assms by (induction n) (auto intro: reachable.advance tick_refines)

theorem rr_safe:
  "reachable (fst c) \<Longrightarrow> safe (fst (rr_run n c))"
  using rr_reachable mutual_exclusion by blast

theorem rr_execution:
  "execution (fst c) (\<lambda>n. fst (rr_run n c))"
  by (simp add: execution_def tick_refines)

lemma rr_add: "rr_run (n + k) c = rr_run k (rr_run n c)"
  by (induction k) simp_all

definition pack :: "position \<Rightarrow> position \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> state" where
  "pack a b pa pb = \<lparr>loc = (\<lambda>i. case i of A \<Rightarrow> a | B \<Rightarrow> b),
    permit = (\<lambda>i. case i of A \<Rightarrow> pa | B \<Rightarrow> pb)\<rparr>"

lemma pack_state:
  "pack (loc s A) (loc s B) (permit s A) (permit s B) = s"
proof -
  have L: "(\<lambda>i. case i of A \<Rightarrow> loc s A | B \<Rightarrow> loc s B) = loc s"
    by (rule ext; rename_tac i; case_tac i) simp_all
  have P: "(\<lambda>i. case i of A \<Rightarrow> permit s A | B \<Rightarrow> permit s B) = permit s"
    by (rule ext; rename_tac i; case_tac i) simp_all
  show ?thesis by (simp add: pack_def L P)
qed

definition entered8 where
  "entered8 c i \<longleftrightarrow>
    loc (fst (rr_run 1 c)) i = Inside \<or>
    loc (fst (rr_run 2 c)) i = Inside \<or>
    loc (fst (rr_run 3 c)) i = Inside \<or>
    loc (fst (rr_run 4 c)) i = Inside \<or>
    loc (fst (rr_run 5 c)) i = Inside \<or>
    loc (fst (rr_run 6 c)) i = Inside \<or>
    loc (fst (rr_run 7 c)) i = Inside \<or>
    loc (fst (rr_run 8 c)) i = Inside"

lemma finite_bound_check:
  "invariant (pack a b pa pb) \<Longrightarrow> permit_live (pack a b pa pb) \<Longrightarrow>
   loc (pack a b pa pb) i = Waiting \<Longrightarrow> entered8 (pack a b pa pb, turn) i"
  by (cases a; cases b; cases pa; cases pb; cases i; cases turn)
     (simp_all add: invariant_def permit_live_def train_all pack_def entered8_def
       tick_def dispatch_def numeral_eq_Suc)

lemma entered8_bound:
  assumes "entered8 c i"
  shows "\<exists>k. 0 < k \<and> k \<le> 8 \<and> loc (fst (rr_run k c)) i = Inside"
  using assms unfolding entered8_def
  apply (elim disjE)
  subgoal by (intro exI[of _ 1]) simp
  subgoal by (intro exI[of _ 2]) simp
  subgoal by (intro exI[of _ 3]) simp
  subgoal by (intro exI[of _ 4]) simp
  subgoal by (intro exI[of _ 5]) simp
  subgoal by (intro exI[of _ 6]) simp
  subgoal by (intro exI[of _ 7]) simp
  subgoal by (intro exI[of _ 8]) simp
  done

theorem rr_wait_bound:
  assumes "reachable s" "loc s i = Waiting"
  shows "\<exists>k. 0 < k \<and> k \<le> 8 \<and> loc (fst (rr_run k (s,turn))) i = Inside"
proof -
  have inv: "invariant s" by (rule reachable_invariant[OF assms(1)])
  have live: "permit_live s" by (rule reachable_permit_live[OF assms(1)])
  have "entered8 (s,turn) i"
    using finite_bound_check[of "loc s A" "loc s B" "permit s A" "permit s B" i turn]
      inv live assms(2) by (simp add: pack_state)
  then show ?thesis by (rule entered8_bound)
qed

theorem rr_every_request_served:
  assumes "reachable (fst c)" "loc (fst (rr_run n c)) i = Waiting"
  shows "\<exists>k. 0 < k \<and> k \<le> 8 \<and> loc (fst (rr_run (n+k) c)) i = Inside"
proof -
  have r: "reachable (fst (rr_run n c))" by (rule rr_reachable[OF assms(1)])
  show ?thesis using rr_wait_bound[OF r assms(2), of "snd (rr_run n c)"]
    by (simp add: rr_add)
qed

text \<open>Both trains are waiting with no permissions. B gets the first
  slot. A enters at slot eight; thus the universal bound cannot be seven.\<close>

lemma tight_start_reachable: "reachable s2"
  by (rule reachable.advance[OF reachable.advance[OF reachable.initial edge01] edge12])

theorem eighth_slot_entry:
  "loc (fst (rr_run 8 (s2,B))) A = Inside"
  by (simp add: states tick_def dispatch_def numeral_eq_Suc)

theorem no_entry_first_seven:
  "k < 8 \<Longrightarrow> loc (fst (rr_run k (s2,B))) A \<noteq> Inside"
proof -
  assume "k < 8"
  then have "k=0 \<or> k=1 \<or> k=2 \<or> k=3 \<or> k=4 \<or> k=5 \<or> k=6 \<or> k=7"
    by arith
  then show ?thesis by (auto simp: states tick_def dispatch_def numeral_eq_Suc)
qed

end
