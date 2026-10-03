theory Tunnel_Liveness
  imports Tunnel_CTLK "HOL-Library.Infinite_Set"
begin

definition permit_live where
  "permit_live s \<longleftrightarrow> (\<forall>i. permit s i \<longrightarrow> loc s i \<noteq> Outside)"

lemma permit_live_step:
  "step s t \<Longrightarrow> permit_live s \<Longrightarrow> permit_live t"
  by (erule step.cases) (auto simp: permit_live_def)

lemma reachable_permit_live:
  "reachable s \<Longrightarrow> permit_live s"
proof (induction rule: reachable.induct)
  case initial
  show ?case by (simp add: initial_def permit_live_def)
next
  case (advance s t)
  show ?case using advance by (meson permit_live_step)
qed

definition free where "free s \<longleftrightarrow> (\<forall>i. \<not> permit s i)"

lemma release_holder:
  assumes "reachable s" "permit s j"
  shows "\<exists>t. step\<^sup>*\<^sup>* s t \<and> free t \<and>
    (\<forall>i. i \<noteq> j \<longrightarrow> loc t i = loc s i)"
proof -
  have live: "loc s j \<noteq> Outside"
    using reachable_permit_live[OF assms(1)] assms(2)
    by (auto simp: permit_live_def)
  have sole: "\<forall>i. i \<noteq> j \<longrightarrow> \<not> permit s i"
    using reachable_invariant[OF assms(1)] assms(2)
    unfolding invariant_def by blast
  show ?thesis
  proof (cases "loc s j")
    case Outside
    with live show ?thesis by simp
  next
    case Inside
    let ?t = "s\<lparr>loc := (loc s)(j := Outside), permit := (permit s)(j := False)\<rparr>"
    have "step s ?t" by (rule step.leave[OF Inside])
    then have "step\<^sup>*\<^sup>* s ?t" by (rule r_into_rtranclp)
    with sole show ?thesis by (intro exI[of _ ?t]) (auto simp: free_def)
  next
    case Waiting
    let ?u = "s\<lparr>loc := (loc s)(j := Inside)\<rparr>"
    let ?t = "?u\<lparr>loc := (loc ?u)(j := Outside), permit := (permit ?u)(j := False)\<rparr>"
    have e1: "step s ?u" by (rule step.enter[OF Waiting assms(2)])
    have e2: "step ?u ?t" by (rule step.leave) simp
    have "step\<^sup>*\<^sup>* s ?t"
      using e1 e2 by (meson r_into_rtranclp rtranclp_trans)
    with sole show ?thesis by (intro exI[of _ ?t]) (auto simp: free_def)
  qed
qed

lemma free_can_enter:
  assumes "free s" "loc s i = Waiting"
  shows "\<exists>t. step\<^sup>*\<^sup>* s t \<and> loc t i = Inside"
proof -
  let ?u = "s\<lparr>permit := (permit s)(i := True)\<rparr>"
  let ?t = "?u\<lparr>loc := (loc ?u)(i := Inside)\<rparr>"
  have e1: "step s ?u" using assms by (intro step.grant) (auto simp: free_def)
  have e2: "step ?u ?t" using assms(2) by (intro step.enter) auto
  have "step\<^sup>*\<^sup>* s ?t"
    using e1 e2 by (meson r_into_rtranclp rtranclp_trans)
  then show ?thesis by (intro exI[of _ ?t]) simp
qed

theorem waiting_has_entry_path:
  assumes "reachable s" "loc s i = Waiting"
  shows "\<exists>t. step\<^sup>*\<^sup>* s t \<and> loc t i = Inside"
proof (cases "permit s i")
  case True
  have "step s (s\<lparr>loc := (loc s)(i := Inside)\<rparr>)"
    by (rule step.enter[OF assms(2) True])
  then show ?thesis using r_into_rtranclp by fastforce
next
  case False
  show ?thesis
  proof (cases "free s")
    case True
    show ?thesis by (rule free_can_enter[OF True assms(2)])
  next
    case False
    then obtain j where p: "permit s j" unfolding free_def by blast
    have ij: "i \<noteq> j" using p \<open>\<not> permit s i\<close> by blast
    obtain u where u: "step\<^sup>*\<^sup>* s u" "free u" "loc u i = loc s i"
      using release_holder[OF assms(1) p] ij by blast
    have uw: "loc u i = Waiting" using u(3) assms(2) by simp
    obtain t where t: "step\<^sup>*\<^sup>* u t" "loc t i = Inside"
      using free_can_enter[OF u(2) uw] by blast
    have "step\<^sup>*\<^sup>* s t" by (rule rtranclp_trans[OF u(1) t(1)])
    with t(2) show ?thesis by blast
  qed
qed

lemma waiting_step:
  "step s t \<Longrightarrow> loc s i = Waiting \<Longrightarrow>
    loc t i = Waiting \<or> loc t i = Inside"
  by (erule step.cases) auto

definition recurrent :: "(nat \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> bool" where
  "recurrent pi s \<longleftrightarrow> (\<forall>n. \<exists>m\<ge>n. pi m = s)"

text \<open>Strong fairness per concrete enabled edge, including idle and
  request edges. This is stronger than weak action fairness. No bound on
  response time is assumed or concluded.\<close>

definition transition_fair where
  "transition_fair pi \<longleftrightarrow>
    (\<forall>s t. recurrent pi s \<and> step s t \<longrightarrow>
      (\<forall>n. \<exists>m\<ge>n. pi m = s \<and> pi (Suc m) = t))"

lemma recurrent_successor:
  assumes "transition_fair pi" "recurrent pi s" "step s t"
  shows "recurrent pi t"
  using assms unfolding transition_fair_def recurrent_def
  by (metis le_SucI)

lemma recurrent_reachable:
  assumes "step\<^sup>*\<^sup>* s t" "transition_fair pi" "recurrent pi s"
  shows "recurrent pi t"
  using assms by (induction rule: rtranclp_induct) (auto intro: recurrent_successor)

lemma recurrent_state_exists:
  fixes pi :: "nat \<Rightarrow> state"
  shows "\<exists>s. recurrent pi s"
proof -
  have fin: "finite (range pi)" by (rule finite_subset[OF subset_UNIV finite_states])
  obtain n where "infinite {m. pi m = pi n}"
    using pigeonhole_infinite[OF infinite_UNIV_nat fin] by auto
  then have "recurrent pi (pi n)"
    by (simp add: recurrent_def infinite_nat_iff_unbounded_le)
  then show ?thesis by blast
qed

theorem fair_eventual_entry:
  assumes run: "execution s pi" and start: "reachable s"
    and fair: "transition_fair pi" and wait: "loc (pi n) i = Waiting"
  shows "\<exists>m\<ge>n. loc (pi m) i = Inside"
proof (rule ccontr)
  assume never: "\<not> (\<exists>m\<ge>n. loc (pi m) i = Inside)"
  have waiting: "loc (pi (n + k)) i = Waiting" for k
  proof (induction k)
    case 0
    show ?case using wait by simp
  next
    case (Suc k)
    have e: "step (pi (n + k)) (pi (Suc (n + k)))"
      using run unfolding execution_def by blast
    show ?case using waiting_step[OF e Suc.IH] never by auto
  qed
  obtain u where rec: "recurrent pi u" using recurrent_state_exists[of pi] by blast
  obtain k where k: "k \<ge> n" "pi k = u" using rec unfolding recurrent_def by blast
  have wu: "loc u i = Waiting" using waiting[of "k-n"] k by simp
  have ru: "reachable u" using execution_reachable[OF start run, of k] k by simp
  obtain t where t: "step\<^sup>*\<^sup>* u t" "loc t i = Inside"
    using waiting_has_entry_path[OF ru wu] by blast
  have "recurrent pi t" by (rule recurrent_reachable[OF t(1) fair rec])
  then obtain m where "m \<ge> n" "pi m = t" unfolding recurrent_def by blast
  with t(2) never show False by blast
qed

theorem fair_safe_service:
  assumes "execution s pi" "reachable s" "transition_fair pi"
  shows "(\<forall>n. safe (pi n)) \<and>
    (\<forall>i n. loc (pi n) i = Waiting \<longrightarrow> (\<exists>m\<ge>n. loc (pi m) i = Inside))"
  using infinite_path_safety[OF assms(2,1)] fair_eventual_entry[OF assms] by blast

theorem endless_wait_is_not_fair:
  "\<not> transition_fair (\<lambda>_. s1)"
proof
  assume f: "transition_fair (\<lambda>_. s1)"
  have r: "reachable s1" by (rule reachable.advance[OF reachable.initial edge01])
  have w: "loc s1 A = Waiting" by (simp add: s1_def)
  have "\<exists>m\<ge>0. loc ((\<lambda>_. s1) m) A = Inside"
    using fair_eventual_entry[where pi="\<lambda>_. s1" and n=0 and i=A,
      OF stuttering_execution r f] w by simp
  with w show False by simp
qed

end
