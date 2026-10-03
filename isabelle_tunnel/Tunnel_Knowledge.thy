theory Tunnel_Knowledge
  imports Main
begin

text \<open>
  A small interleaving model inspired by Handbook of Logics for Knowledge
  and Belief (2014 draft), section 8.2.4, pp. 354-355, property (8.3).
  The transition system below is our explicit model, not a transcription
  of an implementation supplied by the book. Grants are persistent local
  permissions. Exit atomically clears a permission. No message loss,
  fairness or physical timing assumptions are encoded.
\<close>

datatype train = A | B
datatype position = Outside | Waiting | Inside

record state =
  loc :: "train \<Rightarrow> position"
  permit :: "train \<Rightarrow> bool"

definition initial :: state where
  "initial = \<lparr>loc = (\<lambda>_. Outside), permit = (\<lambda>_. False)\<rparr>"

inductive step :: "state \<Rightarrow> state \<Rightarrow> bool" where
  request: "loc s i = Outside \<Longrightarrow>
    step s (s\<lparr>loc := (loc s)(i := Waiting)\<rparr>)"
| grant: "loc s i = Waiting \<Longrightarrow> (\<forall>j. \<not> permit s j) \<Longrightarrow>
    step s (s\<lparr>permit := (permit s)(i := True)\<rparr>)"
| enter: "loc s i = Waiting \<Longrightarrow> permit s i \<Longrightarrow>
    step s (s\<lparr>loc := (loc s)(i := Inside)\<rparr>)"
| leave: "loc s i = Inside \<Longrightarrow>
    step s (s\<lparr>loc := (loc s)(i := Outside),
              permit := (permit s)(i := False)\<rparr>)"
| idle: "step s s"

inductive reachable :: "state \<Rightarrow> bool" where
  initial: "reachable initial"
| advance: "reachable s \<Longrightarrow> step s t \<Longrightarrow> reachable t"

definition invariant :: "state \<Rightarrow> bool" where
  "invariant s \<longleftrightarrow>
    (\<forall>i j. permit s i \<longrightarrow> permit s j \<longrightarrow> i = j) \<and>
    (\<forall>i. loc s i = Inside \<longrightarrow> permit s i)"

definition safe :: "state \<Rightarrow> bool" where
  "safe s \<longleftrightarrow> \<not> (loc s A = Inside \<and> loc s B = Inside)"

lemma initial_invariant: "invariant initial"
  by (simp add: invariant_def initial_def)

lemma step_preserves_invariant:
  assumes "step s t" "invariant s"
  shows "invariant t"
  using assms
  by (cases rule: step.cases) (auto simp: invariant_def)

theorem reachable_invariant:
  assumes "reachable s"
  shows "invariant s"
  using assms
  by (induction rule: reachable.induct)
     (auto intro: initial_invariant step_preserves_invariant)

lemma invariant_excludes_other_train:
  assumes "invariant s" "loc s i = Inside" "i \<noteq> j"
  shows "loc s j \<noteq> Inside"
  using assms unfolding invariant_def by blast

theorem mutual_exclusion:
  assumes "reachable s"
  shows "safe s"
  using reachable_invariant[OF assms]
  unfolding invariant_def safe_def by auto

text \<open>
  Knowledge ranges only over states reachable under this protocol.
  An agent observes its own position, without a clock or perfect recall.
  This is deliberately a coarse observation function. The theorem below
  is the reachable-state form of AG(in_i --> K_i(not in_j)).
\<close>

definition knows :: "train \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool" where
  "knows i P s \<longleftrightarrow>
    (\<forall>t. reachable t \<and> loc t i = loc s i \<longrightarrow> P t)"

lemma knowledge_is_factive:
  assumes "reachable s" "knows i P s"
  shows "P s"
  using assms unfolding knows_def by blast

theorem inside_knows_other_out:
  assumes "reachable s" "loc s i = Inside" "i \<noteq> j"
  shows "knows i (\<lambda>t. loc t j \<noteq> Inside) s"
proof (unfold knows_def, intro allI impI)
  fix t
  assume obs: "reachable t \<and> loc t i = loc s i"
  have inv: "invariant t"
    using obs reachable_invariant by blast
  have inside: "loc t i = Inside"
    using obs assms by simp
  show "loc t j \<noteq> Inside"
    using invariant_excludes_other_train[OF inv inside assms(3)] .
qed

text \<open>
  Fault: issue a permission whenever nobody is currently inside, ignoring
  outstanding permissions. Both grants can occur before either entry.
\<close>

inductive bad_step :: "state \<Rightarrow> state \<Rightarrow> bool" where
  normal: "step s t \<Longrightarrow> bad_step s t"
| premature_grant: "loc s i = Waiting \<Longrightarrow>
    (\<forall>j. loc s j \<noteq> Inside) \<Longrightarrow>
    bad_step s (s\<lparr>permit := (permit s)(i := True)\<rparr>)"

inductive bad_reachable :: "state \<Rightarrow> bool" where
  initial: "bad_reachable initial"
| advance: "bad_reachable s \<Longrightarrow> bad_step s t \<Longrightarrow> bad_reachable t"

definition s1 where "s1 = initial\<lparr>loc := (loc initial)(A := Waiting)\<rparr>"
definition s2 where "s2 = s1\<lparr>loc := (loc s1)(B := Waiting)\<rparr>"
definition s3 where "s3 = s2\<lparr>permit := (permit s2)(A := True)\<rparr>"
definition s4 where "s4 = s3\<lparr>permit := (permit s3)(B := True)\<rparr>"
definition s5 where "s5 = s4\<lparr>loc := (loc s4)(A := Inside)\<rparr>"
definition s6 where "s6 = s5\<lparr>loc := (loc s5)(B := Inside)\<rparr>"

lemmas states = s1_def s2_def s3_def s4_def s5_def s6_def initial_def

lemma edge01: "step initial s1"
  unfolding s1_def by (rule step.request) (simp add: initial_def)

lemma edge12: "step s1 s2"
  unfolding s2_def by (rule step.request) (simp add: states)

lemma edge23: "step s2 s3"
  unfolding s3_def by (rule step.grant) (simp_all add: states)

lemma edge34: "bad_step s3 s4"
  unfolding s4_def by (rule bad_step.premature_grant) (simp_all add: states)

lemma edge45: "step s4 s5"
  unfolding s5_def by (rule step.enter) (simp_all add: states)

lemma edge56: "step s5 s6"
  unfolding s6_def by (rule step.enter) (simp_all add: states)

lemma safe_prefix: "reachable s3"
  using reachable.initial edge01 edge12 edge23
  by (meson reachable.advance)

lemma safe_system_rejects_double_permission: "\<not> reachable s4"
proof
  assume "reachable s4"
  then have "invariant s4" by (rule reachable_invariant)
  then have "permit s4 A \<longrightarrow> permit s4 B \<longrightarrow> A = B"
    unfolding invariant_def by blast
  then show False by (simp add: states)
qed

lemma collision_reachable: "bad_reachable s6"
  using bad_reachable.initial edge01 edge12 edge23 edge34 edge45 edge56
  by (meson bad_reachable.advance bad_step.normal)

lemma collision_is_unsafe: "\<not> safe s6"
  by (simp add: safe_def states)

theorem faulty_protocol_counterexample:
  "\<exists>s. bad_reachable s \<and> \<not> safe s"
  using collision_reachable collision_is_unsafe by blast

definition bad_knows :: "train \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool" where
  "bad_knows i P s \<longleftrightarrow>
    (\<forall>t. bad_reachable t \<and> loc t i = loc s i \<longrightarrow> P t)"

theorem faulty_knowledge_counterexample:
  "loc s6 A = Inside \<and> \<not> bad_knows A (\<lambda>t. loc t B \<noteq> Inside) s6"
  using collision_reachable unfolding bad_knows_def
  by (auto simp: states)

end
