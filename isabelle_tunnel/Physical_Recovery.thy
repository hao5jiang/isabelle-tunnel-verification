theory Physical_Recovery
  imports Physical_Controller
begin

fun run_system where
  "run_system [] s = s"
| "run_system (e#es) s = run_system es (system_react e s)"

lemma run_system_valid:
  "physical_valid s \<Longrightarrow> physical_valid (run_system es s)"
  by (induction es arbitrary: s; simp only: run_system.simps; blast intro: physical_step_valid)

definition recovery_events where
  "recovery_events s = (case stage (core (machine s)) of
    Entering i \<Rightarrow> [PlantEnter i, SenseEntry i,
      Receive (era s) (EnterAck i (generation (machine s)))]
  | Leaving i \<Rightarrow> [PlantLeave i, SenseExit i,
      Receive (era s) (LeaveAck i (generation (machine s)))]
  | _ \<Rightarrow> [SystemPoll])"

definition recovery_round where
  "recovery_round s = run_system (recovery_events s) s"

lemma recovery_round_valid:
  "physical_valid s \<Longrightarrow> physical_valid (recovery_round s)"
  unfolding recovery_round_def by (rule run_system_valid)

theorem recovery_round_refines:
  "core (machine (recovery_round s)) =
    react (trigger (stage (core (machine s)))) (core (machine s))"
  by (cases "stage (core (machine s))")
    (simp_all add: recovery_round_def recovery_events_def numbered_react_def Let_def)

theorem recovery_round_keeps_era: "era (recovery_round s) = era s"
  by (cases "stage (core (machine s))")
    (simp_all add: recovery_round_def recovery_events_def)

text \<open>The recovery policy completes physical movement, samples a truthful
  acknowledgement in the current era, and delivers it. It is a constructive
  cooperative continuation, not a guarantee about an unresponsive device.\<close>

fun recovery_run where
  "recovery_run s 0 = s"
| "recovery_run s (Suc n) = recovery_round (recovery_run s n)"

lemma recovery_run_valid:
  "physical_valid s \<Longrightarrow> physical_valid (recovery_run s n)"
  by (induction n; simp only: recovery_run.simps; blast intro: recovery_round_valid)

lemma recovery_core_valid:
  "physical_valid s \<Longrightarrow> valid (core (machine (recovery_run s n)))"
  using recovery_run_valid[of s n] by (simp add: physical_valid_def)

lemma valid_state_no_collision:
  "physical_valid s \<Longrightarrow> \<not> (in_zone s A \<and> in_zone s B)"
  by (cases "stage (core (machine s))")
    (auto simp: physical_valid_def valid_def train_all)

theorem recovery_intermediate_safe:
  assumes "physical_valid s"
  shows "let t = run_system (take j (recovery_events (recovery_run s n))) (recovery_run s n)
    in \<not> (in_zone t A \<and> in_zone t B)"
  unfolding Let_def
  by (rule valid_state_no_collision; rule run_system_valid;
    rule recovery_run_valid; rule assms)

lemma recovery_served_mono:
  "mono (\<lambda>n. served (core (machine (recovery_run s n))) i)"
  by (simp only: mono_iff_le_Suc recovery_run.simps recovery_round_refines;
    blast intro: served_mono_step)

lemma recovery_received_mono:
  "mono (\<lambda>n. received (core (machine (recovery_run s n))) i)"
  by (simp only: mono_iff_le_Suc recovery_run.simps recovery_round_refines;
    blast intro: received_mono_step)

theorem recovery_next_service:
  assumes init: "physical_valid s"
    and queued: "pending (core (machine (recovery_run s n))) i > 0"
  shows "\<exists>m\<ge>n. served (core (machine (recovery_run s m))) i >
    served (core (machine (recovery_run s n))) i"
proof (rule ccontr)
  let ?c = "\<lambda>k. core (machine (recovery_run s k))"
  assume never: "\<not> (\<exists>m\<ge>n. served (?c m) i > served (?c n) i)"
  have same: "served (?c m) i = served (?c n) i" if "m\<ge>n" for m
    using monoD[OF recovery_served_mono[where s=s and i=i] that] never that by auto
  have eqstep: "served (react (trigger (stage (?c m))) (?c m)) i = served (?c m) i"
    if "m\<ge>n" for m
    using same[OF that] same[of "Suc m"] that
    by (simp only: recovery_run.simps recovery_round_refines; auto)
  have pm: "mono (\<lambda>k. pending (?c (n+k)) i)"
    unfolding mono_iff_le_Suc
  proof
    fix k
    have ge: "n+k\<ge>n" by simp
    show "pending (?c (n+k)) i \<le> pending (?c (n+Suc k)) i"
      using pending_persists[OF recovery_core_valid[OF init] eqstep[OF ge]]
      by (simp only: add_Suc_right recovery_run.simps recovery_round_refines)
  qed
  have positive: "pending (?c m) i>0" if "m\<ge>n" for m
    using monoD[OF pm, of 0 "m-n"] queued that by simp
  have ex: "\<exists>r::nat. \<exists>k\<ge>n. rank i (?c k)=r" by blast
  obtain r where witness: "\<exists>k\<ge>n. rank i (?c k)=r"
    and least: "\<forall>v<r. \<not> (\<exists>k\<ge>n. rank i (?c k)=v)"
    using iffD1[OF exists_least_iff ex] by blast
  obtain k where k: "k\<ge>n" "rank i (?c k)=r" using witness by blast
  have decrease: "rank i (?c (Suc k)) < rank i (?c k)"
    using trigger_progress[OF recovery_core_valid[OF init] positive[OF k(1)] eqstep[OF k(1)]]
    by (simp only: recovery_run.simps recovery_round_refines)
  have less: "rank i (?c (Suc k)) < r" using decrease by (simp only: k(2))
  have next_ge: "Suc k\<ge>n" using k(1) by simp
  show False using least less next_ge by blast
qed

theorem recovery_every_ticket_served:
  assumes init: "physical_valid s"
    and admitted: "target \<le> received (core (machine (recovery_run s n))) i"
  shows "\<exists>m\<ge>n. target \<le> served (core (machine (recovery_run s m))) i"
  using admitted
proof (induction target arbitrary: n)
  case 0
  show ?case by auto
next
  case (Suc target)
  let ?c = "\<lambda>k. core (machine (recovery_run s k))"
  obtain k where k: "k\<ge>n" "target \<le> served (?c k) i"
    using Suc.IH[of n] Suc.prems by auto
  show ?case
  proof (cases "Suc target \<le> served (?c k) i")
    case True
    with k(1) show ?thesis by blast
  next
    case False
    have count_eq: "served (?c k) i=target" using k(2) False by simp
    have rec: "Suc target \<le> received (?c k) i"
      using monoD[OF recovery_received_mono[where s=s and i=i] k(1)] Suc.prems by simp
    have pending: "pending (?c k) i>0"
      using recovery_core_valid[OF init, of k] rec count_eq
      by (auto simp: valid_def)
    obtain m where m: "m\<ge>k" "served (?c m) i > served (?c k) i"
      using recovery_next_service[OF init pending] by blast
    have "m\<ge>n" using m(1) k(1) by simp
    with m(2) count_eq show ?thesis by auto
  qed
qed

theorem restart_has_service_continuation:
  assumes "physical_valid s" "target \<le> received (core (machine s)) i"
  shows "\<exists>m. target \<le> served (core (machine (recovery_run (system_react Restart s) m))) i"
  using recovery_every_ticket_served[OF physical_restart_valid[OF assms(1)], of target 0 i] assms(2)
  by simp

definition a_leaving where
  "a_leaving = run_system [SystemRequest A, SystemPoll, PlantEnter A, SenseEntry A,
    Receive 0 (EnterAck A 1), SystemPoll] system_boot"

lemma a_leaving_valid: "physical_valid a_leaving"
  unfolding a_leaving_def by (rule run_system_valid[OF physical_boot_valid])

lemma a_leaving_facts:
  "stage (core (machine a_leaving))=Leaving A \<and> in_zone a_leaving A \<and>
    generation (machine a_leaving)=1 \<and> era a_leaving=0"
  by (simp add: a_leaving_def system_boot_def numbered_boot_def boot_def
    numbered_react_def Let_def grant_to_def)

theorem invented_exit_is_blocked:
  "system_react (Receive 0 (LeaveAck A 1)) a_leaving = a_leaving"
  by (simp add: a_leaving_def system_boot_def numbered_boot_def boot_def
    numbered_react_def Let_def grant_to_def)

definition bypassed_exit where
  "bypassed_exit = a_leaving\<lparr>machine:=numbered_react (LeaveAck A 1) (machine a_leaving)\<rparr>"

theorem bypassed_provenance_can_collide:
  "let s = run_system [SystemRequest B, SystemPoll, PlantEnter B] bypassed_exit
   in in_zone s A \<and> in_zone s B"
  by (simp add: bypassed_exit_def a_leaving_def system_boot_def numbered_boot_def boot_def
    numbered_react_def Let_def grant_to_def)

theorem erased_checkpoint_loses_coverage:
  "let s = a_leaving\<lparr>machine:=numbered_boot, era:=Suc (era a_leaving)\<rparr>
   in in_zone s A \<and> \<not> zone (core (machine s)) A"
  using a_leaving_facts by (simp add: Let_def numbered_boot_def boot_def)

theorem recovery_after_active_restart:
  "let s = run_system [PlantLeave A, SenseExit A, Receive 1 (LeaveAck A 1)]
    (system_react Restart a_leaving)
   in stage (core (machine s))=Ready \<and> \<not> in_zone s A \<and> \<not> in_zone s B"
  by (simp add: a_leaving_def system_boot_def numbered_boot_def boot_def
    numbered_react_def Let_def grant_to_def)

end
