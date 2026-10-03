theory Bounded_Identifiers
  imports Physical_Recovery
begin

text \<open>Only identifiers are bounded. Request counters and the provenance
  history remain mathematical unbounded objects. Locking disables controller
  processing, not previously authorized plant motion. It is not an emergency
  brake, nor a proof of successful recovery after an actual power failure.\<close>

record bounded_system =
  system :: physical_system
  locked :: bool

fun plant_event where
  "plant_event (PlantEnter i) = True"
| "plant_event (PlantLeave i) = True"
| "plant_event _ = False"

definition limit_guard where
  "limit_guard G E e s \<longleftrightarrow>
    (e=Restart \<and> E\<le>era s) \<or>
    (e=SystemPoll \<and> stage (core (machine s))=Ready \<and> G\<le>generation (machine s))"

definition bounded_react where
  "bounded_react G E e b =
    (if locked b then
      (if plant_event e then b\<lparr>system:=system_react e (system b)\<rparr> else b)
     else if limit_guard G E e (system b) then b\<lparr>locked:=True\<rparr>
     else b\<lparr>system:=system_react e (system b)\<rparr>)"

definition bounded_boot :: bounded_system where
  "bounded_boot = \<lparr>system=system_boot, locked=False\<rparr>"

definition identifiers_bounded where
  "identifiers_bounded G E s \<longleftrightarrow> generation (machine s)\<le>G \<and> era s\<le>E"

definition bounded_valid where
  "bounded_valid G E b \<longleftrightarrow> physical_valid (system b) \<and>
    identifiers_bounded G E (system b)"

fun bounded_history where
  "bounded_history G E ev 0 = bounded_boot"
| "bounded_history G E ev (Suc n) = bounded_react G E (ev n) (bounded_history G E ev n)"

lemma receive_generation_unchanged:
  assumes "physical_valid s"
  shows "generation (machine (system_react (Receive ep p) s)) = generation (machine s)"
proof (cases "ep=era s \<and> (ep,p)\<in>certificates s")
  case False
  then show ?thesis by auto
next
  case True
  have bound: "certificate_bound (generation (machine s)) p"
    using assms True unfolding physical_valid_def by blast
  show ?thesis using True bound
    by (cases p; auto simp: numbered_react_def Let_def split: if_splits)
qed

lemma unrestricted_generation_mono:
  assumes "physical_valid s"
  shows "generation (machine s) \<le> generation (machine (system_react e s))"
  using assms generation_mono_step[where p="Enqueue _" and s="machine s"]
    generation_mono_step[where p=Schedule and s="machine s"] receive_generation_unchanged[OF assms]
  by (cases e; auto simp: numbered_react_def Let_def split: if_splits)

lemma unrestricted_era_mono:
  "era s \<le> era (system_react e s)"
  by (cases e) (auto split: if_splits)

lemma allowed_identifiers_bounded:
  assumes phys: "physical_valid s" and bound: "identifiers_bounded G E s"
    and allowed: "\<not> limit_guard G E e s"
  shows "identifiers_bounded G E (system_react e s)"
  using assms receive_generation_unchanged[OF phys]
  by (cases e; cases "stage (core (machine s))";
    auto simp: identifiers_bounded_def limit_guard_def numbered_react_def Let_def grant_to_def
      split: if_splits)

lemma plant_identifiers_unchanged:
  assumes "plant_event e"
  shows "generation (machine (system_react e s)) = generation (machine s) \<and>
    era (system_react e s) = era s"
  using assms by (cases e) auto

lemma bounded_step_physical_valid:
  "physical_valid (system b) \<Longrightarrow> physical_valid (system (bounded_react G E e b))"
  using physical_step_valid[of "system b" e]
  by (auto simp: bounded_react_def split: if_splits)

theorem bounded_step_valid:
  assumes "bounded_valid G E b"
  shows "bounded_valid G E (bounded_react G E e b)"
proof -
  have phys: "physical_valid (system b)" and ids: "identifiers_bounded G E (system b)"
    using assms by (auto simp: bounded_valid_def)
  have p: "physical_valid (system (bounded_react G E e b))"
    by (rule bounded_step_physical_valid[OF phys])
  have i: "identifiers_bounded G E (system (bounded_react G E e b))"
    using ids allowed_identifiers_bounded[OF phys ids] plant_identifiers_unchanged[of e "system b"]
    by (auto simp: bounded_react_def identifiers_bounded_def split: if_splits)
  show ?thesis using p i by (simp add: bounded_valid_def)
qed

lemma bounded_boot_valid: "bounded_valid G E bounded_boot"
  using physical_boot_valid
  by (simp add: bounded_valid_def identifiers_bounded_def bounded_boot_def system_boot_def numbered_boot_def)

theorem bounded_history_valid: "bounded_valid G E (bounded_history G E ev n)"
  by (induction n; simp only: bounded_history.simps;
    blast intro: bounded_boot_valid bounded_step_valid)

theorem bounded_identifiers:
  "generation (machine (system (bounded_history G E ev n)))\<le>G \<and>
    era (system (bounded_history G E ev n))\<le>E"
  using bounded_history_valid[of G E ev n]
  by (simp add: bounded_valid_def identifiers_bounded_def)

theorem bounded_physical_safety:
  "\<not> (in_zone (system (bounded_history G E ev n)) A \<and>
    in_zone (system (bounded_history G E ev n)) B)"
  using bounded_history_valid[of G E ev n] valid_state_no_collision
  unfolding bounded_valid_def by blast

theorem bounded_accounting:
  "received (core (machine (system (bounded_history G E ev n)))) i =
    pending (core (machine (system (bounded_history G E ev n)))) i +
    served (core (machine (system (bounded_history G E ev n)))) i"
  using bounded_history_valid[of G E ev n]
  by (simp add: bounded_valid_def physical_valid_def valid_def)

theorem lock_persists:
  "locked b \<Longrightarrow> locked (bounded_react G E e b)"
  by (simp add: bounded_react_def)

theorem lock_keeps_control_state:
  assumes "locked b"
  shows "machine (system (bounded_react G E e b)) = machine (system b) \<and>
    era (system (bounded_react G E e b)) = era (system b)"
  using assms by (cases e) (auto simp: bounded_react_def)

theorem locking_preserves_snapshot:
  assumes "\<not>locked b" "limit_guard G E e (system b)"
  shows "locked (bounded_react G E e b) \<and> system (bounded_react G E e b)=system b"
  using assms by (simp add: bounded_react_def)

lemma bounded_generation_mono_step:
  "bounded_valid G E b \<Longrightarrow>
    generation (machine (system b)) \<le> generation (machine (system (bounded_react G E e b)))"
  using unrestricted_generation_mono[of "system b" e]
  by (auto simp: bounded_valid_def bounded_react_def split: if_splits)

theorem bounded_generation_monotone:
  "mono (\<lambda>n. generation (machine (system (bounded_history G E ev n))))"
  unfolding mono_iff_le_Suc
  by (simp only: bounded_history.simps;
    blast intro: bounded_generation_mono_step bounded_history_valid)

theorem bounded_era_monotone:
  "mono (\<lambda>n. era (system (bounded_history G E ev n)))"
  unfolding mono_iff_le_Suc
  by (simp only: bounded_history.simps;
    auto simp: bounded_react_def intro: unrestricted_era_mono split: if_splits)

theorem finite_width_representation:
  "generation (machine (system (bounded_history (2^w-1) (2^v-1) ev n))) < 2^w \<and>
    era (system (bounded_history (2^w-1) (2^v-1) ev n)) < 2^v"
proof -
  have positive: "(0::nat)<2^w" "(0::nat)<2^v" by simp_all
  show ?thesis using bounded_identifiers[of "2^w-1" "2^v-1" ev n] positive by arith
qed

theorem wire_identifier_roundtrip:
  "generation (machine (system (bounded_history (2^w-1) (2^v-1) ev n))) mod 2^w =
      generation (machine (system (bounded_history (2^w-1) (2^v-1) ev n))) \<and>
    era (system (bounded_history (2^w-1) (2^v-1) ev n)) mod 2^v =
      era (system (bounded_history (2^w-1) (2^v-1) ev n))"
  using finite_width_representation[of w v ev n] by auto

fun run_bounded where
  "run_bounded G E [] b = b"
| "run_bounded G E (e#es) b = run_bounded G E es (bounded_react G E e b)"

lemma run_bounded_valid:
  "bounded_valid G E b \<Longrightarrow> bounded_valid G E (run_bounded G E es b)"
  by (induction es arbitrary: b; simp only: run_bounded.simps;
    blast intro: bounded_step_valid)

theorem locked_run_keeps_machine:
  assumes "locked b"
  shows "locked (run_bounded G E es b) \<and>
    machine (system (run_bounded G E es b)) = machine (system b)"
  using assms
  by (induction es arbitrary: b; simp only: run_bounded.simps;
    metis lock_persists lock_keeps_control_state)

definition clearance_events where
  "clearance_events s = (case stage (core (machine s)) of
    Entering i \<Rightarrow> [PlantEnter i, SenseEntry i, Receive (era s) (EnterAck i (generation (machine s))),
      SystemPoll, PlantLeave i, SenseExit i, Receive (era s) (LeaveAck i (generation (machine s)))]
  | Occupied i \<Rightarrow> [SystemPoll, PlantLeave i, SenseExit i,
      Receive (era s) (LeaveAck i (generation (machine s)))]
  | Leaving i \<Rightarrow> [PlantLeave i, SenseExit i, Receive (era s) (LeaveAck i (generation (machine s)))]
  | Ready \<Rightarrow> [])"

theorem clearance_length_bound: "length (clearance_events s) \<le> 7"
  by (cases "stage (core (machine s))") (simp_all add: clearance_events_def)

lemma clearance_control:
  assumes "\<not>locked b" "stage (core (machine (system b)))\<noteq>Ready"
  shows "let t = run_bounded G E (clearance_events (system b)) b in
    stage (core (machine (system t)))=Ready \<and> \<not>locked t \<and>
    generation (machine (system t))=generation (machine (system b)) \<and>
    era (system t)=era (system b)"
  using assms
  by (cases "stage (core (machine (system b)))";
    simp_all add: Let_def clearance_events_def bounded_react_def limit_guard_def numbered_react_def)

theorem active_visit_can_clear:
  assumes valid: "bounded_valid G E b" and live: "\<not>locked b"
    and active: "stage (core (machine (system b)))\<noteq>Ready"
  shows "let t = run_bounded G E (clearance_events (system b)) b in
    stage (core (machine (system t)))=Ready \<and> \<not>locked t \<and>
    \<not>in_zone (system t) A \<and> \<not>in_zone (system t) B \<and>
    generation (machine (system t))=generation (machine (system b)) \<and>
    era (system t)=era (system b)"
proof -
  let ?t = "run_bounded G E (clearance_events (system b)) b"
  have control: "stage (core (machine (system ?t)))=Ready \<and> \<not>locked ?t \<and>
    generation (machine (system ?t))=generation (machine (system b)) \<and>
    era (system ?t)=era (system b)"
    using clearance_control[OF live active, of G E] by (simp add: Let_def)
  have tv: "bounded_valid G E ?t" by (rule run_bounded_valid[OF valid])
  have empty: "\<not>in_zone (system ?t) A \<and> \<not>in_zone (system ?t) B"
    using tv control by (auto simp: bounded_valid_def physical_valid_def valid_def train_all)
  show ?thesis using control empty by (simp only: Let_def; blast)
qed

definition zero_cap_pending where
  "zero_cap_pending = bounded_react 0 0 (SystemRequest A) bounded_boot"

theorem exhaustion_keeps_unserved_request:
  "let b = bounded_react 0 0 SystemPoll zero_cap_pending in
    locked b \<and> pending (core (machine (system b))) A=1 \<and>
    served (core (machine (system b))) A=0 \<and> bounded_react 0 0 SystemPoll b=b"
  by (simp add: zero_cap_pending_def bounded_react_def limit_guard_def bounded_boot_def
    system_boot_def numbered_boot_def boot_def numbered_react_def Let_def)

text \<open>A deliberately incorrect reuse rule retains genuine old certificates
  while mapping every admission number above one back to one. The witness
  below violates physical safety even without forging a sensor certificate.\<close>

definition completed_a where
  "completed_a = run_system [PlantLeave A, SenseExit A, Receive 0 (LeaveAck A 1)] a_leaving"

definition naive_reuse where
  "naive_reuse e s = (let t=system_react e s in
    if generation (machine t)>1 then t\<lparr>machine:=(machine t)\<lparr>generation:=1\<rparr>\<rparr> else t)"

fun run_naive where
  "run_naive [] s = s"
| "run_naive (e#es) s = run_naive es (naive_reuse e s)"

theorem authentic_replay_after_reuse_collides:
  "let s = run_naive [SystemRequest A, SystemPoll, PlantEnter A, SenseEntry A,
    Receive 0 (EnterAck A 1), SystemPoll, Receive 0 (LeaveAck A 1),
    SystemRequest B, SystemPoll, PlantEnter B] completed_a
   in in_zone s A \<and> in_zone s B"
  by (simp add: naive_reuse_def completed_a_def a_leaving_def system_boot_def
    numbered_boot_def boot_def numbered_react_def Let_def grant_to_def)

end
