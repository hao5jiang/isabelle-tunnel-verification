theory Endpoint_Activation
  imports Endpoint_Persistence
begin

text \<open>Durable commit and RAM-gate activation are distinct events.
  The active gate can lag behind the durable floor. Old commands may execute
  in that gap, so acknowledgements must use the active gate, not just storage.
  Recovery loads the latest committed floor before enabling entry or ack output.
  During outage the engine's gate is an abstract shadow, not persistent RAM;
  endpoint_awake disables entry and acknowledgement emission. Physical exits
  remain possible. Local gate checks/updates are atomic abstract actions.
  Actual storage, memory-ordering, firmware, and actuator assumptions remain.\<close>

record activation_system =
  engine :: fence_system
  activation_logs :: "train \<Rightarrow> nat checkpoint_journal"
  endpoint_awake :: "train \<Rightarrow> bool"

definition disk_floor where
  "disk_floor s i = the (journal_restore (activation_logs s i))"

definition activation_valid where
  "activation_valid s \<longleftrightarrow> fenced_valid (engine s) \<and>
    (\<forall>i. journal_valid (activation_logs s i) \<and>
      reject_below (engine s) i \<le> disk_floor s i \<and>
      (disk_floor s i=0 \<or> (disk_floor s i,i) \<in> fence_requests (engine s)))"

definition activation_boot :: activation_system where
  "activation_boot = \<lparr>engine=fence_boot, activation_logs=(\<lambda>_. journal_boot 0),
    endpoint_awake=(\<lambda>_. True)\<rparr>"

definition set_activation_log where
  "set_activation_log i j s = s\<lparr>activation_logs:=(activation_logs s)(i:=j)\<rparr>"

definition can_load_floor where
  "can_load_floor i s \<longleftrightarrow> (\<exists>k. journal_restore (activation_logs s i)=Some k \<and>
    reject_below (engine s) i \<le> k \<and>
    (k=reject_below (engine s) i \<or> (k,i) \<in> fence_requests (engine s)))"

definition load_floor where
  "load_floor i s = (if can_load_floor i s then
    s\<lparr>engine:=fence_step (DeliverFence (disk_floor s i) i) (engine s)\<rparr> else s)"

datatype activation_event = Wire fence_event | StoreFlush train | StoreCommit train
  | ApplyFloor train | DevicePowerLoss train | DeviceRecover train

fun activation_network where
  "activation_network (DeliverFence k i) s =
    (if endpoint_awake s i \<and> (k,i) \<in> fence_requests (engine s)
     then set_activation_log i (journal_step (Prepare (max k (disk_floor s i))) (activation_logs s i)) s
     else s)"
| "activation_network (DeliverEntry k i) s =
    (if endpoint_awake s i then s\<lparr>engine:=fence_step (DeliverEntry k i) (engine s)\<rparr> else s)"
| "activation_network (SendClearAck k i) s =
    (if endpoint_awake s i then s\<lparr>engine:=fence_step (SendClearAck k i) (engine s)\<rparr> else s)"
| "activation_network e s = s\<lparr>engine:=fence_step e (engine s)\<rparr>"

fun activation_step where
  "activation_step (Wire e) s = activation_network e s"
| "activation_step (StoreFlush i) s =
    (if endpoint_awake s i then set_activation_log i
      (journal_step Flush (activation_logs s i)) s else s)"
| "activation_step (StoreCommit i) s = (case inactive_record (activation_logs s i) of
    Complete k \<Rightarrow>
      (if endpoint_awake s i \<and> journal_pending (activation_logs s i) \<and>
        disk_floor s i \<le> k \<and> (k,i) \<in> fence_requests (engine s)
       then set_activation_log i (journal_step Commit (activation_logs s i)) s else s)
    | _ \<Rightarrow> s)"
| "activation_step (ApplyFloor i) s = (if endpoint_awake s i then load_floor i s else s)"
| "activation_step (DevicePowerLoss i) s =
    (set_activation_log i (journal_step Crash (activation_logs s i)) s)
      \<lparr>endpoint_awake:=(endpoint_awake s)(i:=False)\<rparr>"
| "activation_step (DeviceRecover i) s =
    (if can_load_floor i s then (load_floor i s)\<lparr>endpoint_awake:=(endpoint_awake s)(i:=True)\<rparr>
     else s)"

lemma activation_boot_valid: "activation_valid activation_boot"
  by (simp add: activation_valid_def activation_boot_def disk_floor_def fence_boot_def
    fenced_valid_def fence_core_def committed_epoch_def committed_owner_def
    journal_valid_def journal_restore_def selected_record_def journal_boot_def)

lemma activation_restore:
  assumes "activation_valid s"
  shows "journal_restore (activation_logs s i)=Some (disk_floor s i)"
proof -
  have jv: "journal_valid (activation_logs s i)" using assms unfolding activation_valid_def by blast
  obtain k where "journal_restore (activation_logs s i)=Some k"
    using journal_valid_has_restore[OF jv] by blast
  then show ?thesis by (simp add: disk_floor_def)
qed

lemma valid_can_load:
  assumes "activation_valid s"
  shows "can_load_floor i s"
proof -
  have bound: "reject_below (engine s) i \<le> disk_floor s i"
    using assms unfolding activation_valid_def by blast
  have source: "disk_floor s i=0 \<or> (disk_floor s i,i) \<in> fence_requests (engine s)"
    using assms unfolding activation_valid_def by blast
  show ?thesis using activation_restore[OF assms, of i] bound source
    by (auto simp: can_load_floor_def)
qed

lemma fenced_requests_mono:
  "fence_requests p \<subseteq> fence_requests (fence_step e p)"
  by (cases e; auto split: checkpoint_slot.splits prod.splits)

lemma activation_engine_update:
  assumes "activation_valid s" "fenced_valid p"
    "\<forall>i. reject_below p i \<le> disk_floor s i"
    "fence_requests (engine s) \<subseteq> fence_requests p"
  shows "activation_valid (s\<lparr>engine:=p\<rparr>)"
  using assms by (auto simp: activation_valid_def disk_floor_def)

lemma activation_log_same_restore:
  assumes "activation_valid s" "journal_valid j"
    "journal_restore j=journal_restore (activation_logs s i)"
  shows "activation_valid (set_activation_log i j s)"
  using assms by (auto simp: activation_valid_def set_activation_log_def disk_floor_def)

lemma load_floor_valid:
  assumes v: "activation_valid s"
  shows "activation_valid (load_floor i s)"
proof -
  have pv: "fenced_valid (fence_step (DeliverFence (disk_floor s i) i) (engine s))"
    using v fence_step_valid[where s="engine s" and e="DeliverFence (disk_floor s i) i"]
    unfolding activation_valid_def by blast
  have bounds: "\<forall>j. reject_below (fence_step (DeliverFence (disk_floor s i) i) (engine s)) j
      \<le> disk_floor s j"
    using v unfolding activation_valid_def by auto
  have upd: "activation_valid (s\<lparr>engine:=fence_step (DeliverFence (disk_floor s i) i) (engine s)\<rparr>)"
    by (rule activation_engine_update[OF v pv bounds fenced_requests_mono])
  show ?thesis using v upd by (simp add: load_floor_def)
qed

lemma loaded_floor_matches_disk:
  assumes "activation_valid s"
  shows "reject_below (engine (load_floor i s)) i = disk_floor s i"
proof -
  have bound: "reject_below (engine s) i \<le> disk_floor s i"
    using assms unfolding activation_valid_def by blast
  have source: "disk_floor s i=0 \<or> (disk_floor s i,i) \<in> fence_requests (engine s)"
    using assms unfolding activation_valid_def by blast
  show ?thesis using bound source valid_can_load[OF assms, of i]
    by (auto simp: load_floor_def)
qed

lemma activation_network_valid:
  assumes v: "activation_valid s"
  shows "activation_valid (activation_network msg s)"
proof (cases "\<exists>k i. msg=DeliverFence k i")
  case True
  then obtain k i where msg: "msg=DeliverFence k i" by blast
  have jv: "journal_valid (activation_logs s i)" using v unfolding activation_valid_def by blast
  have upd: "activation_valid (set_activation_log i
      (journal_step (Prepare (max k (disk_floor s i))) (activation_logs s i)) s)"
    by (rule activation_log_same_restore[OF v]; simp add: jv del: journal_step.simps)
  show ?thesis using msg v upd by simp
next
  case False
  have nf: "\<And>k i. msg \<noteq> DeliverFence k i" using False by blast
  have pv: "fenced_valid (fence_step msg (engine s))"
    using v fence_step_valid[where s="engine s" and e=msg] unfolding activation_valid_def by blast
  have floor: "reject_below (fence_step msg (engine s)) = reject_below (engine s)"
    by (rule fence_nonfence_preserves_floor[OF nf])
  have bounds: "\<forall>i. reject_below (fence_step msg (engine s)) i \<le> disk_floor s i"
    using v by (simp add: floor activation_valid_def)
  have upd: "activation_valid (s\<lparr>engine:=fence_step msg (engine s)\<rparr>)"
    by (rule activation_engine_update[OF v pv bounds fenced_requests_mono])
  show ?thesis using v upd nf by (cases msg; auto)
qed

lemma store_commit_valid:
  assumes v: "activation_valid s"
  shows "activation_valid (activation_step (StoreCommit i) s)"
proof (cases "inactive_record (activation_logs s i)")
  case Empty
  then show ?thesis using v by simp
next
  case (Partial k)
  then show ?thesis using v by simp
next
  case (Complete k)
  show ?thesis
  proof (cases "endpoint_awake s i \<and> journal_pending (activation_logs s i) \<and>
      disk_floor s i \<le> k \<and> (k,i) \<in> fence_requests (engine s)")
    case False
    show ?thesis using v
      by (simp only: activation_step.simps Complete checkpoint_slot.case False if_False)
  next
    case True
    have jv: "journal_valid (journal_step Commit (activation_logs s i))"
      using v commit_valid[where s="activation_logs s i"] unfolding activation_valid_def by blast
    have restored: "journal_restore (journal_step Commit (activation_logs s i))=Some k"
      using True Complete complete_commit_is_recoverable[where s="activation_logs s i" and x=k] by blast
    have bound: "reject_below (engine s) i \<le> k"
    proof -
      have "reject_below (engine s) i \<le> disk_floor s i"
        using v unfolding activation_valid_def by blast
      then show ?thesis using True by arith
    qed
    show ?thesis using True Complete v jv restored bound
      by (simp only: activation_step.simps Complete checkpoint_slot.case if_True;
        auto simp: activation_valid_def set_activation_log_def disk_floor_def del: journal_step.simps)
  qed
qed

theorem activation_step_valid:
  assumes v: "activation_valid s"
  shows "activation_valid (activation_step e s)"
proof (cases e)
  case (Wire msg)
  then show ?thesis using activation_network_valid[OF v, of msg] by simp
next
  case (StoreFlush i)
  have jv: "journal_valid (activation_logs s i)" using v unfolding activation_valid_def by blast
  have upd: "activation_valid (set_activation_log i (journal_step Flush (activation_logs s i)) s)"
    by (rule activation_log_same_restore[OF v]; simp add: jv del: journal_step.simps)
  show ?thesis using StoreFlush v upd by simp
next
  case (StoreCommit i)
  then show ?thesis using store_commit_valid[OF v, of i] by simp
next
  case (ApplyFloor i)
  then show ?thesis using v load_floor_valid[OF v, of i] by simp
next
  case (DevicePowerLoss i)
  have jv: "journal_valid (activation_logs s i)" using v unfolding activation_valid_def by blast
  have upd: "activation_valid (set_activation_log i (journal_step Crash (activation_logs s i)) s)"
    by (rule activation_log_same_restore[OF v]; simp add: jv crash_valid del: journal_step.simps)
  show ?thesis using DevicePowerLoss upd
    by (simp add: activation_valid_def disk_floor_def del: journal_step.simps)
next
  case (DeviceRecover i)
  then show ?thesis using v load_floor_valid[OF v, of i]
    by (simp add: activation_valid_def disk_floor_def)
qed

fun activation_history where
  "activation_history ev 0 = activation_boot"
| "activation_history ev (Suc n) = activation_step (ev n) (activation_history ev n)"

theorem activation_history_valid: "activation_valid (activation_history ev n)"
  by (induction n) (auto intro: activation_boot_valid activation_step_valid)

theorem split_commit_activation_safe:
  "\<not> (A \<in> physical_inside (engine (activation_history ev n)) \<and>
         B \<in> physical_inside (engine (activation_history ev n)))"
  using activation_history_valid[of ev n] fenced_physical_mutual_exclusion
  unfolding activation_valid_def by blast

theorem store_commit_does_not_activate:
  "engine (activation_step (StoreCommit i) s) = engine s"
  by (cases "inactive_record (activation_logs s i)"; simp add: set_activation_log_def)

theorem gap_cannot_acknowledge_new_floor:
  "reject_below (engine s) i < k \<Longrightarrow>
    activation_step (Wire (SendClearAck k i)) s = s"
  by auto

theorem recovery_loads_latest_committed_floor:
  assumes "activation_valid s"
  shows "reject_below (engine (activation_step (DeviceRecover i) s)) i = disk_floor s i \<and>
    endpoint_awake (activation_step (DeviceRecover i) s) i"
  using valid_can_load[OF assms, of i] loaded_floor_matches_disk[OF assms, of i] by simp

lemma activation_network_projection:
  "engine (activation_network msg s)=engine s \<or>
    engine (activation_network msg s)=fence_step msg (engine s)"
  by (cases msg; auto simp: set_activation_log_def)

lemma load_floor_projection:
  "engine (load_floor i s)=engine s \<or>
    engine (load_floor i s)=fence_step (DeliverFence (disk_floor s i) i) (engine s)"
  by (simp add: load_floor_def)

theorem activation_step_refines_fencing:
  "engine (activation_step e s)=engine s \<or>
    (\<exists>msg. engine (activation_step e s)=fence_step msg (engine s))"
proof (cases e)
  case (Wire msg)
  then show ?thesis using activation_network_projection[of msg s] by auto
next
  case (StoreFlush i)
  then show ?thesis by (simp add: set_activation_log_def)
next
  case (StoreCommit i)
  then show ?thesis using store_commit_does_not_activate[of i s] by simp
next
  case (ApplyFloor i)
  have sim: "engine (activation_step (ApplyFloor i) s)=engine s \<or>
      engine (activation_step (ApplyFloor i) s)=fence_step (DeliverFence (disk_floor s i) i) (engine s)"
    using load_floor_projection[of i s] by (cases "endpoint_awake s i"; simp)
  show ?thesis using sim ApplyFloor by blast
next
  case (DevicePowerLoss i)
  then show ?thesis by (simp add: set_activation_log_def)
next
  case (DeviceRecover i)
  have sim: "engine (activation_step (DeviceRecover i) s)=engine s \<or>
      engine (activation_step (DeviceRecover i) s)=fence_step (DeliverFence (disk_floor s i) i) (engine s)"
    using load_floor_projection[of i s] by (cases "can_load_floor i s"; simp)
  show ?thesis using sim DeviceRecover by blast
qed

fun activation_run where
  "activation_run [] s=s"
| "activation_run (e#es) s=activation_run es (activation_step e s)"

lemma activation_run_valid:
  "activation_valid s \<Longrightarrow> activation_valid (activation_run es s)"
  by (induction es arbitrary: s) (auto intro: activation_step_valid)

theorem activation_finite_run_refines_fencing:
  "\<exists>msgs. engine (activation_run es s)=fence_run msgs (engine s)"
proof (induction es arbitrary: s)
  case Nil
  then show ?case by (intro exI[where x="[]"]; simp)
next
  case (Cons e es)
  obtain msgs where suffix: "engine (activation_run es (activation_step e s))=
      fence_run msgs (engine (activation_step e s))"
    using Cons.IH by blast
  show ?case
  proof (cases "engine (activation_step e s)=engine s")
    case True
    show ?thesis using suffix True by (intro exI[where x=msgs]; simp)
  next
    case False
    obtain msg where head: "engine (activation_step e s)=fence_step msg (engine s)"
      using activation_step_refines_fencing[of e s] False by blast
    show ?thesis using suffix head by (intro exI[where x="msg#msgs"]; simp)
  qed
qed

definition activation_fence_trace where
  "activation_fence_trace k i=[Wire (DeliverFence k i), StoreFlush i, StoreCommit i,
    ApplyFloor i, Wire (SendClearAck k i), Wire (ReceiveClearAck k i)]"

definition activation_handoff_trace where
  "activation_handoff_trace k owner=[Wire (BeginHandoff owner), Wire FlushHandoff] @
    activation_fence_trace k A @ activation_fence_trace k B @ [Wire CommitHandoff]"

definition act_queued_a where
  "act_queued_a=activation_run (activation_handoff_trace 1 (Some A) @ [Wire (SendEntry A)]) activation_boot"

definition act_gap where
  "act_gap=activation_run [Wire (BeginHandoff (Some B)), Wire FlushHandoff,
    Wire (DeliverFence 2 A), StoreFlush A, StoreCommit A] act_queued_a"

lemma act_gap_valid: "activation_valid act_gap"
  unfolding act_gap_def act_queued_a_def by (intro activation_run_valid activation_boot_valid)

theorem committed_gap_still_uses_old_gate:
  "disk_floor act_gap A=2 \<and> reject_below (engine act_gap) A=1 \<and>
    A \<in> physical_inside (engine (activation_step (Wire (DeliverEntry 1 A)) act_gap)) \<and>
    activation_step (Wire (SendClearAck 2 A)) act_gap=act_gap"
  by (simp add: act_gap_def act_queued_a_def activation_handoff_trace_def activation_fence_trace_def
    activation_boot_def fence_boot_def set_activation_log_def disk_floor_def can_load_floor_def load_floor_def
    committed_epoch_def committed_owner_def journal_boot_def journal_restore_def
    selected_record_def inactive_record_def write_inactive_def fence_train_all)

definition act_recovered_b where
  "act_recovered_b=activation_run ([DevicePowerLoss A, DeviceRecover A,
    Wire (DeliverEntry 1 A), Wire (SendClearAck 2 A), Wire (ReceiveClearAck 2 A)] @
    activation_fence_trace 2 B @ [Wire CommitHandoff, Wire (SendEntry B),
    Wire (DeliverEntry 2 B), Wire (DeliverEntry 1 A)]) act_gap"

lemma act_recovered_b_valid: "activation_valid act_recovered_b"
  unfolding act_recovered_b_def by (rule activation_run_valid[OF act_gap_valid])

theorem crash_in_commit_activation_gap_is_safe:
  "physical_inside (engine act_recovered_b)={B} \<and>
    reject_below (engine act_recovered_b) A=2 \<and> disk_floor act_recovered_b A=2 \<and>
    (1,A) \<in> command_history (engine act_recovered_b)"
  by (simp add: act_recovered_b_def act_gap_def act_queued_a_def
    activation_handoff_trace_def activation_fence_trace_def activation_boot_def fence_boot_def
    set_activation_log_def disk_floor_def can_load_floor_def load_floor_def committed_epoch_def committed_owner_def
    journal_boot_def journal_restore_def selected_record_def inactive_record_def write_inactive_def fence_train_all)

text \<open>Fault injection changes only which floor an acknowledgement checks.
  Entry retains the normal active-gate check. Storage alone is insufficient.\<close>

definition faulty_disk_ack where
  "faulty_disk_ack k i s = (if endpoint_awake s i \<and> (k,i) \<in> fence_requests (engine s) \<and>
    k \<le> disk_floor s i \<and> i \<notin> physical_inside (engine s)
    then s\<lparr>engine:=(engine s)\<lparr>ack_history:=insert (k,i) (ack_history (engine s))\<rparr>\<rparr> else s)"

definition disk_only_ack_collision where
  "disk_only_ack_collision=activation_run ([Wire (ReceiveClearAck 2 A)] @
    activation_fence_trace 2 B @ [Wire CommitHandoff, Wire (SendEntry B),
    Wire (DeliverEntry 2 B), Wire (DeliverEntry 1 A)]) (faulty_disk_ack 2 A act_gap)"

theorem disk_only_acknowledgement_can_collide:
  "physical_inside (engine disk_only_ack_collision)={A,B}"
  by (simp add: disk_only_ack_collision_def faulty_disk_ack_def act_gap_def act_queued_a_def
    activation_handoff_trace_def activation_fence_trace_def activation_boot_def fence_boot_def
    set_activation_log_def disk_floor_def can_load_floor_def load_floor_def committed_epoch_def committed_owner_def
    journal_boot_def journal_restore_def selected_record_def inactive_record_def write_inactive_def fence_train_all)

end
