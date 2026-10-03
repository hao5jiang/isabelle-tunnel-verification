theory Endpoint_Persistence
  imports Fenced_Handoff
begin

text \<open>Each endpoint has a separate two-slot journal. A received fence
  stages a record but does not activate it. Only a durable Commit activates
  the gate; acknowledgements therefore refer to committed floors. Power loss
  disables entry and acknowledgement emission until recovery reads the journal.
  The platform's floor is the abstract durable floor, not RAM assumed to survive.
  Physical occupancy and authentic packet histories remain independent state.
  Storage assumptions are inherited from Checkpoint_Journal. Loss of complete
  records, broken actuation gates, and finite-width wraparound remain excluded.\<close>

record endpoint_system =
  platform :: fence_system
  device_logs :: "train \<Rightarrow> nat checkpoint_journal"
  device_online :: "train \<Rightarrow> bool"

definition endpoint_boot :: endpoint_system where
  "endpoint_boot = \<lparr>platform=fence_boot, device_logs=(\<lambda>_. journal_boot 0),
    device_online=(\<lambda>_. True)\<rparr>"

definition endpoint_valid where
  "endpoint_valid s \<longleftrightarrow> fenced_valid (platform s) \<and>
    (\<forall>i. journal_valid (device_logs s i) \<and>
      journal_restore (device_logs s i) = Some (reject_below (platform s) i))"

datatype endpoint_event = Network fence_event | EndpointFlush train
  | EndpointCommit train | EndpointPowerLoss train | EndpointRecover train

definition replace_device_log where
  "replace_device_log i j s = s\<lparr>device_logs:=(device_logs s)(i:=j)\<rparr>"

fun network_step where
  "network_step (DeliverFence k i) s =
    (if device_online s i \<and> (k,i) \<in> fence_requests (platform s)
     then replace_device_log i
       (journal_step (Prepare (max k (reject_below (platform s) i))) (device_logs s i)) s
     else s)"
| "network_step (DeliverEntry k i) s =
    (if device_online s i then s\<lparr>platform:=fence_step (DeliverEntry k i) (platform s)\<rparr> else s)"
| "network_step (SendClearAck k i) s =
    (if device_online s i then s\<lparr>platform:=fence_step (SendClearAck k i) (platform s)\<rparr> else s)"
| "network_step e s = s\<lparr>platform:=fence_step e (platform s)\<rparr>"

fun endpoint_step where
  "endpoint_step (Network e) s = network_step e s"
| "endpoint_step (EndpointFlush i) s =
    (if device_online s i then replace_device_log i
      (journal_step Flush (device_logs s i)) s else s)"
| "endpoint_step (EndpointCommit i) s =
    (case inactive_record (device_logs s i) of Complete k \<Rightarrow>
      (if device_online s i \<and> journal_pending (device_logs s i) \<and>
        reject_below (platform s) i \<le> k \<and> (k,i) \<in> fence_requests (platform s)
       then s\<lparr>device_logs:=(device_logs s)(i:=journal_step Commit (device_logs s i)),
         platform:=fence_step (DeliverFence k i) (platform s)\<rparr> else s)
    | _ \<Rightarrow> s)"
| "endpoint_step (EndpointPowerLoss i) s =
    (replace_device_log i (journal_step Crash (device_logs s i)) s)
      \<lparr>device_online:=(device_online s)(i:=False)\<rparr>"
| "endpoint_step (EndpointRecover i) s =
    (case journal_restore (device_logs s i) of None \<Rightarrow> s
    | Some k \<Rightarrow> s\<lparr>device_online:=(device_online s)(i:=True),
        platform:=(platform s)\<lparr>reject_below:=(reject_below (platform s))(i:=k)\<rparr>\<rparr>)"

lemma fence_nonfence_preserves_floor:
  "(\<And>k i. e \<noteq> DeliverFence k i) \<Longrightarrow>
    reject_below (fence_step e p) = reject_below p"
  by (cases e; auto split: checkpoint_slot.splits prod.splits)

lemma endpoint_boot_valid: "endpoint_valid endpoint_boot"
  by (simp add: endpoint_valid_def endpoint_boot_def fence_boot_valid fence_boot_def
    fenced_valid_def fence_core_def committed_epoch_def committed_owner_def
    journal_valid_def journal_restore_def selected_record_def journal_boot_def)

lemma device_log_update_valid:
  assumes "endpoint_valid s" "journal_valid j"
    "journal_restore j = journal_restore (device_logs s i)"
  shows "endpoint_valid (replace_device_log i j s)"
  using assms by (auto simp: endpoint_valid_def replace_device_log_def)

lemma platform_update_valid:
  assumes "endpoint_valid s" "fenced_valid p" "reject_below p = reject_below (platform s)"
  shows "endpoint_valid (s\<lparr>platform:=p\<rparr>)"
  using assms by (simp add: endpoint_valid_def)

lemma network_step_valid:
  assumes v: "endpoint_valid s"
  shows "endpoint_valid (network_step e s)"
proof (cases "\<exists>k i. e=DeliverFence k i")
  case True
  then obtain k i where msg: "e=DeliverFence k i" by blast
  have jv: "journal_valid (device_logs s i)" using v unfolding endpoint_valid_def by blast
  have upd: "endpoint_valid (replace_device_log i
      (journal_step (Prepare (max k (reject_below (platform s) i))) (device_logs s i)) s)"
    by (rule device_log_update_valid[OF v]; simp add: jv del: journal_step.simps)
  show ?thesis using msg v upd by simp
next
  case False
  have nf: "\<And>k i. e \<noteq> DeliverFence k i" using False by blast
  have pv: "fenced_valid (fence_step e (platform s))"
    using v fence_step_valid[where s="platform s" and e=e] unfolding endpoint_valid_def by blast
  have fl: "reject_below (fence_step e (platform s)) = reject_below (platform s)"
    by (rule fence_nonfence_preserves_floor[OF nf])
  have upd: "endpoint_valid (s\<lparr>platform:=fence_step e (platform s)\<rparr>)"
    by (rule platform_update_valid[OF v pv fl])
  show ?thesis using v upd nf by (cases e; auto)
qed

lemma endpoint_commit_valid:
  assumes v: "endpoint_valid s"
  shows "endpoint_valid (endpoint_step (EndpointCommit i) s)"
proof (cases "inactive_record (device_logs s i)")
  case Empty
  then show ?thesis using v by simp
next
  case (Partial k)
  then show ?thesis using v by simp
next
  case (Complete k)
  show ?thesis
  proof (cases "device_online s i \<and> journal_pending (device_logs s i) \<and>
      reject_below (platform s) i \<le> k \<and> (k,i) \<in> fence_requests (platform s)")
    case False
    show ?thesis using v
      by (simp only: endpoint_step.simps Complete checkpoint_slot.case False if_False)
  next
    case True
    have jv: "journal_valid (journal_step Commit (device_logs s i))"
      using v commit_valid[where s="device_logs s i"] unfolding endpoint_valid_def by blast
    have restored: "journal_restore (journal_step Commit (device_logs s i)) = Some k"
      using True Complete complete_commit_is_recoverable[where s="device_logs s i" and x=k] by blast
    have pv: "fenced_valid (fence_step (DeliverFence k i) (platform s))"
      using v fence_step_valid[where s="platform s" and e="DeliverFence k i"]
      unfolding endpoint_valid_def by blast
    show ?thesis using True Complete jv restored pv v
      by (simp only: endpoint_step.simps Complete checkpoint_slot.case if_True;
        auto simp: endpoint_valid_def max_absorb1 max_absorb2 del: journal_step.simps)
  qed
qed

lemma recovered_floor_is_unchanged:
  assumes "endpoint_valid s"
  shows "platform (endpoint_step (EndpointRecover i) s) = platform s"
proof -
  have r: "journal_restore (device_logs s i) = Some (reject_below (platform s) i)"
    using assms unfolding endpoint_valid_def by blast
  show ?thesis by (simp add: r)
qed

theorem endpoint_step_valid:
  assumes v: "endpoint_valid s"
  shows "endpoint_valid (endpoint_step e s)"
proof (cases e)
  case (Network msg)
  then show ?thesis using network_step_valid[OF v, of msg] by simp
next
  case (EndpointFlush i)
  have jv: "journal_valid (device_logs s i)" using v unfolding endpoint_valid_def by blast
  have upd: "endpoint_valid (replace_device_log i (journal_step Flush (device_logs s i)) s)"
    by (rule device_log_update_valid[OF v]; simp add: jv del: journal_step.simps)
  show ?thesis using EndpointFlush v upd by simp
next
  case (EndpointCommit i)
  then show ?thesis using endpoint_commit_valid[OF v, of i] by simp
next
  case (EndpointPowerLoss i)
  have jv: "journal_valid (device_logs s i)" using v unfolding endpoint_valid_def by blast
  have upd: "endpoint_valid (replace_device_log i (journal_step Crash (device_logs s i)) s)"
    by (rule device_log_update_valid[OF v]; simp add: jv crash_valid del: journal_step.simps)
  show ?thesis using EndpointPowerLoss upd
    by (simp add: endpoint_valid_def del: journal_step.simps)
next
  case (EndpointRecover i)
  have r: "journal_restore (device_logs s i) = Some (reject_below (platform s) i)"
    using v unfolding endpoint_valid_def by blast
  show ?thesis using EndpointRecover v by (simp add: r endpoint_valid_def)
qed

fun endpoint_history where
  "endpoint_history ev 0 = endpoint_boot"
| "endpoint_history ev (Suc n) = endpoint_step (ev n) (endpoint_history ev n)"

theorem endpoint_history_valid: "endpoint_valid (endpoint_history ev n)"
  by (induction n) (auto intro: endpoint_boot_valid endpoint_step_valid)

theorem endpoint_crashes_preserve_mutual_exclusion:
  "\<not> (A \<in> physical_inside (platform (endpoint_history ev n)) \<and>
         B \<in> physical_inside (platform (endpoint_history ev n)))"
  using endpoint_history_valid[of ev n] fenced_physical_mutual_exclusion
  unfolding endpoint_valid_def by blast

theorem offline_entry_and_ack_blocked:
  "\<not> device_online s i \<Longrightarrow>
    endpoint_step (Network (DeliverEntry k i)) s = s \<and>
    endpoint_step (Network (SendClearAck k i)) s = s"
  by simp

theorem acknowledged_floor_is_durable:
  assumes "endpoint_valid s" "(k,i) \<in> ack_history (platform s)"
  shows "\<exists>d. journal_restore (device_logs s i) = Some d \<and> k \<le> d"
proof -
  have floor: "k \<le> reject_below (platform s) i"
    using assms unfolding endpoint_valid_def fenced_valid_def fence_core_def by blast
  show ?thesis using assms(1) floor unfolding endpoint_valid_def by blast
qed

theorem staging_does_not_activate_floor:
  "platform (endpoint_step (Network (DeliverFence k i)) s) = platform s"
  by (simp add: replace_device_log_def)

theorem power_loss_keeps_physical_state:
  "physical_inside (platform (endpoint_step (EndpointPowerLoss i) s)) = physical_inside (platform s)"
  by (simp add: replace_device_log_def)

lemma network_projection_step:
  "platform (network_step msg s) = platform s \<or>
    platform (network_step msg s) = fence_step msg (platform s)"
  by (cases msg; auto simp: replace_device_log_def)

theorem endpoint_step_refines_fencing:
  assumes v: "endpoint_valid s"
  shows "platform (endpoint_step e s) = platform s \<or>
    (\<exists>msg. platform (endpoint_step e s) = fence_step msg (platform s))"
proof (cases e)
  case (Network msg)
  then show ?thesis using network_projection_step[of msg s] by auto
next
  case (EndpointFlush i)
  then show ?thesis by (simp add: replace_device_log_def)
next
  case (EndpointCommit i)
  show ?thesis
  proof (cases "inactive_record (device_logs s i)")
    case Empty
    then show ?thesis using EndpointCommit by simp
  next
    case (Partial k)
    then show ?thesis using EndpointCommit by simp
  next
    case (Complete k)
    have sim: "platform (endpoint_step (EndpointCommit i) s) = platform s \<or>
        platform (endpoint_step (EndpointCommit i) s) = fence_step (DeliverFence k i) (platform s)"
      by (simp add: Complete)
    show ?thesis using sim EndpointCommit by blast
  qed
next
  case (EndpointPowerLoss i)
  then show ?thesis by (simp add: replace_device_log_def)
next
  case (EndpointRecover i)
  then show ?thesis using recovered_floor_is_unchanged[OF v, of i] by simp
qed

fun endpoint_run where
  "endpoint_run [] s = s"
| "endpoint_run (e#es) s = endpoint_run es (endpoint_step e s)"

lemma endpoint_run_valid:
  "endpoint_valid s \<Longrightarrow> endpoint_valid (endpoint_run es s)"
  by (induction es arbitrary: s) (auto intro: endpoint_step_valid)

theorem endpoint_finite_run_refines_fencing:
  assumes "endpoint_valid s"
  shows "\<exists>msgs. platform (endpoint_run es s) = fence_run msgs (platform s)"
  using assms
proof (induction es arbitrary: s)
  case Nil
  then show ?case by (intro exI[where x="[]"]; simp)
next
  case (Cons e es)
  have valid_next: "endpoint_valid (endpoint_step e s)" using endpoint_step_valid[OF Cons.prems] .
  obtain msgs where suffix: "platform (endpoint_run es (endpoint_step e s)) =
      fence_run msgs (platform (endpoint_step e s))"
    using Cons.IH[OF valid_next] by blast
  have sim: "platform (endpoint_step e s) = platform s \<or>
      (\<exists>msg. platform (endpoint_step e s) = fence_step msg (platform s))"
    using endpoint_step_refines_fencing[OF Cons.prems, of e] .
  show ?case
  proof (cases "platform (endpoint_step e s) = platform s")
    case True
    show ?thesis using suffix True by (intro exI[where x=msgs]; simp)
  next
    case False
    obtain msg where head: "platform (endpoint_step e s) = fence_step msg (platform s)"
      using sim False by blast
    show ?thesis using suffix head by (intro exI[where x="msg#msgs"]; simp)
  qed
qed

definition device_fence_trace where
  "device_fence_trace k i = [Network (DeliverFence k i), EndpointFlush i, EndpointCommit i,
    Network (SendClearAck k i), Network (ReceiveClearAck k i)]"

definition endpoint_handoff_trace where
  "endpoint_handoff_trace k owner = [Network (BeginHandoff owner), Network FlushHandoff] @
    device_fence_trace k A @ device_fence_trace k B @ [Network CommitHandoff]"

definition ep_queued_a where
  "ep_queued_a = endpoint_run (endpoint_handoff_trace 1 (Some A) @ [Network (SendEntry A)]) endpoint_boot"

definition ep_flushed_a where
  "ep_flushed_a = endpoint_run [Network (BeginHandoff (Some B)), Network FlushHandoff,
    Network (DeliverFence 2 A), EndpointFlush A] ep_queued_a"

definition ep_recovered_b where
  "ep_recovered_b = endpoint_run ([EndpointCommit A, Network (SendClearAck 2 A),
    EndpointPowerLoss A, Network (ReceiveClearAck 2 A)] @ device_fence_trace 2 B @
    [Network CommitHandoff, Network (SendEntry B), Network (DeliverEntry 2 B),
      EndpointRecover A, Network (DeliverEntry 1 A)]) ep_flushed_a"

lemma ep_flushed_a_valid: "endpoint_valid ep_flushed_a"
  unfolding ep_flushed_a_def ep_queued_a_def
  by (intro endpoint_run_valid endpoint_boot_valid)

lemma ep_recovered_b_valid: "endpoint_valid ep_recovered_b"
  unfolding ep_recovered_b_def by (rule endpoint_run_valid[OF ep_flushed_a_valid])

theorem durable_endpoint_recovery_keeps_old_entry_blocked:
  "physical_inside (platform ep_recovered_b) = {B} \<and>
    (1,A) \<in> command_history (platform ep_recovered_b) \<and>
    journal_restore (device_logs ep_recovered_b A) = Some 2 \<and> device_online ep_recovered_b A"
  by (simp add: ep_recovered_b_def ep_flushed_a_def ep_queued_a_def
    endpoint_handoff_trace_def device_fence_trace_def endpoint_boot_def fence_boot_def
    replace_device_log_def committed_epoch_def committed_owner_def journal_boot_def
    journal_restore_def selected_record_def inactive_record_def write_inactive_def fence_train_all)

text \<open>This faulty activation is outside endpoint_step: it raises a RAM
  gate before committing its endpoint journal. The resulting acknowledgement
  can authorize handoff, but power loss restores the older gate and permits
  a delayed old command to cause a collision.\<close>

definition early_volatile_activation where
  "early_volatile_activation = ep_flushed_a\<lparr>platform:=
    fence_step (DeliverFence 2 A) (platform ep_flushed_a)\<rparr>"

definition early_ack_collision where
  "early_ack_collision = endpoint_run ([Network (SendClearAck 2 A), Network (ReceiveClearAck 2 A)] @
    device_fence_trace 2 B @ [Network CommitHandoff, Network (SendEntry B),
      Network (DeliverEntry 2 B), EndpointPowerLoss A, EndpointRecover A,
      Network (DeliverEntry 1 A)]) early_volatile_activation"

theorem acknowledgement_before_endpoint_commit_can_collide:
  "physical_inside (platform early_ack_collision) = {A,B}"
  by (simp add: early_ack_collision_def early_volatile_activation_def ep_flushed_a_def ep_queued_a_def
    endpoint_handoff_trace_def device_fence_trace_def endpoint_boot_def fence_boot_def
    replace_device_log_def committed_epoch_def committed_owner_def journal_boot_def
    journal_restore_def selected_record_def inactive_record_def write_inactive_def fence_train_all)

end
