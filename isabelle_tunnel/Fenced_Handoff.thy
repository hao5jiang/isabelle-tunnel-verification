theory Fenced_Handoff
  imports Durable_Admission
begin

text \<open>Explicit asynchronous fencing handshake. Packet sets are authentic
  emission histories, permitting delay, nondelivery, and repeated delivery.
  Controller crashes retain those histories and the physical state, clear
  received acknowledgements, abort the journal transaction, and stop emission.
  An endpoint raises its rejection floor before acknowledging an empty zone.
  Entry checks that floor at actuation, not merely when a packet is queued.
  Endpoint floors do not reset in this model. Natural-number epochs do not wrap.
  Storage has exactly the assumptions of Checkpoint_Journal; authentication,
  endpoint persistence, and the local actuation gate are implementation duties.
  No eventual-delivery, eventual-exit, or fault-free suffix is assumed.\<close>

record fence_system =
  fence_log :: "(nat \<times> train option) checkpoint_journal"
  emission_stopped :: bool
  reject_below :: "train \<Rightarrow> nat"
  command_history :: "(nat \<times> train) set"
  fence_requests :: "(nat \<times> train) set"
  ack_history :: "(nat \<times> train) set"
  ack_received :: "(nat \<times> train) set"
  physical_inside :: "train set"

definition committed_epoch where
  "committed_epoch s = fst (the (journal_restore (fence_log s)))"

definition committed_owner where
  "committed_owner s = snd (the (journal_restore (fence_log s)))"

definition fence_core where
  "fence_core g owner s \<longleftrightarrow>
    (\<forall>i. g \<le> reject_below s i) \<and>
    (\<forall>k i. (k,i) \<in> command_history s \<longrightarrow>
       k \<le> g \<and> (k=g \<longrightarrow> owner=Some i)) \<and>
    (\<forall>i\<in>physical_inside s. owner=Some i) \<and>
    (\<forall>k i. (k,i) \<in> ack_history s \<longrightarrow>
       k \<le> reject_below s i \<and> (g<k \<longrightarrow> i \<notin> physical_inside s)) \<and>
    ack_received s \<subseteq> ack_history s"

definition fenced_valid where
  "fenced_valid s \<longleftrightarrow> journal_valid (fence_log s) \<and>
    fence_core (committed_epoch s) (committed_owner s) s"

definition fence_boot :: fence_system where
  "fence_boot = \<lparr>fence_log=journal_boot (0,None), emission_stopped=True,
    reject_below=(\<lambda>_. 0), command_history={}, fence_requests={},
    ack_history={}, ack_received={}, physical_inside={}\<rparr>"

datatype fence_event = BeginHandoff "train option" | FlushHandoff | CommitHandoff
  | SendEntry train | DeliverEntry nat train | DeliverFence nat train
  | SendClearAck nat train | ReceiveClearAck nat train | PhysicalExit train
  | ControllerCrash

fun fence_step where
  "fence_step (BeginHandoff owner) s = s\<lparr>
    fence_log:=journal_step (Prepare (Suc (committed_epoch s),owner)) (fence_log s),
    emission_stopped:=True,
    fence_requests:=insert (Suc (committed_epoch s),A)
      (insert (Suc (committed_epoch s),B) (fence_requests s))\<rparr>"
| "fence_step FlushHandoff s = s\<lparr>fence_log:=journal_step Flush (fence_log s)\<rparr>"
| "fence_step CommitHandoff s = (case inactive_record (fence_log s) of
    Complete (k,owner) \<Rightarrow>
      (if journal_pending (fence_log s) \<and> emission_stopped s \<and>
        k=Suc (committed_epoch s) \<and> (\<forall>i. (k,i) \<in> ack_received s)
       then s\<lparr>fence_log:=journal_step Commit (fence_log s), emission_stopped:=False\<rparr>
       else s)
    | _ \<Rightarrow> s)"
| "fence_step (SendEntry i) s =
    (if \<not> emission_stopped s \<and> committed_owner s = Some i
     then s\<lparr>command_history:=insert (committed_epoch s,i) (command_history s)\<rparr>
     else s)"
| "fence_step (DeliverEntry k i) s =
    (if (k,i) \<in> command_history s \<and> reject_below s i \<le> k
     then s\<lparr>physical_inside:=insert i (physical_inside s)\<rparr> else s)"
| "fence_step (DeliverFence k i) s =
    (if (k,i) \<in> fence_requests s then
      s\<lparr>reject_below:=(reject_below s)(i:=max k (reject_below s i))\<rparr> else s)"
| "fence_step (SendClearAck k i) s =
    (if (k,i) \<in> fence_requests s \<and> k \<le> reject_below s i \<and>
      i \<notin> physical_inside s
     then s\<lparr>ack_history:=insert (k,i) (ack_history s)\<rparr> else s)"
| "fence_step (ReceiveClearAck k i) s =
    (if (k,i) \<in> ack_history s
     then s\<lparr>ack_received:=insert (k,i) (ack_received s)\<rparr> else s)"
| "fence_step (PhysicalExit i) s = s\<lparr>physical_inside:=physical_inside s - {i}\<rparr>"
| "fence_step ControllerCrash s = s\<lparr>fence_log:=journal_step Crash (fence_log s),
    emission_stopped:=True, ack_received:={}\<rparr>"

lemma fence_boot_valid: "fenced_valid fence_boot"
  by (simp add: fenced_valid_def fence_core_def fence_boot_def committed_epoch_def
    committed_owner_def journal_valid_def journal_restore_def selected_record_def journal_boot_def)

lemma received_future_ack:
  assumes "fence_core g owner s" "(k,i) \<in> ack_received s" "g<k"
  shows "k \<le> reject_below s i \<and> i \<notin> physical_inside s"
  using assms unfolding fence_core_def by blast

definition effective_commands where
  "effective_commands s = {i. \<exists>k. (k,i) \<in> command_history s \<and> reject_below s i \<le> k}"

theorem acknowledgements_establish_quiescence:
  assumes "fence_core g owner s" "\<forall>i. (Suc g,i) \<in> ack_received s"
  shows "physical_inside s = {} \<and> effective_commands s = {} \<and>
    (\<forall>i. Suc g \<le> reject_below s i)"
proof -
  have per: "\<And>i. Suc g \<le> reject_below s i \<and> i \<notin> physical_inside s"
  proof -
    fix i
    have seen: "(Suc g,i) \<in> ack_received s" using assms(2) by blast
    show "Suc g \<le> reject_below s i \<and> i \<notin> physical_inside s"
      using received_future_ack[OF assms(1) seen] by simp
  qed
  have empty_physical: "physical_inside s = {}" using per by blast
  have empty_effective: "effective_commands s = {}"
  proof (rule equals0I)
    fix i
    assume "i \<in> effective_commands s"
    then obtain k where cmd: "(k,i) \<in> command_history s" and gate: "reject_below s i \<le> k"
      unfolding effective_commands_def by blast
    have bound: "k \<le> g" using assms(1) cmd unfolding fence_core_def by blast
    have floor: "Suc g \<le> reject_below s i" using per[of i] by blast
    show False using bound gate floor by arith
  qed
  show ?thesis using empty_physical empty_effective per by blast
qed

lemma core_floor:
  "fence_core g owner s \<Longrightarrow> g \<le> reject_below s i"
  unfolding fence_core_def by blast

lemma core_command:
  "fence_core g owner s \<Longrightarrow> (k,i) \<in> command_history s \<Longrightarrow>
    k \<le> g \<and> (k=g \<longrightarrow> owner=Some i)"
  unfolding fence_core_def by blast

lemma core_ack:
  "fence_core g owner s \<Longrightarrow> (k,i) \<in> ack_history s \<Longrightarrow>
    k \<le> reject_below s i \<and> (g<k \<longrightarrow> i \<notin> physical_inside s)"
  unfolding fence_core_def by blast

lemma core_entry_preserved:
  assumes core: "fence_core g owner s" and cmd: "(k,i) \<in> command_history s"
    and gate: "reject_below s i \<le> k"
  shows "fence_core g owner (s\<lparr>physical_inside:=insert i (physical_inside s)\<rparr>)"
proof -
  have floor: "g \<le> reject_below s i" using core_floor[OF core, of i] .
  have bound: "k \<le> g \<and> (k=g \<longrightarrow> owner=Some i)" using core_command[OF core cmd] .
  have eq: "k=g" using floor bound gate by arith
  have own: "owner=Some i" using bound eq by blast
  have ack_bound: "\<And>n. (n,i) \<in> ack_history s \<Longrightarrow> n \<le> g"
  proof -
    fix n
    assume a: "(n,i) \<in> ack_history s"
    have "n \<le> reject_below s i" using core_ack[OF core a] by blast
    then show "n \<le> g" using gate eq by arith
  qed
  show ?thesis using core own ack_bound
    unfolding fence_core_def by (auto; metis not_le)
qed

lemma core_raise_floor:
  assumes "fence_core g owner s" "\<forall>i. reject_below s i \<le> f i"
  shows "fence_core g owner (s\<lparr>reject_below:=f\<rparr>)"
  using assms unfolding fence_core_def by (auto intro: order_trans; metis order_trans)

lemma commit_core:
  assumes "fence_core g old s" "\<forall>i. (Suc g,i) \<in> ack_received s"
  shows "fence_core (Suc g) owner s"
proof -
  have commands: "\<forall>k i. (k,i) \<in> command_history s \<longrightarrow>
      k \<le> Suc g \<and> (k=Suc g \<longrightarrow> owner=Some i)"
  proof (intro allI impI)
    fix k i
    assume cmd: "(k,i) \<in> command_history s"
    have "k \<le> g" using core_command[OF assms(1) cmd] by blast
    then show "k \<le> Suc g \<and> (k=Suc g \<longrightarrow> owner=Some i)" by auto
  qed
  show ?thesis using assms acknowledgements_establish_quiescence[OF assms] commands
    unfolding fence_core_def by auto
qed

lemma fence_commit_valid:
  assumes v: "fenced_valid s"
  shows "fenced_valid (fence_step CommitHandoff s)"
proof (cases "inactive_record (fence_log s)")
  case Empty
  then show ?thesis using v by simp
next
  case (Partial payload)
  then show ?thesis using v by simp
next
  case (Complete payload)
  obtain k owner where pair: "payload=(k,owner)" by (cases payload) auto
  show ?thesis
  proof (cases "journal_pending (fence_log s) \<and> emission_stopped s \<and>
      k=Suc (committed_epoch s) \<and> (\<forall>i. (k,i) \<in> ack_received s)")
    case False
    show ?thesis using v
      by (simp only: fence_step.simps Complete pair checkpoint_slot.case prod.case False if_False)
  next
    case True
    have jv: "journal_valid (journal_step Commit (fence_log s))"
      using v commit_valid[where s="fence_log s"] unfolding fenced_valid_def by blast
    have restore: "journal_restore (journal_step Commit (fence_log s)) = Some (k,owner)"
      using True Complete pair
        complete_commit_is_recoverable[where s="fence_log s" and x="(k,owner)"] by blast
    have core: "fence_core k owner s"
      using commit_core[where g="committed_epoch s" and old="committed_owner s"
          and s=s and owner=owner] v True unfolding fenced_valid_def by blast
    show ?thesis using Complete pair True jv restore core
      by (simp only: fence_step.simps checkpoint_slot.case prod.case if_True;
        simp add: fenced_valid_def committed_epoch_def committed_owner_def fence_core_def
          del: journal_step.simps)
  qed
qed

lemma noncommit_valid:
  assumes v: "fenced_valid s" and nc: "e \<noteq> CommitHandoff"
  shows "fenced_valid (fence_step e s)"
proof (cases e)
  case (BeginHandoff owner)
  then show ?thesis using v
    by (simp add: fenced_valid_def fence_core_def committed_epoch_def committed_owner_def
      del: journal_step.simps)
next
  case FlushHandoff
  then show ?thesis using v
    by (simp add: fenced_valid_def fence_core_def committed_epoch_def committed_owner_def
      del: journal_step.simps)
next
  case CommitHandoff
  then show ?thesis using nc by blast
next
  case (SendEntry i)
  then show ?thesis using v
    by (auto simp: fenced_valid_def fence_core_def committed_epoch_def committed_owner_def)
next
  case (DeliverEntry k i)
  then show ?thesis using v core_entry_preserved[where g="committed_epoch s"
      and owner="committed_owner s" and s=s and k=k and i=i]
    by (auto simp: fenced_valid_def committed_epoch_def committed_owner_def)
next
  case (DeliverFence k i)
  have raise: "fence_core (committed_epoch s) (committed_owner s)
      (s\<lparr>reject_below:=(reject_below s)(i:=max k (reject_below s i))\<rparr>)"
    using v by (intro core_raise_floor; auto simp: fenced_valid_def)
  show ?thesis using DeliverFence v raise
    by (auto simp: fenced_valid_def committed_epoch_def committed_owner_def)
next
  case (SendClearAck k i)
  then show ?thesis using v
    by (auto simp: fenced_valid_def fence_core_def committed_epoch_def committed_owner_def)
next
  case (ReceiveClearAck k i)
  then show ?thesis using v
    by (auto simp: fenced_valid_def fence_core_def committed_epoch_def committed_owner_def)
next
  case (PhysicalExit i)
  then show ?thesis using v
    by (auto simp: fenced_valid_def fence_core_def committed_epoch_def committed_owner_def)
next
  case ControllerCrash
  then show ?thesis using v crash_valid[where s="fence_log s"]
    by (simp add: fenced_valid_def fence_core_def committed_epoch_def committed_owner_def
      del: journal_step.simps)
qed

theorem fence_step_valid:
  "fenced_valid s \<Longrightarrow> fenced_valid (fence_step e s)"
  using noncommit_valid[where s=s and e=e] fence_commit_valid[where s=s]
  by (cases "e=CommitHandoff") auto

fun fence_history where
  "fence_history ev 0 = fence_boot"
| "fence_history ev (Suc n) = fence_step (ev n) (fence_history ev n)"

theorem fence_history_valid: "fenced_valid (fence_history ev n)"
  by (induction n) (auto intro: fence_boot_valid fence_step_valid)

theorem fenced_physical_mutual_exclusion:
  assumes "fenced_valid s"
  shows "\<not> (A \<in> physical_inside s \<and> B \<in> physical_inside s)"
proof -
  have coverage: "\<forall>i\<in>physical_inside s. committed_owner s=Some i"
    using assms unfolding fenced_valid_def fence_core_def by blast
  have a: "A \<in> physical_inside s \<Longrightarrow> committed_owner s=Some A"
    using coverage by blast
  have b: "B \<in> physical_inside s \<Longrightarrow> committed_owner s=Some B"
    using coverage by blast
  show ?thesis using a b by auto
qed

theorem fenced_all_interleavings_safe:
  "\<not> (A \<in> physical_inside (fence_history ev n) \<and>
         B \<in> physical_inside (fence_history ev n))"
  using fence_history_valid[of ev n] fenced_physical_mutual_exclusion by blast

theorem old_epoch_entry_rejected:
  assumes "fenced_valid s" "k < committed_epoch s"
  shows "fence_step (DeliverEntry k i) s = s"
proof -
  have core: "fence_core (committed_epoch s) (committed_owner s) s"
    using assms(1) unfolding fenced_valid_def by blast
  have floor: "committed_epoch s \<le> reject_below s i" using core_floor[OF core, of i] .
  have "\<not> reject_below s i \<le> k" using floor assms(2) by arith
  then show ?thesis by simp
qed

theorem acknowledged_fence_rejects_older_entry:
  assumes "fenced_valid s" "(k,i) \<in> ack_received s" "n<k"
  shows "fence_step (DeliverEntry n i) s = s"
proof -
  have floor: "k \<le> reject_below s i"
    using assms(1,2) unfolding fenced_valid_def fence_core_def by blast
  have "\<not> reject_below s i \<le> n" using floor assms(3) by arith
  then show ?thesis by simp
qed

theorem crash_keeps_fences_and_commands:
  "reject_below (fence_step ControllerCrash s) = reject_below s \<and>
    command_history (fence_step ControllerCrash s) = command_history s \<and>
    physical_inside (fence_step ControllerCrash s) = physical_inside s \<and>
    emission_stopped (fence_step ControllerCrash s) \<and>
    ack_received (fence_step ControllerCrash s) = {}"
  by simp

theorem crash_stops_emission:
  "fence_step (SendEntry i) (fence_step ControllerCrash s) = fence_step ControllerCrash s"
  by simp

fun map_checkpoint_slot where
  "map_checkpoint_slot f Empty = Empty"
| "map_checkpoint_slot f (Partial x) = Partial (f x)"
| "map_checkpoint_slot f (Complete x) = Complete (f x)"

definition map_checkpoint_journal where
  "map_checkpoint_journal f j = \<lparr>
    journal_left=map_checkpoint_slot f (journal_left j),
    journal_right=map_checkpoint_slot f (journal_right j),
    journal_active=journal_active j, journal_pending=journal_pending j,
    journal_commits=map f (journal_commits j)\<rparr>"

lemma mapped_restore:
  "journal_restore (map_checkpoint_journal f j) = map_option f (journal_restore j)"
  by (cases "journal_active j"; cases "journal_left j"; cases "journal_right j")
    (simp_all add: journal_restore_def selected_record_def map_checkpoint_journal_def)

lemma mapped_journal_valid:
  "journal_valid j \<Longrightarrow> journal_valid (map_checkpoint_journal f j)"
  by (cases "journal_active j")
    (auto simp: journal_valid_def selected_record_def map_checkpoint_journal_def last_map)

definition fence_projection :: "fence_system \<Rightarrow> admission_system" where
  "fence_projection s = \<lparr>durable=map_checkpoint_journal snd (fence_log s),
    issued=effective_commands s, occupants=physical_inside s\<rparr>"

lemma effective_command_owner:
  assumes core: "fence_core g owner s" and member: "i \<in> effective_commands s"
  shows "owner=Some i"
proof -
  obtain k where cmd: "(k,i) \<in> command_history s" and gate: "reject_below s i \<le> k"
    using member unfolding effective_commands_def by blast
  have floor: "g \<le> reject_below s i" using core_floor[OF core, of i] .
  have bound: "k \<le> g \<and> (k=g \<longrightarrow> owner=Some i)" using core_command[OF core cmd] .
  have "k=g" using floor gate bound by arith
  then show ?thesis using bound by blast
qed

theorem projection_satisfies_admission_invariant:
  assumes v: "fenced_valid s"
  shows "admission_valid (fence_projection s)"
proof -
  have jv: "journal_valid (fence_log s)" using v unfolding fenced_valid_def by blast
  obtain payload where restored: "journal_restore (fence_log s) = Some payload"
    using journal_valid_has_restore[OF jv] by blast
  have core: "fence_core (committed_epoch s) (committed_owner s) s"
    using v unfolding fenced_valid_def by blast
  have cover: "\<forall>i\<in>effective_commands s \<union> physical_inside s. committed_owner s=Some i"
    using effective_command_owner[OF core] core unfolding fence_core_def by blast
  show ?thesis using mapped_journal_valid[OF jv, of snd] cover restored
    by (auto simp: fence_projection_def admission_valid_def covered_by_def
      mapped_restore committed_owner_def)
qed

theorem received_handshake_meets_admission_guard:
  assumes "fenced_valid s" "\<forall>i. (Suc (committed_epoch s),i) \<in> ack_received s"
  shows "quiescent (fence_projection s)"
  using acknowledgements_establish_quiescence[where g="committed_epoch s"
    and owner="committed_owner s" and s=s] assms
  by (auto simp: fenced_valid_def quiescent_def fence_projection_def)

text \<open>The projection preserves the admission invariant and implements
  its quiescence guard using received messages. This is not a step-by-step
  refinement of admission_step: fencing removes effective commands without
  consuming their network histories, a cancellation operation not present
  among the events of Durable_Admission.\<close>

fun fence_run where
  "fence_run [] s = s"
| "fence_run (e#es) s = fence_run es (fence_step e s)"

lemma fence_run_valid:
  "fenced_valid s \<Longrightarrow> fenced_valid (fence_run es s)"
  by (induction es arbitrary: s) (auto intro: fence_step_valid)

definition handoff_trace where
  "handoff_trace k owner = [BeginHandoff owner, FlushHandoff,
    DeliverFence k A, SendClearAck k A, ReceiveClearAck k A,
    DeliverFence k B, SendClearAck k B, ReceiveClearAck k B, CommitHandoff]"

lemma fence_train_all: "(\<forall>i::train. P i) \<longleftrightarrow> P A \<and> P B"
  by (metis train.exhaust)

definition fence_queued_a where
  "fence_queued_a = fence_run (handoff_trace 1 (Some A) @ [SendEntry A]) fence_boot"

definition fence_entered_b where
  "fence_entered_b = fence_run (handoff_trace 2 (Some B) @
    [ControllerCrash, DeliverEntry 1 A, BeginHandoff (Some B), FlushHandoff,
     DeliverFence 3 A, SendClearAck 3 A, ReceiveClearAck 3 A,
     DeliverFence 3 B, SendClearAck 3 B, ReceiveClearAck 3 B, CommitHandoff,
     SendEntry B, DeliverEntry 3 B, DeliverEntry 1 A]) fence_queued_a"

lemma fence_queued_a_valid: "fenced_valid fence_queued_a"
  unfolding fence_queued_a_def by (rule fence_run_valid[OF fence_boot_valid])

lemma fence_entered_b_valid: "fenced_valid fence_entered_b"
  unfolding fence_entered_b_def by (rule fence_run_valid[OF fence_queued_a_valid])

theorem delayed_old_command_survives_but_cannot_enter:
  "physical_inside fence_entered_b = {B} \<and>
    (1,A) \<in> command_history fence_entered_b \<and>
    committed_epoch fence_entered_b = 3 \<and> committed_owner fence_entered_b = Some B"
  by (simp add: fence_entered_b_def fence_queued_a_def handoff_trace_def fence_boot_def
    committed_epoch_def committed_owner_def journal_boot_def journal_restore_def
    selected_record_def inactive_record_def write_inactive_def fence_train_all)

theorem resetting_endpoint_floor_can_collide:
  "physical_inside (fence_step (DeliverEntry 1 A)
      (fence_entered_b\<lparr>reject_below:=(reject_below fence_entered_b)(A:=0)\<rparr>)) = {A,B}"
  using delayed_old_command_survives_but_cannot_enter by simp

end
