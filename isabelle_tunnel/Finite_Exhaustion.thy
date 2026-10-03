theory Finite_Exhaustion
  imports Finite_Activation
begin

text \<open>Exhaustion stops new entry emission, not physical movement. The last
  committed owner's already emitted commands remain independently deliverable.
  The same configured limit is used throughout each execution.\<close>

lemma exhaustion_noncommit_epoch:
  assumes "journal_valid (fence_log p)" "msg \<noteq> CommitHandoff"
  shows "committed_epoch (fence_step msg p) = committed_epoch p"
  using assms
  by (cases msg; simp add: committed_epoch_def del: journal_step.simps)

lemma exhaustion_noncommit_stopped:
  assumes "emission_stopped p" "msg \<noteq> CommitHandoff"
  shows "emission_stopped (fence_step msg p)"
  using assms by (cases msg; auto)

lemma activation_noncommit_keeps_stop:
  assumes v: "activation_valid s" and stopped: "emission_stopped (engine s)"
    and not_commit: "e \<noteq> Wire CommitHandoff"
  shows "committed_epoch (engine (activation_step e s)) = committed_epoch (engine s) \<and>
    emission_stopped (engine (activation_step e s))"
proof (cases e)
  case (Wire msg)
  have jv: "journal_valid (fence_log (engine s))"
    using v unfolding activation_valid_def fenced_valid_def by blast
  have nc: "msg \<noteq> CommitHandoff" using not_commit Wire by simp
  have keep_epoch: "committed_epoch (fence_step msg (engine s)) = committed_epoch (engine s)"
    by (rule exhaustion_noncommit_epoch[OF jv nc])
  have keep_stop: "emission_stopped (fence_step msg (engine s))"
    by (rule exhaustion_noncommit_stopped[OF stopped nc])
  show ?thesis using activation_network_projection[of msg s] keep_epoch keep_stop stopped Wire
    by auto
next
  case (StoreFlush i)
  then show ?thesis using stopped by (simp add: set_activation_log_def)
next
  case (StoreCommit i)
  then show ?thesis using stopped store_commit_does_not_activate[of i s] by simp
next
  case (ApplyFloor i)
  then show ?thesis using stopped by (auto simp: load_floor_def committed_epoch_def)
next
  case (DevicePowerLoss i)
  then show ?thesis using stopped by (simp add: set_activation_log_def)
next
  case (DeviceRecover i)
  then show ?thesis using stopped by (auto simp: load_floor_def committed_epoch_def)
qed

theorem exhausted_step_keeps_epoch_and_stop:
  assumes v: "finite_valid L s" and cap: "committed_epoch (engine s)=L"
    and stopped: "emission_stopped (engine s)"
  shows "committed_epoch (engine (finite_activation_step L e s))=L \<and>
    emission_stopped (engine (finite_activation_step L e s))"
proof -
  have av: "activation_valid s" using v unfolding finite_valid_def by blast
  have normal: "e \<noteq> Wire CommitHandoff \<Longrightarrow>
      committed_epoch (engine (activation_step e s))=L \<and>
      emission_stopped (engine (activation_step e s))"
    using activation_noncommit_keeps_stop[OF av stopped, of e] cap by simp
  show ?thesis using normal cap stopped
    by (cases e; auto simp: finite_activation_step_def stop_emission_def committed_epoch_def
      split: fence_event.splits)
qed

theorem exhausted_run_keeps_epoch_and_stop:
  assumes "finite_valid L s" "committed_epoch (engine s)=L"
    "emission_stopped (engine s)"
  shows "committed_epoch (engine (finite_activation_run L es s))=L \<and>
    emission_stopped (engine (finite_activation_run L es s))"
  using assms
proof (induction es arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  have valid_after: "finite_valid L (finite_activation_step L e s)"
    by (rule finite_activation_step_valid[OF Cons.prems(1)])
  have stopped_after: "committed_epoch (engine (finite_activation_step L e s))=L \<and>
      emission_stopped (engine (finite_activation_step L e s))"
    by (rule exhausted_step_keeps_epoch_and_stop[OF Cons.prems])
  show ?case using Cons.IH[OF valid_after] stopped_after by simp
qed

theorem exhausted_floors_equal_limit:
  assumes v: "finite_valid L s" and cap: "committed_epoch (engine s)=L"
  shows "reject_below (engine s) i=L \<and> disk_floor s i=L"
proof -
  have lower: "L \<le> reject_below (engine s) i"
    using v cap unfolding finite_valid_def activation_valid_def fenced_valid_def fence_core_def by blast
  have middle: "reject_below (engine s) i \<le> disk_floor s i"
    using v unfolding finite_valid_def activation_valid_def by blast
  have upper: "disk_floor s i \<le> L" by (rule finite_disk_bound[OF v])
  show ?thesis using lower middle upper by arith
qed

theorem exhausted_older_entry_rejected:
  assumes "finite_valid L s" "committed_epoch (engine s)=L" "k<L"
  shows "finite_activation_step L (Wire (DeliverEntry k i)) s=s"
  using exhausted_floors_equal_limit[OF assms(1,2), of i] assms(3)
  by (auto simp: finite_activation_step_def)

theorem stopped_new_entry_is_ignored:
  assumes "emission_stopped (engine s)"
  shows "finite_activation_step L (Wire (SendEntry i)) s=s"
  using assms by (simp add: finite_activation_step_def)

text \<open>The final-round delivery rule deliberately does not check the
  emission switch. An already emitted command can still actuate after stopping.
  This is a conditional characterization, not an eventual-exit theorem.\<close>

theorem last_round_delivery_after_stop:
  assumes v: "finite_valid L s" and cap: "committed_epoch (engine s)=L"
    and stopped: "emission_stopped (engine s)"
    and awake: "endpoint_awake s i" and issued: "(L,i) \<in> command_history (engine s)"
  shows "i \<in> physical_inside (engine (finite_activation_step L (Wire (DeliverEntry L i)) s))"
  using exhausted_floors_equal_limit[OF v cap, of i] awake issued
  by (simp add: finite_activation_step_def)

definition final_round_queued where
  "final_round_queued = finite_activation_run 1
    (activation_handoff_trace 1 (Some A) @ [Wire (SendEntry A)]) activation_boot"

definition final_round_stopped where
  "final_round_stopped = finite_activation_step 1 (Wire (BeginHandoff (Some B))) final_round_queued"

lemma final_round_stopped_valid: "finite_valid 1 final_round_stopped"
  unfolding final_round_stopped_def final_round_queued_def
  by (intro finite_activation_step_valid finite_activation_run_valid finite_boot_valid)

theorem final_round_used_then_stopped:
  "committed_epoch (engine final_round_stopped)=1 \<and>
    committed_owner (engine final_round_stopped)=Some A \<and>
    emission_stopped (engine final_round_stopped) \<and>
    physical_inside (engine final_round_stopped)={} \<and>
    (1,A) \<in> command_history (engine final_round_stopped) \<and>
    endpoint_awake final_round_stopped A"
  by (simp add: final_round_stopped_def final_round_queued_def finite_activation_step_def
    activation_handoff_trace_def activation_fence_trace_def activation_boot_def fence_boot_def
    stop_emission_def set_activation_log_def disk_floor_def can_load_floor_def load_floor_def
    committed_epoch_def committed_owner_def journal_boot_def journal_restore_def
    selected_record_def inactive_record_def write_inactive_def fence_train_all)

theorem stopped_final_round_can_still_enter:
  "A \<in> physical_inside (engine
    (finite_activation_step 1 (Wire (DeliverEntry 1 A)) final_round_stopped))"
  using last_round_delivery_after_stop[OF final_round_stopped_valid, where i=A]
    final_round_used_then_stopped by blast

theorem cap_handoff_attempt_stops_emission:
  assumes "committed_epoch (engine s)=L"
  shows "finite_activation_step L (Wire (BeginHandoff owner)) s=stop_emission s"
  using assms by (simp add: finite_activation_step_def)

theorem zero_limit_run_keeps_initial_epoch_and_stop:
  "committed_epoch (engine (finite_activation_run 0 es activation_boot))=0 \<and>
    emission_stopped (engine (finite_activation_run 0 es activation_boot))"
proof -
  have initial_epoch: "committed_epoch (engine activation_boot)=0"
    by (simp add: activation_boot_def fence_boot_def committed_epoch_def
      journal_boot_def journal_restore_def selected_record_def)
  have initial_stop: "emission_stopped (engine activation_boot)"
    by (simp add: activation_boot_def fence_boot_def)
  show ?thesis
    by (rule exhausted_run_keeps_epoch_and_stop[OF finite_boot_valid initial_epoch initial_stop])
qed

theorem cap_enabled_command_has_last_epoch_and_owner:
  assumes v: "finite_valid L s" and cap: "committed_epoch (engine s)=L"
    and issued: "(k,i) \<in> command_history (engine s)"
    and enabled: "reject_below (engine s) i \<le> k"
  shows "k=L \<and> committed_owner (engine s)=Some i"
proof -
  have core: "fence_core (committed_epoch (engine s)) (committed_owner (engine s)) (engine s)"
    using v unfolding finite_valid_def activation_valid_def fenced_valid_def by blast
  have bounds: "k \<le> committed_epoch (engine s) \<and>
      (k=committed_epoch (engine s) \<longrightarrow> committed_owner (engine s)=Some i)"
    by (rule core_command[OF core issued])
  have at_cap: "k=L"
    using bounds cap enabled exhausted_floors_equal_limit[OF v cap, of i] by arith
  show ?thesis using bounds cap at_cap by simp
qed

end
