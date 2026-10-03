theory Finite_Activation
  imports Endpoint_Activation Journal_Bounds
begin

text \<open>The cap is a parameter of the complete execution.  Epoch L can be
  used; requesting its successor stops new emission without allocating an
  out-of-range payload. This does not cancel previously emitted commands.
  Both journal slots and the ghost commit histories are covered.\<close>

definition packets_bounded where
  "packets_bounded L ps \<longleftrightarrow> (\<forall>k i. (k,i)\<in>ps \<longrightarrow> k\<le>L)"

definition fence_ranges where
  "fence_ranges L p \<longleftrightarrow>
    journal_payloads (\<lambda>x. fst x\<le>L) (fence_log p) \<and>
    packets_bounded L (command_history p) \<and>
    packets_bounded L (fence_requests p) \<and>
    packets_bounded L (ack_history p) \<and>
    packets_bounded L (ack_received p)"

definition activation_ranges where
  "activation_ranges L s \<longleftrightarrow> fence_ranges L (engine s) \<and>
    (\<forall>i. journal_payloads (\<lambda>k. k\<le>L) (activation_logs s i))"

definition finite_valid where
  "finite_valid L s \<longleftrightarrow> activation_valid s \<and> activation_ranges L s"

fun wire_in_range where
  "wire_in_range L (DeliverEntry k i) = (k\<le>L)"
| "wire_in_range L (DeliverFence k i) = (k\<le>L)"
| "wire_in_range L (SendClearAck k i) = (k\<le>L)"
| "wire_in_range L (ReceiveClearAck k i) = (k\<le>L)"
| "wire_in_range L e = True"

fun activation_in_range where
  "activation_in_range L (Wire msg) = wire_in_range L msg"
| "activation_in_range L e = True"

definition stop_emission where
  "stop_emission s = s\<lparr>engine:=(engine s)\<lparr>emission_stopped:=True\<rparr>\<rparr>"

definition finite_activation_step where
  "finite_activation_step L e s =
    (if \<not> activation_in_range L e then s else
     case e of
       Wire (BeginHandoff owner) \<Rightarrow>
         (if committed_epoch (engine s)<L then activation_step e s else stop_emission s)
     | Wire CommitHandoff \<Rightarrow>
         (if committed_epoch (engine s)<L then activation_step e s else s)
     | _ \<Rightarrow> activation_step e s)"

fun finite_activation_run where
  "finite_activation_run L [] s=s"
| "finite_activation_run L (e#es) s=
    finite_activation_run L es (finite_activation_step L e s)"

fun finite_activation_history where
  "finite_activation_history L ev 0=activation_boot"
| "finite_activation_history L ev (Suc n)=
    finite_activation_step L (ev n) (finite_activation_history L ev n)"

lemma fenced_epoch_range:
  assumes "fenced_valid p" "fence_ranges L p"
  shows "committed_epoch p\<le>L"
proof -
  have jv: "journal_valid (fence_log p)"
    using assms(1) by (simp add: fenced_valid_def)
  obtain x where r: "journal_restore (fence_log p)=Some x"
    using journal_valid_has_restore[OF jv] by blast
  have jp: "journal_payloads (\<lambda>x. fst x\<le>L) (fence_log p)"
    using assms(2) by (simp add: fence_ranges_def)
  have "fst x\<le>L" by (rule journal_payloads_restore[OF jp r])
  then show ?thesis by (simp add: committed_epoch_def r)
qed

lemma activation_disk_range:
  assumes "activation_valid s" "activation_ranges L s"
  shows "disk_floor s i\<le>L"
proof -
  have jp: "journal_payloads (\<lambda>k. k\<le>L) (activation_logs s i)"
    using assms(2) unfolding activation_ranges_def by blast
  show ?thesis by (rule journal_payloads_restore[OF jp activation_restore[OF assms(1)]])
qed

lemma finite_disk_bound:
  "finite_valid L s \<Longrightarrow> disk_floor s i\<le>L"
  unfolding finite_valid_def by (blast intro: activation_disk_range)

lemma finite_epoch_bound:
  "finite_valid L s \<Longrightarrow> committed_epoch (engine s)\<le>L"
  unfolding finite_valid_def activation_valid_def activation_ranges_def
  by (blast intro: fenced_epoch_range)

lemma finite_active_bound:
  assumes "finite_valid L s"
  shows "reject_below (engine s) i\<le>L"
proof -
  have "reject_below (engine s) i\<le>disk_floor s i"
    using assms unfolding finite_valid_def activation_valid_def by blast
  then show ?thesis using finite_disk_bound[OF assms, of i] by arith
qed

lemma finite_boot_valid: "finite_valid L activation_boot"
  using activation_boot_valid
  by (simp add: finite_valid_def activation_ranges_def activation_boot_def
    fence_ranges_def fence_boot_def packets_bounded_def)

lemma fence_step_ranges:
  assumes v: "fenced_valid p" and r: "fence_ranges L p"
    and wire: "wire_in_range L msg"
    and room: "\<And>owner. msg=BeginHandoff owner \<Longrightarrow> committed_epoch p<L"
  shows "fence_ranges L (fence_step msg p)"
proof -
  have jp: "journal_payloads (\<lambda>x. fst x\<le>L) (fence_log p)"
    using r by (simp add: fence_ranges_def)
  have epoch: "committed_epoch p\<le>L" by (rule fenced_epoch_range[OF v r])
  show ?thesis
    using r wire epoch room
      journal_payloads_prepare[OF jp]
      journal_payloads_flush[OF jp] journal_payloads_commit[OF jp] journal_payloads_crash[OF jp]
    by (cases msg)
      (auto simp: fence_ranges_def packets_bounded_def
        del: journal_step.simps split: checkpoint_slot.splits prod.splits)
qed

lemma ranges_engine_update:
  "activation_ranges L s \<Longrightarrow> fence_ranges L p \<Longrightarrow>
    activation_ranges L (s\<lparr>engine:=p\<rparr>)"
  by (simp add: activation_ranges_def)

lemma ranges_log_update:
  "activation_ranges L s \<Longrightarrow> journal_payloads (\<lambda>k. k\<le>L) j \<Longrightarrow>
    activation_ranges L (set_activation_log i j s)"
  by (auto simp: activation_ranges_def set_activation_log_def)

lemma activation_network_ranges:
  assumes v: "activation_valid s" and r: "activation_ranges L s"
    and wire: "wire_in_range L msg"
    and room: "\<And>owner. msg=BeginHandoff owner \<Longrightarrow> committed_epoch (engine s)<L"
  shows "activation_ranges L (activation_network msg s)"
proof (cases "\<exists>k i. msg=DeliverFence k i")
  case True
  then obtain k i where msg: "msg=DeliverFence k i" by blast
  have jp: "journal_payloads (\<lambda>k. k\<le>L) (activation_logs s i)"
    using r unfolding activation_ranges_def by blast
  have bound: "max k (disk_floor s i)\<le>L"
    using wire msg activation_disk_range[OF v r, of i] by simp
  have upd: "activation_ranges L (set_activation_log i
      (journal_step (Prepare (max k (disk_floor s i))) (activation_logs s i)) s)"
    by (rule ranges_log_update[OF r journal_payloads_prepare[OF jp bound]])
  show ?thesis using msg r upd by simp
next
  case False
  have fv: "fenced_valid (engine s)" using v by (simp add: activation_valid_def)
  have fr: "fence_ranges L (engine s)" using r by (simp add: activation_ranges_def)
  have upd: "activation_ranges L (s\<lparr>engine:=fence_step msg (engine s)\<rparr>)"
    by (rule ranges_engine_update[OF r fence_step_ranges[OF fv fr wire room]])
  show ?thesis using False r upd by (cases msg; auto)
qed

lemma load_floor_ranges:
  "activation_ranges L s \<Longrightarrow> activation_ranges L (load_floor i s)"
  by (auto simp: load_floor_def activation_ranges_def fence_ranges_def)

lemma activation_step_ranges:
  assumes v: "activation_valid s" and r: "activation_ranges L s"
    and wire: "activation_in_range L e"
    and room: "\<And>owner. e=Wire (BeginHandoff owner) \<Longrightarrow> committed_epoch (engine s)<L"
  shows "activation_ranges L (activation_step e s)"
proof (cases e)
  case (Wire msg)
  show ?thesis using Wire wire room
    by (auto intro: activation_network_ranges[OF v r])
next
  case (StoreFlush i)
  have jp: "journal_payloads (\<lambda>k. k\<le>L) (activation_logs s i)"
    using r unfolding activation_ranges_def by blast
  show ?thesis using StoreFlush r ranges_log_update[OF r journal_payloads_flush[OF jp]] by simp
next
  case (StoreCommit i)
  have jp: "journal_payloads (\<lambda>k. k\<le>L) (activation_logs s i)"
    using r unfolding activation_ranges_def by blast
  show ?thesis using StoreCommit r ranges_log_update[OF r journal_payloads_commit[OF jp]]
    by (simp del: journal_step.simps split: checkpoint_slot.splits)
next
  case (ApplyFloor i)
  show ?thesis using ApplyFloor r load_floor_ranges[OF r, of i] by simp
next
  case (DevicePowerLoss i)
  have jp: "journal_payloads (\<lambda>k. k\<le>L) (activation_logs s i)"
    using r unfolding activation_ranges_def by blast
  have upd: "activation_ranges L (set_activation_log i (journal_step Crash (activation_logs s i)) s)"
    by (rule ranges_log_update[OF r journal_payloads_crash[OF jp]])
  show ?thesis using DevicePowerLoss upd
    by (simp add: activation_ranges_def del: journal_step.simps)
next
  case (DeviceRecover i)
  show ?thesis using DeviceRecover r load_floor_ranges[OF r, of i]
    by (simp add: activation_ranges_def)
qed

lemma stop_emission_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (stop_emission s)"
  by (simp add: stop_emission_def finite_valid_def activation_valid_def fenced_valid_def
    fence_core_def committed_epoch_def committed_owner_def disk_floor_def
    activation_ranges_def fence_ranges_def)

theorem finite_activation_step_valid:
  assumes v: "finite_valid L s"
  shows "finite_valid L (finite_activation_step L e s)"
proof -
  have av: "activation_valid s" and ar: "activation_ranges L s"
    using v unfolding finite_valid_def by blast+
  have ordinary: "activation_in_range L e \<Longrightarrow>
    (\<And>owner. e=Wire (BeginHandoff owner) \<Longrightarrow> committed_epoch (engine s)<L) \<Longrightarrow>
    finite_valid L (activation_step e s)"
    using activation_step_valid[OF av, of e] activation_step_ranges[OF av ar, where e=e]
    by (auto simp: finite_valid_def)
  show ?thesis using v ordinary stop_emission_valid[OF v]
    by (auto simp: finite_activation_step_def split: activation_event.splits fence_event.splits)
qed

theorem finite_activation_run_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (finite_activation_run L es s)"
  by (induction es arbitrary: s) (auto intro: finite_activation_step_valid)

theorem finite_activation_history_valid:
  "finite_valid L (finite_activation_history L ev n)"
  by (induction n) (auto intro: finite_boot_valid finite_activation_step_valid)

theorem finite_activation_mutual_exclusion:
  "\<not> (A\<in>physical_inside (engine (finite_activation_history L ev n)) \<and>
    B\<in>physical_inside (engine (finite_activation_history L ev n)))"
  using finite_activation_history_valid[of L ev n]
  unfolding finite_valid_def activation_valid_def fenced_valid_def fence_core_def
  by (metis option.inject train.distinct(1))

theorem finite_activation_all_payloads_bounded:
  "activation_ranges L (finite_activation_history L ev n) \<and>
    committed_epoch (engine (finite_activation_history L ev n))\<le>L \<and>
    (\<forall>i. disk_floor (finite_activation_history L ev n) i\<le>L \<and>
      reject_below (engine (finite_activation_history L ev n)) i\<le>L)"
  using finite_activation_history_valid[of L ev n]
    finite_epoch_bound finite_disk_bound finite_active_bound
  unfolding finite_valid_def by blast

theorem out_of_range_is_ignored:
  "\<not> activation_in_range L e \<Longrightarrow> finite_activation_step L e s=s"
  by (simp add: finite_activation_step_def)

text \<open>The bounds describe numeric payloads, not a finite bound on history
  length.  This model does not verify byte decoding, machine arithmetic,
  changes to the configured cap, backup rollback, or an emergency stop.\<close>

end
