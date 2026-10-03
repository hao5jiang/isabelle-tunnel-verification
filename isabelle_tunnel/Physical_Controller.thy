theory Physical_Controller
  imports Numbered_Controller
begin

text \<open>This is a specification of a trusted sensor and authenticated
  provenance boundary, not an implementation of cryptography. The environment
  may delay, replay, or invent receive events. Invented certificates cannot
  enter the provenance set. A restart preserves the controller checkpoint
  and increments an unbounded durable era; rollback is outside this model.\<close>

record physical_system =
  machine :: numbered
  era :: nat
  in_zone :: "train \<Rightarrow> bool"
  certificates :: "(nat \<times> packet) set"

datatype system_event = SystemRequest train | SystemPoll
  | PlantEnter train | PlantLeave train | SenseEntry train | SenseExit train
  | Receive nat packet | Restart

definition system_boot :: physical_system where
  "system_boot = \<lparr>machine=numbered_boot, era=0,
    in_zone=(\<lambda>_.False), certificates={}\<rparr>"

fun system_react :: "system_event \<Rightarrow> physical_system \<Rightarrow> physical_system" where
  "system_react (SystemRequest i) s =
    s\<lparr>machine:=numbered_react (Enqueue i) (machine s)\<rparr>"
| "system_react SystemPoll s = s\<lparr>machine:=numbered_react Schedule (machine s)\<rparr>"
| "system_react (PlantEnter i) s =
    (if stage (core (machine s))=Entering i then s\<lparr>in_zone:=(in_zone s)(i:=True)\<rparr> else s)"
| "system_react (PlantLeave i) s =
    (if stage (core (machine s))=Leaving i then s\<lparr>in_zone:=(in_zone s)(i:=False)\<rparr> else s)"
| "system_react (SenseEntry i) s =
    (if stage (core (machine s))=Entering i \<and> in_zone s i then
      s\<lparr>certificates:=insert (era s, EnterAck i (generation (machine s))) (certificates s)\<rparr>
    else s)"
| "system_react (SenseExit i) s =
    (if stage (core (machine s))=Leaving i \<and> \<not> in_zone s i then
      s\<lparr>certificates:=insert (era s, LeaveAck i (generation (machine s))) (certificates s)\<rparr>
    else s)"
| "system_react (Receive e p) s =
    (if e=era s \<and> (e,p)\<in>certificates s then
      s\<lparr>machine:=numbered_react p (machine s)\<rparr> else s)"
| "system_react Restart s = s\<lparr>era:=Suc (era s)\<rparr>"

fun system_history where
  "system_history ev 0 = system_boot"
| "system_history ev (Suc n) = system_react (ev n) (system_history ev n)"

fun certificate_bound where
  "certificate_bound g (EnterAck i k) = (k \<le> g)"
| "certificate_bound g (LeaveAck i k) = (k \<le> g)"
| "certificate_bound g _ = False"

lemma certificate_bound_Suc:
  "certificate_bound g p \<Longrightarrow> certificate_bound (Suc g) p"
  by (cases p) auto

definition physical_valid where
  "physical_valid s \<longleftrightarrow>
    valid (core (machine s)) \<and>
    (\<forall>i. in_zone s i \<longrightarrow> zone (core (machine s)) i) \<and>
    (\<forall>i. stage (core (machine s))=Occupied i \<longrightarrow> in_zone s i) \<and>
    (\<forall>e p. (e,p)\<in>certificates s \<longrightarrow> e\<le>era s \<and>
      certificate_bound (generation (machine s)) p) \<and>
    (\<forall>i. (era s, EnterAck i (generation (machine s)))\<in>certificates s \<longrightarrow>
      stage (core (machine s))=Entering i \<longrightarrow> in_zone s i) \<and>
    (\<forall>i. (era s, LeaveAck i (generation (machine s)))\<in>certificates s \<longrightarrow>
      stage (core (machine s))=Leaving i \<longrightarrow> \<not> in_zone s i) \<and>
    (\<forall>i. (era s, LeaveAck i (generation (machine s)))\<in>certificates s \<longrightarrow>
      stage (core (machine s))\<noteq>Entering i \<and> stage (core (machine s))\<noteq>Occupied i)"

lemma physical_boot_valid: "physical_valid system_boot"
  by (simp add: physical_valid_def system_boot_def numbered_boot_def boot_def valid_def)

lemma physical_request_valid:
  assumes "physical_valid s"
  shows "physical_valid (system_react (SystemRequest i) s)"
  using assms
  by (cases "stage (core (machine s))";
    auto simp: physical_valid_def numbered_react_def Let_def valid_def)

lemma physical_grant_valid:
  assumes init: "physical_valid s" and ready: "stage (core (machine s))=Ready"
    and queued: "pending (core (machine s)) i>0"
  shows "physical_valid (s\<lparr>machine:=(machine s)\<lparr>core:=grant_to i (core (machine s)),
    generation:=Suc (generation (machine s))\<rparr>\<rparr>)"
proof -
  have bounded: "certificate_bound (generation (machine s)) p"
    if "(e,p)\<in>certificates s" for e p
    using init that unfolding physical_valid_def by blast
  have raised: "\<forall>e p. (e,p)\<in>certificates s \<longrightarrow> e\<le>era s \<and>
    certificate_bound (Suc (generation (machine s))) p"
    using init unfolding physical_valid_def by (blast intro: certificate_bound_Suc)
  have no_entry: "(era s, EnterAck i (Suc (generation (machine s))))\<notin>certificates s" for i
    using bounded[where e="era s" and p="EnterAck i (Suc (generation (machine s)))"] by auto
  have no_exit: "(era s, LeaveAck i (Suc (generation (machine s))))\<notin>certificates s" for i
    using bounded[where e="era s" and p="LeaveAck i (Suc (generation (machine s)))"] by auto
  have cv: "valid (core (machine s))" using init by (simp add: physical_valid_def)
  have empty: "\<not>in_zone s A \<and> \<not>in_zone s B"
    using init ready by (auto simp: physical_valid_def valid_def train_all)
  have newvalid: "valid (grant_to i (core (machine s)))"
    using cv ready queued by (auto simp: grant_to_def valid_def)
  show ?thesis using newvalid empty raised no_entry no_exit
    by (cases i; auto simp: physical_valid_def grant_to_def train_all)
qed

lemma physical_poll_valid:
  assumes init: "physical_valid s"
  shows "physical_valid (system_react SystemPoll s)"
proof (cases "stage (core (machine s))")
  case Ready
  show ?thesis
  proof (cases "pending (core (machine s)) (priority (core (machine s)))>0")
    case True
    show ?thesis using physical_grant_valid[OF init Ready True] Ready True
      by (simp add: numbered_react_def Let_def grant_to_def)
  next
    case first: False
    show ?thesis
    proof (cases "pending (core (machine s)) (other (priority (core (machine s))))>0")
      case True
      show ?thesis using physical_grant_valid[OF init Ready True] Ready first True
        by (simp add: numbered_react_def Let_def grant_to_def)
    next
      case False
      then show ?thesis using init Ready first by (simp add: numbered_react_def Let_def)
    qed
  qed
next
  case (Entering i)
  then show ?thesis using init by (simp add: numbered_react_def Let_def)
next
  case (Occupied i)
  then show ?thesis using init
    by (cases i; auto simp: physical_valid_def numbered_react_def Let_def valid_def train_all)
next
  case (Leaving i)
  then show ?thesis using init by (simp add: numbered_react_def Let_def)
qed

lemma physical_enter_valid:
  assumes "physical_valid s"
  shows "physical_valid (system_react (PlantEnter i) s)"
proof (cases "stage (core (machine s))=Entering i")
  case False
  then show ?thesis using assms by simp
next
  case True
  have cv: "valid (core (machine s))" using assms by (simp add: physical_valid_def)
  have zi: "zone (core (machine s)) i" using cv True by (auto simp: valid_def)
  show ?thesis using assms True zi
    by (cases i; auto simp: physical_valid_def train_all)
qed

lemma physical_leave_valid:
  assumes "physical_valid s"
  shows "physical_valid (system_react (PlantLeave i) s)"
  using assms by (cases i; auto simp: physical_valid_def train_all split: if_splits)

lemma sense_entry_valid:
  assumes "physical_valid s"
  shows "physical_valid (system_react (SenseEntry i) s)"
  using assms by (cases i; auto simp: physical_valid_def train_all split: if_splits)

lemma sense_exit_valid:
  assumes "physical_valid s"
  shows "physical_valid (system_react (SenseExit i) s)"
  using assms by (cases i; auto simp: physical_valid_def train_all split: if_splits)

lemma physical_receive_valid:
  assumes "physical_valid s"
  shows "physical_valid (system_react (Receive e p) s)"
proof (cases "e=era s \<and> (e,p)\<in>certificates s")
  case False
  then show ?thesis using assms by auto
next
  case True
  have bound: "certificate_bound (generation (machine s)) p"
    using assms True by (auto simp: physical_valid_def)
  show ?thesis
  proof (cases p)
    case (Enqueue i)
    then show ?thesis using bound by simp
  next
    case Schedule
    then show ?thesis using bound by simp
  next
    case (EnterAck i k)
    show ?thesis
    proof (cases "k=generation (machine s) \<and> stage (core (machine s))=Entering i")
      case False
      then show ?thesis using assms EnterAck True by (auto simp: numbered_react_def)
    next
      case match: True
      then show ?thesis using assms EnterAck True
        by (cases i; auto simp: physical_valid_def numbered_react_def Let_def valid_def train_all)
    qed
  next
    case (LeaveAck i k)
    show ?thesis
    proof (cases "k=generation (machine s) \<and> stage (core (machine s))=Leaving i")
      case False
      then show ?thesis using assms LeaveAck True by (auto simp: numbered_react_def)
    next
      case match: True
      then show ?thesis using assms LeaveAck True
        by (cases i; auto simp: physical_valid_def numbered_react_def Let_def valid_def train_all)
    qed
  qed
qed

lemma physical_restart_valid:
  assumes "physical_valid s"
  shows "physical_valid (system_react Restart s)"
  using assms by (auto simp: physical_valid_def; force)

theorem physical_step_valid:
  "physical_valid s \<Longrightarrow> physical_valid (system_react e s)"
  by (cases e; blast intro: physical_request_valid physical_poll_valid physical_enter_valid
    physical_leave_valid sense_entry_valid sense_exit_valid physical_receive_valid physical_restart_valid)

theorem physical_history_valid: "physical_valid (system_history ev n)"
  by (induction n; simp only: system_history.simps; blast intro: physical_boot_valid physical_step_valid)

theorem physical_occupancy_covered:
  "in_zone (system_history ev n) i \<Longrightarrow> zone (core (machine (system_history ev n))) i"
  using physical_history_valid[of ev n] by (simp add: physical_valid_def)

theorem physical_mutual_exclusion:
  "\<not> (in_zone (system_history ev n) A \<and> in_zone (system_history ev n) B)"
  using physical_history_valid[of ev n]
  by (cases "stage (core (machine (system_history ev n)))")
    (auto simp: physical_valid_def valid_def train_all)

theorem physical_request_accounting:
  "received (core (machine (system_history ev n))) i =
    pending (core (machine (system_history ev n))) i + served (core (machine (system_history ev n))) i"
  using physical_history_valid[of ev n] by (simp add: physical_valid_def valid_def)

theorem unissued_packet_rejected:
  "(e,p) \<notin> certificates s \<Longrightarrow> system_react (Receive e p) s = s"
  by simp

theorem wrong_era_rejected:
  "e \<noteq> era s \<Longrightarrow> system_react (Receive e p) s = s"
  by simp

theorem restart_preserves_checkpoint:
  "machine (system_react Restart s) = machine s \<and>
    in_zone (system_react Restart s) = in_zone s \<and>
    era (system_react Restart s) = Suc (era s)"
  by simp

theorem old_era_after_restart:
  "system_react (Receive (era s) p) (system_react Restart s) = system_react Restart s"
  by simp

theorem era_monotone:
  "mono (\<lambda>n. era (system_history ev n))"
proof (rule monoI)
  fix n m :: nat
  assume "n \<le> m"
  have "era (system_history ev k) \<le> era (system_history ev (Suc k))" for k
    by (cases "ev k") (auto split: if_splits)
  then have "mono (\<lambda>k. era (system_history ev k))" by (simp add: mono_iff_le_Suc)
  then show "era (system_history ev n) \<le> era (system_history ev m)"
    using \<open>n \<le> m\<close> by (rule monoD)
qed

theorem old_era_stays_rejected:
  assumes "e < era (system_history ev n)" "n \<le> m"
  shows "system_react (Receive e p) (system_history ev m) = system_history ev m"
proof -
  have "era (system_history ev n) \<le> era (system_history ev m)"
    by (rule monoD[OF era_monotone assms(2)])
  then have "e \<noteq> era (system_history ev m)" using assms(1) by arith
  then show ?thesis by (rule wrong_era_rejected)
qed

end
