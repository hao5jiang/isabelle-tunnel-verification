theory Durable_Admission
  imports Checkpoint_Journal Tunnel_Knowledge
begin

text \<open>A write-ahead admission kernel. The journal stores an optional owner.
  Commands already emitted and actual occupants are separate plant/network
  state: a controller crash does not erase them. An owner change requires
  confirmed quiescence, including absence of outstanding entry commands.

  This is a specification of the required handshake, not an implementation
  of a quiescence detector. The guard reads ideal, truthful plant/network
  state atomically with Commit. A distributed implementation must establish
  an equivalent fencing/draining handshake. Commands are coalesced per train;
  delayed duplicate packets, rebooted actuators, and lossy acknowledgements
  require further refinement. No fairness or eventual recovery is assumed.
  This theory does not refine the complete numbered/bounded controller.\<close>

record admission_system =
  durable :: "train option checkpoint_journal"
  issued :: "train set"
  occupants :: "train set"

datatype admission_event =
    StageReservation "train option" | PersistReservation | CommitReservation
  | EmitEnter train | ExecuteEnter train | ExecuteLeave train | AdmissionCrash

definition admission_boot :: admission_system where
  "admission_boot = \<lparr>durable=journal_boot None, issued={}, occupants={}\<rparr>"

definition covered_by where
  "covered_by owner s \<longleftrightarrow> (\<forall>i\<in>issued s \<union> occupants s. owner = Some i)"

definition admission_valid where
  "admission_valid s \<longleftrightarrow> journal_valid (durable s) \<and>
    (\<exists>owner. journal_restore (durable s) = Some owner \<and> covered_by owner s)"

definition quiescent where
  "quiescent s \<longleftrightarrow> issued s = {} \<and> occupants s = {}"

definition handoff_allowed where
  "handoff_allowed owner s \<longleftrightarrow>
    journal_restore (durable s) = Some owner \<or> quiescent s"

fun admission_step where
  "admission_step (StageReservation owner) s =
    s\<lparr>durable:=journal_step (Prepare owner) (durable s)\<rparr>"
| "admission_step PersistReservation s =
    s\<lparr>durable:=journal_step Flush (durable s)\<rparr>"
| "admission_step CommitReservation s =
    (case inactive_record (durable s) of Complete owner \<Rightarrow>
      (if handoff_allowed owner s
       then s\<lparr>durable:=journal_step Commit (durable s)\<rparr> else s)
    | _ \<Rightarrow> s)"
| "admission_step (EmitEnter i) s =
    (if journal_restore (durable s) = Some (Some i)
     then s\<lparr>issued:=insert i (issued s)\<rparr> else s)"
| "admission_step (ExecuteEnter i) s =
    (if i \<in> issued s
     then s\<lparr>issued:=issued s - {i}, occupants:=insert i (occupants s)\<rparr>
     else s)"
| "admission_step (ExecuteLeave i) s = s\<lparr>occupants:=occupants s - {i}\<rparr>"
| "admission_step AdmissionCrash s = s\<lparr>durable:=journal_step Crash (durable s)\<rparr>"

lemma admission_boot_valid: "admission_valid admission_boot"
  by (simp add: admission_valid_def admission_boot_def journal_boot_valid
    journal_valid_def journal_restore_def selected_record_def journal_boot_def covered_by_def)

lemma journal_valid_has_restore:
  "journal_valid j \<Longrightarrow> \<exists>x. journal_restore j = Some x"
  by (auto simp: journal_valid_def journal_restore_def)

lemma durable_update_covered [simp]:
  "covered_by owner (s\<lparr>durable:=j\<rparr>) = covered_by owner s"
  by (simp add: covered_by_def)

lemma allowed_owner_covers:
  "admission_valid s \<Longrightarrow> handoff_allowed owner s \<Longrightarrow> covered_by owner s"
  by (auto simp: admission_valid_def handoff_allowed_def quiescent_def covered_by_def)

lemma admission_commit_valid:
  assumes v: "admission_valid s"
  shows "admission_valid (admission_step CommitReservation s)"
proof (cases "inactive_record (durable s)")
  case Empty
  then show ?thesis using v by simp
next
  case (Partial owner)
  then show ?thesis using v by simp
next
  case (Complete owner)
  show ?thesis
  proof (cases "handoff_allowed owner s \<and> journal_pending (durable s)")
    case True
    have cov: "covered_by owner s" using allowed_owner_covers v True by blast
    have jv: "journal_valid (journal_step Commit (durable s))"
      using v commit_valid unfolding admission_valid_def by blast
    have restored: "journal_restore (journal_step Commit (durable s)) = Some owner"
      using complete_commit_is_recoverable[where s="durable s" and x=owner]
        Complete True by blast
    show ?thesis using Complete True cov jv restored
      by (simp only: admission_step.simps checkpoint_slot.case if_True;
          auto simp: admission_valid_def)
  next
    case False
    show ?thesis
    proof (cases "handoff_allowed owner s")
      case True
      have np: "\<not> journal_pending (durable s)" using False True by blast
      show ?thesis using Complete True np v by simp
    next
      case False
      show ?thesis using Complete False v by simp
    qed
  qed
qed

theorem admission_step_valid:
  assumes "admission_valid s"
  shows "admission_valid (admission_step e s)"
proof (cases e)
  case (StageReservation owner)
  then show ?thesis using assms
    by (simp add: admission_valid_def del: journal_step.simps)
next
  case PersistReservation
  then show ?thesis using assms
    by (simp add: admission_valid_def del: journal_step.simps)
next
  case CommitReservation
  then show ?thesis using admission_commit_valid[OF assms] by simp
next
  case (EmitEnter i)
  then show ?thesis using assms
    by (auto simp: admission_valid_def covered_by_def)
next
  case (ExecuteEnter i)
  then show ?thesis using assms
    by (auto simp: admission_valid_def covered_by_def ball_Un; metis bspec option.inject)
next
  case (ExecuteLeave i)
  then show ?thesis using assms
    by (auto simp: admission_valid_def covered_by_def)
next
  case AdmissionCrash
  then show ?thesis using assms crash_valid[where s="durable s"]
    by (simp add: admission_valid_def del: journal_step.simps)
qed

fun admission_history where
  "admission_history ev 0 = admission_boot"
| "admission_history ev (Suc n) = admission_step (ev n) (admission_history ev n)"

theorem admission_history_valid: "admission_valid (admission_history ev n)"
  by (induction n) (auto intro: admission_boot_valid admission_step_valid)

theorem durable_occupancy_coverage:
  assumes "admission_valid s" "i \<in> issued s \<union> occupants s"
  shows "journal_restore (durable s) = Some (Some i)"
  using assms by (auto simp: admission_valid_def covered_by_def)

theorem durable_mutual_exclusion:
  "admission_valid s \<Longrightarrow> \<not> (A \<in> occupants s \<and> B \<in> occupants s)"
  using durable_occupancy_coverage[where s=s and i=A]
    durable_occupancy_coverage[where s=s and i=B] by auto

theorem all_interleavings_safe:
  "\<not> (A \<in> occupants (admission_history ev n) \<and>
         B \<in> occupants (admission_history ev n))"
  using admission_history_valid durable_mutual_exclusion by blast

theorem emit_requires_committed_owner:
  "journal_restore (durable s) \<noteq> Some (Some i) \<Longrightarrow>
   admission_step (EmitEnter i) s = s"
  by simp

theorem crash_preserves_inflight_and_physical_state:
  "issued (admission_step AdmissionCrash s) = issued s \<and>
   occupants (admission_step AdmissionCrash s) = occupants s"
  by simp

theorem inflight_entry_survives_crash:
  "i \<in> issued s \<Longrightarrow>
   i \<in> occupants (admission_step (ExecuteEnter i) (admission_step AdmissionCrash s))"
  by simp

theorem busy_handoff_blocked:
  assumes "\<not> quiescent s" "inactive_record (durable s) = Complete owner"
    "journal_restore (durable s) \<noteq> Some owner"
  shows "admission_step CommitReservation s = s"
  using assms by (simp add: handoff_allowed_def)

theorem quiescent_handoff_commits:
  assumes "quiescent s" "journal_pending (durable s)"
    "inactive_record (durable s) = Complete owner"
  shows "journal_restore (durable (admission_step CommitReservation s)) = Some owner"
  using assms complete_commit_is_recoverable[of "durable s" owner]
  by (simp add: handoff_allowed_def)

fun admission_run where
  "admission_run [] s = s"
| "admission_run (e#es) s = admission_run es (admission_step e s)"

lemma admission_run_valid:
  "admission_valid s \<Longrightarrow> admission_valid (admission_run es s)"
  by (induction es arbitrary: s) (auto intro: admission_step_valid)

definition queued_a where
  "queued_a = admission_run [StageReservation (Some A), PersistReservation,
    CommitReservation, EmitEnter A] admission_boot"

lemma queued_a_facts:
  "admission_valid queued_a \<and> issued queued_a = {A} \<and>
    occupants queued_a = {} \<and> journal_restore (durable queued_a) = Some (Some A)"
  using admission_run_valid[OF admission_boot_valid,
    of "[StageReservation (Some A), PersistReservation, CommitReservation, EmitEnter A]"]
  by (simp add: queued_a_def admission_boot_def handoff_allowed_def quiescent_def
    journal_restore_def selected_record_def inactive_record_def write_inactive_def journal_boot_def)

definition recovery_handoff where
  "recovery_handoff = admission_run [AdmissionCrash, ExecuteEnter A,
    StageReservation (Some B), PersistReservation, CommitReservation,
    ExecuteLeave A, CommitReservation, EmitEnter B, ExecuteEnter B] queued_a"

theorem recovery_handoff_safe_and_completes:
  "admission_valid recovery_handoff \<and> occupants recovery_handoff = {B} \<and>
    issued recovery_handoff = {} \<and>
    journal_restore (durable recovery_handoff) = Some (Some B)"
  using admission_run_valid[of queued_a
    "[AdmissionCrash, ExecuteEnter A, StageReservation (Some B), PersistReservation,
      CommitReservation, ExecuteLeave A, CommitReservation, EmitEnter B, ExecuteEnter B]"]
    queued_a_facts
  by (simp add: recovery_handoff_def queued_a_def admission_boot_def handoff_allowed_def
    quiescent_def journal_restore_def selected_record_def inactive_record_def
    write_inactive_def journal_boot_def)

text \<open>Negative example: emitting an entry before committing its owner is
  an explicitly faulty transition outside admission_step. The journal remains
  internally valid after the crash, but it no longer covers the occupant.\<close>

definition premature_entry where
  "premature_entry = admission_step (ExecuteEnter A)
    (admission_step AdmissionCrash
      ((admission_step PersistReservation
        (admission_step (StageReservation (Some A)) admission_boot))\<lparr>issued:={A}\<rparr>))"

theorem premature_emission_breaks_coverage:
  "journal_valid (durable premature_entry) \<and>
    journal_restore (durable premature_entry) = Some None \<and>
    A \<in> occupants premature_entry \<and> \<not> admission_valid premature_entry"
  by (simp add: premature_entry_def admission_boot_def admission_valid_def covered_by_def
    journal_valid_def journal_restore_def selected_record_def inactive_record_def
    write_inactive_def journal_boot_def)

definition queue_blind_handoff where
  "queue_blind_handoff = (let s = admission_run
    [StageReservation (Some B), PersistReservation] queued_a
    in s\<lparr>durable:=journal_step Commit (durable s)\<rparr>)"

theorem ignoring_queued_command_can_collide:
  "occupants queue_blind_handoff = {} \<and>
    occupants (admission_run [EmitEnter B, ExecuteEnter A, ExecuteEnter B]
      queue_blind_handoff) = {A,B}"
  by (simp add: queue_blind_handoff_def queued_a_def admission_boot_def
    handoff_allowed_def quiescent_def journal_restore_def selected_record_def
    inactive_record_def write_inactive_def journal_boot_def Let_def insert_commute)

end
