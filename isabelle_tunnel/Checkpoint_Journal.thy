theory Checkpoint_Journal
  imports Main
begin

text \<open>This independent two-slot journal is an abstract crash-consistency
  specification. Flush atomically makes an entire inactive record durable.
  Commit atomically persists a selector only after that record is Complete.
  A crash may discard Partial data but preserves Complete data and the selector.
  These are storage assumptions, not conclusions about a filesystem or disk.

  The commit history is ghost specification state: recovery does not read it,
  compare against it, or assume that a runtime oracle knows the correct value.
  Rollback, corruption, dishonest storage, and identifier wraparound are outside
  this theory. It has no plant connection and no commit-before-actuation proof.
  An earlier intact checkpoint can still be too old for a physical controller.
  The seed parameter supplies the initially committed checkpoint.\<close>

datatype 'a checkpoint_slot = Empty | Partial 'a | Complete 'a

record 'a checkpoint_journal =
  journal_left :: "'a checkpoint_slot"
  journal_right :: "'a checkpoint_slot"
  journal_active :: bool
  journal_pending :: bool
  journal_commits :: "'a list"

datatype 'a journal_event = Prepare 'a | Flush | Commit | Crash

definition selected_record where
  "selected_record s = (if journal_active s then journal_right s else journal_left s)"

definition inactive_record where
  "inactive_record s = (if journal_active s then journal_left s else journal_right s)"

definition write_inactive where
  "write_inactive v s = (if journal_active s then s\<lparr>journal_left:=v\<rparr>
    else s\<lparr>journal_right:=v\<rparr>)"

fun flush_record where
  "flush_record (Partial x) = Complete x"
| "flush_record r = r"

fun discard_partial where
  "discard_partial (Partial x) = Empty"
| "discard_partial r = r"

fun record_value where
  "record_value (Complete x) = Some x"
| "record_value _ = None"

definition journal_restore where
  "journal_restore s = record_value (selected_record s)"

definition journal_boot where
  "journal_boot seed = \<lparr>journal_left=Complete seed, journal_right=Empty,
    journal_active=False, journal_pending=False, journal_commits=[seed]\<rparr>"

fun journal_step where
  "journal_step (Prepare x) s = (write_inactive (Partial x) s)\<lparr>journal_pending:=True\<rparr>"
| "journal_step Flush s = (if journal_pending s
    then write_inactive (flush_record (inactive_record s)) s else s)"
| "journal_step Commit s = (if journal_pending s then (case inactive_record s of
    Complete x \<Rightarrow> s\<lparr>journal_active:=\<not>journal_active s,
      journal_commits:=journal_commits s @ [x], journal_pending:=False\<rparr>
    | _ \<Rightarrow> s) else s)"
| "journal_step Crash s = s\<lparr>journal_left:=discard_partial (journal_left s),
    journal_right:=discard_partial (journal_right s), journal_pending:=False\<rparr>"

lemma selected_pending_update [simp]:
  "selected_record (s\<lparr>journal_pending:=p\<rparr>) = selected_record s"
  by (simp add: selected_record_def)

lemma inactive_pending_update [simp]:
  "inactive_record (s\<lparr>journal_pending:=p\<rparr>) = inactive_record s"
  by (simp add: inactive_record_def)

lemma selected_write_inactive [simp]:
  "selected_record (write_inactive v s) = selected_record s"
  by (cases "journal_active s") (simp_all add: selected_record_def write_inactive_def)

lemma inactive_write_inactive [simp]:
  "inactive_record (write_inactive v s) = v"
  by (cases "journal_active s") (simp_all add: inactive_record_def write_inactive_def)

lemma commits_write_inactive [simp]:
  "journal_commits (write_inactive v s) = journal_commits s"
  by (simp add: write_inactive_def)

lemma pending_write_inactive [simp]:
  "journal_pending (write_inactive v s) = journal_pending s"
  by (simp add: write_inactive_def)

lemma selected_switch [simp]:
  "selected_record (s\<lparr>journal_active:=\<not>journal_active s,
    journal_commits:=h\<rparr>) = inactive_record s"
  by (cases "journal_active s") (simp_all add: selected_record_def inactive_record_def)

lemma selected_discard_records [simp]:
  "selected_record (s\<lparr>journal_left:=discard_partial (journal_left s),
    journal_right:=discard_partial (journal_right s)\<rparr>) =
    discard_partial (selected_record s)"
  by (cases "journal_active s") (simp_all add: selected_record_def)

lemma selected_after_crash:
  "selected_record (journal_step Crash s) = discard_partial (selected_record s)"
  by simp

definition journal_valid where
  "journal_valid s \<longleftrightarrow> journal_commits s \<noteq> [] \<and>
    selected_record s = Complete (last (journal_commits s))"

lemma journal_boot_valid: "journal_valid (journal_boot seed)"
  by (simp add: journal_valid_def journal_boot_def selected_record_def)

lemma prepare_valid [simp]:
  "journal_valid (journal_step (Prepare x) s) = journal_valid s"
  by (simp add: journal_valid_def)

lemma flush_valid [simp]:
  "journal_valid (journal_step Flush s) = journal_valid s"
  by (cases "journal_pending s") (simp_all add: journal_valid_def)

lemma commit_valid:
  "journal_valid s \<Longrightarrow> journal_valid (journal_step Commit s)"
  by (cases "journal_pending s"; cases "inactive_record s")
    (simp_all add: journal_valid_def)

lemma crash_valid:
  "journal_valid s \<Longrightarrow> journal_valid (journal_step Crash s)"
  by (simp add: journal_valid_def)

theorem journal_step_valid:
  "journal_valid s \<Longrightarrow> journal_valid (journal_step e s)"
  by (cases e) (auto simp only: prepare_valid flush_valid intro: commit_valid crash_valid)

fun journal_history where
  "journal_history seed ev 0 = journal_boot seed"
| "journal_history seed ev (Suc n) = journal_step (ev n) (journal_history seed ev n)"

theorem journal_history_valid: "journal_valid (journal_history seed ev n)"
  by (induction n) (auto intro: journal_boot_valid journal_step_valid)

theorem selected_record_is_complete:
  "\<exists>x. selected_record (journal_history seed ev n) = Complete x"
  using journal_history_valid[of seed ev n] unfolding journal_valid_def by blast

theorem restore_is_latest_commit:
  "journal_restore (journal_history seed ev n) =
    Some (last (journal_commits (journal_history seed ev n)))"
  using journal_history_valid[of seed ev n]
  by (simp add: journal_valid_def journal_restore_def)

theorem noncommit_preserves_history:
  "e \<noteq> Commit \<Longrightarrow> journal_commits (journal_step e s) = journal_commits s"
  by (cases e) (auto split: if_splits)

theorem incomplete_record_cannot_commit:
  assumes "inactive_record s = Empty \<or> inactive_record s = Partial x"
  shows "journal_step Commit s = s"
  using assms by auto

theorem complete_commit_is_recoverable:
  assumes "journal_pending s" "inactive_record s = Complete x"
  shows "journal_restore (journal_step Commit s) = Some x \<and>
    journal_commits (journal_step Commit s) = journal_commits s @ [x]"
  using assms by (simp add: journal_restore_def)

theorem commit_without_preparation_is_ignored:
  "\<not> journal_pending s \<Longrightarrow> journal_step Commit s = s"
  by simp

theorem successful_commit_clears_preparation:
  assumes "journal_pending s" "inactive_record s = Complete x"
  shows "\<not> journal_pending (journal_step Commit s)"
  using assms by simp

theorem repeated_commit_is_idempotent:
  "journal_step Commit (journal_step Commit s) = journal_step Commit s"
  by (cases "journal_pending s"; cases "inactive_record s") simp_all

theorem crash_aborts_preparation:
  "\<not> journal_pending (journal_step Crash s)"
  by simp

theorem crash_aborted_commit_is_ignored:
  "journal_step Commit (journal_step Crash s) = journal_step Crash s"
  by simp

theorem crash_aborted_flush_is_ignored:
  "journal_step Flush (journal_step Crash s) = journal_step Crash s"
  by simp

lemma prepare_preserves_restore [simp]:
  "journal_restore (journal_step (Prepare x) s) = journal_restore s"
  by (simp add: journal_restore_def)

lemma flush_preserves_restore [simp]:
  "journal_restore (journal_step Flush s) = journal_restore s"
  by (cases "journal_pending s") (simp_all add: journal_restore_def)

lemma crash_preserves_restore [simp]:
  "journal_valid s \<Longrightarrow> journal_restore (journal_step Crash s) = journal_restore s"
  by (simp add: journal_valid_def journal_restore_def)

fun journal_run where
  "journal_run [] s = s"
| "journal_run (e#es) s = journal_run es (journal_step e s)"

lemma journal_run_valid:
  "journal_valid s \<Longrightarrow> journal_valid (journal_run es s)"
  by (induction es arbitrary: s) (auto intro: journal_step_valid)

theorem partial_write_crash_keeps_checkpoint:
  assumes "journal_valid s"
  shows "journal_restore (journal_run [Prepare x, Crash] s) = journal_restore s"
  using assms
  by (simp only: journal_run.simps crash_preserves_restore prepare_valid prepare_preserves_restore)

theorem flushed_write_crash_before_commit_keeps_checkpoint:
  assumes "journal_valid s"
  shows "journal_restore (journal_run [Prepare x, Flush, Crash] s) = journal_restore s"
  using assms
  by (simp only: journal_run.simps crash_preserves_restore prepare_valid flush_valid
    prepare_preserves_restore flush_preserves_restore)

theorem write_flush_commit_restores_new_checkpoint:
  "journal_restore (journal_run [Prepare x, Flush, Commit] s) = Some x"
  by (simp add: journal_restore_def)

theorem committed_write_survives_crash:
  assumes "journal_valid s"
  shows "journal_restore (journal_run [Prepare x, Flush, Commit, Crash] s) = Some x"
proof -
  have v: "journal_valid (journal_step Commit (journal_step Flush (journal_step (Prepare x) s)))"
    by (rule journal_step_valid; rule journal_step_valid; rule journal_step_valid; rule assms)
  show ?thesis using v
    by (simp only: journal_run.simps crash_preserves_restore;
      simp add: journal_restore_def)
qed

text \<open>Complete inactive records may survive a crash, but the crash aborts
  their pending transaction. Flush and Commit cannot activate such an orphan
  without a new Prepare/Flush cycle. Repeated Commit events cannot toggle back
  to the earlier slot. A new Prepare overwrites only the inactive slot.

  The caller can still explicitly prepare an older checkpoint payload. This
  theory prevents accidental selector replay, not semantic rollback chosen by
  a caller. The pending flag is volatile protocol state cleared on crash; the
  active selector and Complete records are assumed durable.\<close>

end
