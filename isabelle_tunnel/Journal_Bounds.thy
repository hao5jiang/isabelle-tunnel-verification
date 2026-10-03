theory Journal_Bounds
  imports Checkpoint_Journal
begin

text \<open>Payload restrictions are independent of crash consistency.  This
  invariant covers both slots, including uncommitted data, and the ghost commit
  history.  It does not require a particular numeric representation.\<close>

fun bounded_record :: "('a \<Rightarrow> bool) \<Rightarrow> 'a checkpoint_slot \<Rightarrow> bool" where
  "bounded_record P Empty = True"
| "bounded_record P (Partial x) = P x"
| "bounded_record P (Complete x) = P x"

definition journal_payloads where
  "journal_payloads P s \<longleftrightarrow>
    bounded_record P (journal_left s) \<and>
    bounded_record P (journal_right s) \<and>
    (\<forall>x\<in>set (journal_commits s). P x)"

lemma bounded_record_flush [simp]:
  "bounded_record P (flush_record r) = bounded_record P r"
  by (cases r) simp_all

lemma bounded_record_discard:
  "bounded_record P r \<Longrightarrow> bounded_record P (discard_partial r)"
  by (cases r) simp_all

lemma journal_payloads_pending [simp]:
  "journal_payloads P (s\<lparr>journal_pending:=b\<rparr>) = journal_payloads P s"
  by (simp add: journal_payloads_def)

lemma journal_payloads_active [simp]:
  "journal_payloads P (s\<lparr>journal_active:=b\<rparr>) = journal_payloads P s"
  by (simp add: journal_payloads_def)

lemma journal_payloads_selected:
  "journal_payloads P s \<Longrightarrow> bounded_record P (selected_record s)"
  by (auto simp: journal_payloads_def selected_record_def)

lemma journal_payloads_inactive:
  "journal_payloads P s \<Longrightarrow> bounded_record P (inactive_record s)"
  by (auto simp: journal_payloads_def inactive_record_def)

lemma journal_payloads_write_inactive:
  assumes "journal_payloads P s" "bounded_record P r"
  shows "journal_payloads P (write_inactive r s)"
  using assms by (auto simp: journal_payloads_def write_inactive_def)

lemma journal_payloads_boot [simp]:
  "journal_payloads P (journal_boot seed) = P seed"
  by (simp add: journal_payloads_def journal_boot_def)

lemma journal_payloads_prepare:
  assumes "journal_payloads P s" "P x"
  shows "journal_payloads P (journal_step (Prepare x) s)"
  using assms
  by (auto intro: journal_payloads_write_inactive)

lemma journal_payloads_flush:
  assumes "journal_payloads P s"
  shows "journal_payloads P (journal_step Flush s)"
  using assms journal_payloads_inactive[OF assms]
  by (auto intro: journal_payloads_write_inactive)

lemma journal_payloads_commit:
  assumes "journal_payloads P s"
  shows "journal_payloads P (journal_step Commit s)"
  using assms journal_payloads_inactive[OF assms]
  by (cases "journal_pending s"; cases "inactive_record s")
    (auto simp: journal_payloads_def)

lemma journal_payloads_crash:
  "journal_payloads P s \<Longrightarrow> journal_payloads P (journal_step Crash s)"
  by (auto simp: journal_payloads_def intro: bounded_record_discard)

lemma journal_payloads_restore:
  assumes "journal_payloads P s" "journal_restore s = Some x"
  shows "P x"
  using assms journal_payloads_selected[OF assms(1)]
  by (cases "selected_record s") (auto simp: journal_restore_def)

lemma journal_payloads_inactive_complete:
  assumes "journal_payloads P s" "inactive_record s = Complete x"
  shows "P x"
  using journal_payloads_inactive[OF assms(1)] assms(2) by simp

lemma journal_payloads_inactive_partial:
  assumes "journal_payloads P s" "inactive_record s = Partial x"
  shows "P x"
  using journal_payloads_inactive[OF assms(1)] assms(2) by simp

lemma journal_payloads_committed:
  "journal_payloads P s \<Longrightarrow> x \<in> set (journal_commits s) \<Longrightarrow> P x"
  by (simp add: journal_payloads_def)

fun bounded_journal_event where
  "bounded_journal_event P (Prepare x) = P x"
| "bounded_journal_event P Flush = True"
| "bounded_journal_event P Commit = True"
| "bounded_journal_event P Crash = True"

lemma journal_payloads_step:
  assumes "journal_payloads P s" "bounded_journal_event P e"
  shows "journal_payloads P (journal_step e s)"
  using assms by (cases e)
    (auto simp only: bounded_journal_event.simps
      intro: journal_payloads_prepare journal_payloads_flush
      journal_payloads_commit journal_payloads_crash)

lemma journal_payloads_run:
  assumes "journal_payloads P s" "\<forall>e\<in>set es. bounded_journal_event P e"
  shows "journal_payloads P (journal_run es s)"
  using assms
  by (induction es arbitrary: s) (auto intro: journal_payloads_step)

lemma journal_payloads_history:
  assumes "P seed" "\<forall>n. bounded_journal_event P (ev n)"
  shows "journal_payloads P (journal_history seed ev n)"
  using assms by (induction n) (auto intro: journal_payloads_step)

end
