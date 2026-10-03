theory Checkpoint_Integration
  imports Physical_Recovery Checkpoint_Journal
begin

text \<open>This is an integration-boundary counterexample, not a controller
  persistence protocol. The journal can correctly restore its latest completed
  commit while that checkpoint is too old for the plant's current occupancy.
  The controller checkpoint is the journal payload; physical occupancy is not
  overwritten by loading that payload. The examples do not establish durable
  commit-before-actuation ordering, authenticated storage, or crash recovery
  for the combined controller and plant.\<close>

definition interrupted_active_journal :: "numbered checkpoint_journal" where
  "interrupted_active_journal = journal_run
    [Prepare (machine a_leaving), Flush, Crash] (journal_boot numbered_boot)"

lemma interrupted_active_journal_valid:
  "journal_valid interrupted_active_journal"
  unfolding interrupted_active_journal_def
  by (rule journal_run_valid; rule journal_boot_valid)

lemma interrupted_active_journal_restores_old:
  "journal_restore interrupted_active_journal = Some numbered_boot"
  unfolding interrupted_active_journal_def
  by (subst flushed_write_crash_before_commit_keeps_checkpoint[OF journal_boot_valid])
    (simp add: journal_restore_def journal_boot_def selected_record_def)

definition illustrative_restore where
  "illustrative_restore j s = (case journal_restore j of
    None \<Rightarrow> s | Some checkpoint \<Rightarrow> s\<lparr>machine:=checkpoint\<rparr>)"

lemma interrupted_restoration_state:
  "illustrative_restore interrupted_active_journal a_leaving =
    a_leaving\<lparr>machine:=numbered_boot\<rparr>"
  by (simp add: illustrative_restore_def interrupted_active_journal_restores_old)

theorem intact_journal_can_lose_physical_coverage:
  "journal_valid interrupted_active_journal \<and>
    journal_restore interrupted_active_journal = Some numbered_boot \<and>
    in_zone (illustrative_restore interrupted_active_journal a_leaving) A \<and>
    \<not> zone (core (machine (illustrative_restore interrupted_active_journal a_leaving))) A"
  using interrupted_active_journal_valid interrupted_active_journal_restores_old a_leaving_facts
  by (simp add: interrupted_restoration_state numbered_boot_def boot_def)

theorem interrupted_restoration_breaks_physical_invariant:
  "\<not> physical_valid (illustrative_restore interrupted_active_journal a_leaving)"
  using intact_journal_can_lose_physical_coverage
  unfolding physical_valid_def by blast

definition committed_active_journal :: "numbered checkpoint_journal" where
  "committed_active_journal = journal_run
    [Prepare (machine a_leaving), Flush, Commit, Crash] (journal_boot numbered_boot)"

lemma committed_active_journal_valid:
  "journal_valid committed_active_journal"
  unfolding committed_active_journal_def
  by (rule journal_run_valid; rule journal_boot_valid)

lemma committed_active_journal_restores_current_example:
  "journal_restore committed_active_journal = Some (machine a_leaving)"
  unfolding committed_active_journal_def
  by (rule committed_write_survives_crash; rule journal_boot_valid)

lemma committed_restoration_state:
  "illustrative_restore committed_active_journal a_leaving = a_leaving"
  by (simp add: illustrative_restore_def committed_active_journal_restores_current_example)

theorem committed_example_preserves_physical_invariant:
  "physical_valid (illustrative_restore committed_active_journal a_leaving)"
  by (simp only: committed_restoration_state; rule a_leaving_valid)

theorem committed_example_preserves_coverage:
  "journal_valid committed_active_journal \<and>
    in_zone (illustrative_restore committed_active_journal a_leaving) A \<and>
    zone (core (machine (illustrative_restore committed_active_journal a_leaving))) A"
  using committed_active_journal_valid a_leaving_valid a_leaving_facts
  by (auto simp: committed_restoration_state physical_valid_def valid_def)

text \<open>The positive example works because this specific committed payload
  equals the controller checkpoint associated with a_leaving. There is no
  runtime test against a magically known correct checkpoint and no general
  freshness theorem. A full integration must relate durable admission records,
  emitted commands, acknowledgement handling, and the plant across crashes.\<close>

end
