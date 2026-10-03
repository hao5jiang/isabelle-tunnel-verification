theory Encoded_Activation
  imports Finite_Exhaustion Epoch_Byte_Codec
begin

text \<open>This adapter validates only the epoch field. Message kind and train
  identity are typed separately. Valid encoding does not establish authenticity;
  the protocol still checks its authentic emission histories. Internal state
  remains the previous mathematical state, not a byte-level memory layout.\<close>

definition epoch_checked_successor where
  "epoch_checked_successor n L bs = (case epoch_decode n L bs of
    None \<Rightarrow> None
    | Some k \<Rightarrow> (if k<L then epoch_encode n L (Suc k) else None))"

lemma checked_successor_after_decode:
  assumes d: "epoch_decode n L bs=Some k"
  shows "epoch_checked_successor n L bs =
    (if k<L then Some (epoch_bytes n (Suc k)) else None)"
  using epoch_decode_sound[OF d]
  by (auto simp: epoch_checked_successor_def d epoch_encode_def)

theorem checked_successor_exact:
  "epoch_checked_successor n L bs=Some out \<longleftrightarrow>
    (\<exists>k. epoch_decode n L bs=Some k \<and> k<L \<and> out=epoch_bytes n (Suc k))"
  by (auto simp: epoch_checked_successor_def epoch_encode_def
    dest: epoch_decode_sound split: option.splits if_splits)

theorem checked_successor_roundtrip:
  assumes "epoch_checked_successor n L bs=Some out"
  shows "\<exists>k. epoch_decode n L bs=Some k \<and>
    epoch_decode n L out=Some (Suc k) \<and> k<Suc k \<and> Suc k\<le>L"
proof -
  obtain k where d: "epoch_decode n L bs=Some k" and bound: "k<L"
    and out: "out=epoch_bytes n (Suc k)"
    using assms checked_successor_exact by blast
  have config: "L<epoch_capacity n" using epoch_decode_sound[OF d] by blast
  have result: "epoch_decode n L out=Some (Suc k)"
    using epoch_decode_encode[OF config, of "Suc k"] bound out by simp
  show ?thesis using d bound result by auto
qed

theorem checked_successor_at_cap:
  "epoch_decode n L bs=Some L \<Longrightarrow> epoch_checked_successor n L bs=None"
  by (simp add: epoch_checked_successor_def)

theorem checked_successor_rejects_invalid:
  "epoch_decode n L bs=None \<Longrightarrow> epoch_checked_successor n L bs=None"
  by (simp add: epoch_checked_successor_def)

theorem guarded_increment_mod_identity:
  assumes "L<epoch_capacity n" "k<L"
  shows "Suc k<epoch_capacity n \<and> Suc k mod epoch_capacity n=Suc k"
proof -
  have bound: "Suc k<epoch_capacity n" using assms by arith
  then show ?thesis by simp
qed

theorem unchecked_increment_wraps:
  "Suc (epoch_capacity n - 1) mod epoch_capacity n=0"
  by (simp add: epoch_capacity_def)

datatype epoch_message = EntryField | FenceField | AckField | ReceiveField

fun field_event where
  "field_event EntryField k i=DeliverEntry k i"
| "field_event FenceField k i=DeliverFence k i"
| "field_event AckField k i=SendClearAck k i"
| "field_event ReceiveField k i=ReceiveClearAck k i"

datatype encoded_event = EncodedField epoch_message "nat list" train
  | TrustedLocal activation_event

fun decode_epoch_event where
  "decode_epoch_event n L (EncodedField kind bs i) =
    map_option (\<lambda>k. Wire (field_event kind k i)) (epoch_decode n L bs)"
| "decode_epoch_event n L (TrustedLocal e)=Some e"

definition encoded_activation_step where
  "encoded_activation_step n L e s = (case decode_epoch_event n L e of
    None \<Rightarrow> s | Some a \<Rightarrow> finite_activation_step L a s)"

fun decoded_epoch_trace where
  "decoded_epoch_trace n L []=[]"
| "decoded_epoch_trace n L (e#es) = (case decode_epoch_event n L e of
    None \<Rightarrow> decoded_epoch_trace n L es
    | Some a \<Rightarrow> a # decoded_epoch_trace n L es)"

fun encoded_activation_run where
  "encoded_activation_run n L [] s=s"
| "encoded_activation_run n L (e#es) s=
    encoded_activation_run n L es (encoded_activation_step n L e s)"

fun encoded_activation_history where
  "encoded_activation_history n L ev 0=activation_boot"
| "encoded_activation_history n L ev (Suc t)=
    encoded_activation_step n L (ev t) (encoded_activation_history n L ev t)"

theorem encoded_field_rejected_stutters:
  "epoch_decode n L bs=None \<Longrightarrow>
    encoded_activation_step n L (EncodedField kind bs i) s=s"
  by (simp add: encoded_activation_step_def)

theorem encoded_field_accepted_exact:
  "epoch_decode n L bs=Some k \<Longrightarrow>
    encoded_activation_step n L (EncodedField kind bs i) s=
    finite_activation_step L (Wire (field_event kind k i)) s"
  by (simp add: encoded_activation_step_def)

theorem encoded_field_roundtrip_exact:
  assumes "L<epoch_capacity n" "k\<le>L"
  shows "encoded_activation_step n L (EncodedField kind (epoch_bytes n k) i) s=
    finite_activation_step L (Wire (field_event kind k i)) s"
  by (rule encoded_field_accepted_exact[OF epoch_decode_encode[OF assms]])

theorem encoded_step_refines_finite:
  "encoded_activation_step n L e s=s \<or>
    (\<exists>a. encoded_activation_step n L e s=finite_activation_step L a s)"
  by (auto simp: encoded_activation_step_def split: option.splits)

theorem encoded_run_refines_finite:
  "encoded_activation_run n L es s=
    finite_activation_run L (decoded_epoch_trace n L es) s"
  by (induction es arbitrary: s)
    (auto simp: encoded_activation_step_def split: option.splits)

theorem encoded_activation_step_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (encoded_activation_step n L e s)"
  by (auto simp: encoded_activation_step_def intro: finite_activation_step_valid split: option.splits)

theorem encoded_activation_run_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (encoded_activation_run n L es s)"
  by (simp add: encoded_run_refines_finite finite_activation_run_valid)

theorem encoded_activation_history_valid:
  "finite_valid L (encoded_activation_history n L ev t)"
  by (induction t) (auto intro: finite_boot_valid encoded_activation_step_valid)

theorem encoded_activation_mutual_exclusion:
  "\<not> (A\<in>physical_inside (engine (encoded_activation_history n L ev t)) \<and>
    B\<in>physical_inside (engine (encoded_activation_history n L ev t)))"
  using encoded_activation_history_valid[of L n ev t]
    fenced_physical_mutual_exclusion
  unfolding finite_valid_def activation_valid_def by blast

theorem encoded_exhaustion_survives:
  assumes "finite_valid L s" "committed_epoch (engine s)=L" "emission_stopped (engine s)"
  shows "committed_epoch (engine (encoded_activation_run n L es s))=L \<and>
    emission_stopped (engine (encoded_activation_run n L es s))"
  by (simp only: encoded_run_refines_finite;
    rule exhausted_run_keeps_epoch_and_stop[OF assms])

theorem issued_epoch_serializes_exactly:
  assumes valid: "finite_valid L s" and config: "L<epoch_capacity n"
    and issued: "(k,i)\<in>command_history (engine s)"
  shows "epoch_encode n L k=Some (epoch_bytes n k) \<and>
    epoch_decode n L (epoch_bytes n k)=Some k"
proof -
  have bound: "k\<le>L" using valid issued
    unfolding finite_valid_def activation_ranges_def fence_ranges_def packets_bounded_def by blast
  show ?thesis using epoch_decode_encode[OF config bound]
    by (simp add: epoch_encode_def config bound)
qed

theorem controller_and_device_values_serialize:
  assumes valid: "finite_valid L s" and config: "L<epoch_capacity n"
  shows "epoch_decode n L (epoch_bytes n (committed_epoch (engine s)))=
      Some (committed_epoch (engine s)) \<and>
    epoch_decode n L (epoch_bytes n (disk_floor s i))=Some (disk_floor s i) \<and>
    epoch_decode n L (epoch_bytes n (reject_below (engine s) i))=
      Some (reject_below (engine s) i)"
  using epoch_decode_encode[OF config] finite_epoch_bound[OF valid]
    finite_disk_bound[OF valid, of i] finite_active_bound[OF valid, of i] by blast

theorem encoded_successor_matches_handoff:
  assumes config: "L<epoch_capacity n" and room: "committed_epoch (engine s)<L"
  defines "g \<equiv> committed_epoch (engine s)"
  shows "epoch_checked_successor n L (epoch_bytes n g)=Some (epoch_bytes n (Suc g)) \<and>
    inactive_record (fence_log (engine (finite_activation_step L (Wire (BeginHandoff owner)) s)))=
      Partial (Suc g,owner)"
proof -
  have bound: "g\<le>L" using room by (simp add: g_def)
  have d: "epoch_decode n L (epoch_bytes n g)=Some g"
    by (rule epoch_decode_encode[OF config bound])
  show ?thesis using checked_successor_after_decode[OF d] room
    by (simp add: finite_activation_step_def g_def)
qed

theorem encoded_successor_matches_exhaustion:
  assumes "L<epoch_capacity n" "committed_epoch (engine s)=L"
  shows "epoch_checked_successor n L (epoch_bytes n (committed_epoch (engine s)))=None \<and>
    finite_activation_step L (Wire (BeginHandoff owner)) s=stop_emission s"
  using epoch_decode_encode[OF assms(1), of L] assms(2)
  by (simp add: epoch_checked_successor_def finite_activation_step_def)

definition epoch_representable where
  "epoch_representable n L k \<longleftrightarrow>
    (\<exists>bs. epoch_encode n L k=Some bs \<and> epoch_decode n L bs=Some k)"

lemma bounded_epoch_representable:
  "L<epoch_capacity n \<Longrightarrow> k\<le>L \<Longrightarrow> epoch_representable n L k"
  using epoch_decode_encode[of L n k]
  by (auto simp: epoch_representable_def epoch_encode_def)

lemma codec_journal_payloads_mono:
  assumes "journal_payloads P j" "\<And>x. P x \<Longrightarrow> Q x"
  shows "journal_payloads Q j"
  using assms
  by (cases "journal_left j"; cases "journal_right j")
    (auto simp: journal_payloads_def)

theorem complete_storage_payloads_representable:
  assumes v: "finite_valid L s" and config: "L<epoch_capacity n"
  shows "journal_payloads (\<lambda>x. epoch_representable n L (fst x)) (fence_log (engine s)) \<and>
    (\<forall>i. journal_payloads (epoch_representable n L) (activation_logs s i))"
proof -
  have controller: "journal_payloads (\<lambda>x. fst x\<le>L) (fence_log (engine s))"
    and devices: "\<And>i. journal_payloads (\<lambda>k. k\<le>L) (activation_logs s i)"
    using v unfolding finite_valid_def activation_ranges_def fence_ranges_def by blast+
  have c: "journal_payloads (\<lambda>x. epoch_representable n L (fst x)) (fence_log (engine s))"
    by (rule codec_journal_payloads_mono[OF controller]; rule bounded_epoch_representable[OF config])
  have d: "\<And>i. journal_payloads (epoch_representable n L) (activation_logs s i)"
    by (rule codec_journal_payloads_mono[OF devices]; rule bounded_epoch_representable[OF config])
  show ?thesis using c d by blast
qed

text \<open>The following negative witness masks a malformed field before
  validation. It demonstrates an input-policy failure, not a collision.\<close>

definition wrongly_truncated_entry where
  "wrongly_truncated_entry n L bs i s = encoded_activation_step n L
    (EncodedField EntryField (epoch_bytes n (epoch_value bs)) i) s"

theorem malformed_field_is_not_a_byte:
  "epoch_decode 1 1 [257]=None \<and> epoch_encode 1 1 257=None \<and>
    epoch_decode 1 1 (epoch_bytes 1 257)=Some 1"
  by (simp add: epoch_decode_def epoch_encode_def epoch_capacity_def)

theorem malformed_field_cannot_actuate:
  "encoded_activation_step 1 1 (EncodedField EntryField [257] A) final_round_stopped=
    final_round_stopped"
  by (rule encoded_field_rejected_stutters; simp add: epoch_decode_def epoch_capacity_def)

theorem premature_truncation_changes_meaning:
  "A\<notin>physical_inside (engine final_round_stopped) \<and>
    A\<in>physical_inside (engine (wrongly_truncated_entry 1 1 [257] A final_round_stopped))"
  using final_round_used_then_stopped stopped_final_round_can_still_enter
  by (simp add: wrongly_truncated_entry_def encoded_activation_step_def
    epoch_decode_def epoch_capacity_def)

text \<open>The finite-width byte-list algorithms have executable definitions.
  No compiler, native integer type, transport framing, storage serialization,
  authentication implementation, or physical device is verified here.\<close>

end
