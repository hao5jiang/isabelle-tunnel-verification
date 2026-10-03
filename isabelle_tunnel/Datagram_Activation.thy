theory Datagram_Activation
  imports Tunnel_Frame
begin

text \<open>Each external input is one complete datagram. Local operations have
  their own datatype: a remote type byte cannot request controller operations
  or acknowledgement generation. Byte validation is not authentication; the
  existing authentic history and physical observation assumptions remain.\<close>

fun packet_action where
  "packet_action p = (case packet_kind p of
    EnterPacket \<Rightarrow> Wire (DeliverEntry (packet_epoch p) (packet_train p))
  | FencePacket \<Rightarrow> Wire (DeliverFence (packet_epoch p) (packet_train p))
  | ClearPacket \<Rightarrow> Wire (ReceiveClearAck (packet_epoch p) (packet_train p)))"

datatype datagram_local = LocalBegin "train option" | LocalFlush | LocalCommit
  | LocalSend train | LocalMakeAck nat train | LocalExit train | LocalControllerCrash
  | LocalStoreFlush train | LocalStoreCommit train | LocalActivate train
  | LocalPowerLoss train | LocalRecover train

fun local_action where
  "local_action (LocalBegin owner)=Wire (BeginHandoff owner)"
| "local_action LocalFlush=Wire FlushHandoff"
| "local_action LocalCommit=Wire CommitHandoff"
| "local_action (LocalSend i)=Wire (SendEntry i)"
| "local_action (LocalMakeAck k i)=Wire (SendClearAck k i)"
| "local_action (LocalExit i)=Wire (PhysicalExit i)"
| "local_action LocalControllerCrash=Wire ControllerCrash"
| "local_action (LocalStoreFlush i)=StoreFlush i"
| "local_action (LocalStoreCommit i)=StoreCommit i"
| "local_action (LocalActivate i)=ApplyFloor i"
| "local_action (LocalPowerLoss i)=DevicePowerLoss i"
| "local_action (LocalRecover i)=DeviceRecover i"

datatype datagram_event = NetworkDatagram "nat list" | LocalOperation datagram_local

fun decode_datagram_event where
  "decode_datagram_event n L (NetworkDatagram bs)=map_option packet_action (frame_decode n L bs)"
| "decode_datagram_event n L (LocalOperation a)=Some (local_action a)"

definition datagram_step where
  "datagram_step n L e s=(case decode_datagram_event n L e of
    None \<Rightarrow> s | Some a \<Rightarrow> finite_activation_step L a s)"

fun decoded_datagram_trace where
  "decoded_datagram_trace n L []=[]"
| "decoded_datagram_trace n L (e#es)=(case decode_datagram_event n L e of
    None \<Rightarrow> decoded_datagram_trace n L es
  | Some a \<Rightarrow> a#decoded_datagram_trace n L es)"

fun datagram_run where
  "datagram_run n L [] s=s"
| "datagram_run n L (e#es) s=datagram_run n L es (datagram_step n L e s)"

fun datagram_history where
  "datagram_history n L ev 0=activation_boot"
| "datagram_history n L ev (Suc t)=datagram_step n L (ev t) (datagram_history n L ev t)"

theorem rejected_datagram_stutters:
  "frame_decode n L bs=None \<Longrightarrow> datagram_step n L (NetworkDatagram bs) s=s"
  by (simp add: datagram_step_def)

theorem accepted_datagram_exact:
  "frame_decode n L bs=Some p \<Longrightarrow>
    datagram_step n L (NetworkDatagram bs) s=finite_activation_step L (packet_action p) s"
  by (simp add: datagram_step_def)

theorem datagram_roundtrip_exact:
  assumes "frame_config n L" "packet_epoch p\<le>L"
  shows "datagram_step n L (NetworkDatagram (frame_bytes n p)) s=
    finite_activation_step L (packet_action p) s"
  by (rule accepted_datagram_exact[OF frame_decode_encode[OF assms]])

theorem network_action_classes:
  assumes "decode_datagram_event n L (NetworkDatagram bs)=Some a"
  shows "\<exists>k i. a=Wire (DeliverEntry k i) \<or> a=Wire (DeliverFence k i) \<or>
    a=Wire (ReceiveClearAck k i)"
proof -
  obtain p where "frame_decode n L bs=Some p" "a=packet_action p"
    using assms by (auto split: option.splits)
  then show ?thesis by (cases "packet_kind p"; auto)
qed

theorem network_cannot_generate_ack:
  "decode_datagram_event n L (NetworkDatagram bs)\<noteq>Some (Wire (SendClearAck k i))"
  using network_action_classes[where n=n and L=L and bs=bs and a="Wire (SendClearAck k i)"]
  by auto

theorem network_cannot_begin_or_restart:
  "decode_datagram_event n L (NetworkDatagram bs)\<noteq>Some (Wire (BeginHandoff owner)) \<and>
    decode_datagram_event n L (NetworkDatagram bs)\<noteq>Some (Wire ControllerCrash)"
  using network_action_classes[where n=n and L=L and bs=bs] by fastforce

theorem datagram_step_refines_finite:
  "datagram_step n L e s=s \<or> (\<exists>a. datagram_step n L e s=finite_activation_step L a s)"
  by (auto simp: datagram_step_def split: option.splits)

theorem datagram_run_refines_finite:
  "datagram_run n L es s=finite_activation_run L (decoded_datagram_trace n L es) s"
  by (induction es arbitrary: s) (auto simp: datagram_step_def split: option.splits)

theorem datagram_step_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (datagram_step n L e s)"
  by (auto simp: datagram_step_def intro: finite_activation_step_valid split: option.splits)

theorem datagram_run_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (datagram_run n L es s)"
  by (simp add: datagram_run_refines_finite finite_activation_run_valid)

theorem datagram_history_valid:
  "finite_valid L (datagram_history n L ev t)"
  by (induction t) (auto intro: finite_boot_valid datagram_step_valid)

theorem datagram_mutual_exclusion:
  "\<not> (A\<in>physical_inside (engine (datagram_history n L ev t)) \<and>
    B\<in>physical_inside (engine (datagram_history n L ev t)))"
  using datagram_history_valid[of L n ev t] fenced_physical_mutual_exclusion
  unfolding finite_valid_def activation_valid_def by blast

theorem datagram_exhaustion_persists:
  assumes "finite_valid L s" "committed_epoch (engine s)=L" "emission_stopped (engine s)"
  shows "committed_epoch (engine (datagram_run n L es s))=L \<and>
    emission_stopped (engine (datagram_run n L es s))"
  by (simp only: datagram_run_refines_finite; rule exhausted_run_keeps_epoch_and_stop[OF assms])

theorem accepted_ack_is_receive_only:
  assumes "frame_decode n L bs=Some p" "packet_kind p=ClearPacket"
  shows "datagram_step n L (NetworkDatagram bs) s=
    finite_activation_step L (Wire (ReceiveClearAck (packet_epoch p) (packet_train p))) s"
  using accepted_datagram_exact[OF assms(1), of s] assms(2) by simp

theorem forged_ack_not_in_history_is_ignored:
  assumes "frame_decode n L bs=Some p" "packet_kind p=ClearPacket"
    "(packet_epoch p,packet_train p)\<notin>ack_history (engine s)"
  shows "datagram_step n L (NetworkDatagram bs) s=s"
  using accepted_ack_is_receive_only[OF assms(1,2), of s] assms(3)
  by (simp add: finite_activation_step_def)

definition final_entry_packet :: tunnel_packet where
  "final_entry_packet=\<lparr>packet_kind=EnterPacket, packet_train=A, packet_epoch=1\<rparr>"

definition unsafe_prefix_step where
  "unsafe_prefix_step n L bs s=datagram_step n L (NetworkDatagram (take (6+n) bs)) s"

text \<open>Trimming a datagram to its expected prefix is an input-policy bug.
  This witness changes input acceptance, not mutual exclusion.\<close>

theorem trailing_data_is_rejected:
  "frame_decode 1 1 (frame_bytes 1 final_entry_packet @ [0])=None"
  by (rule frame_decode_rejects_length) simp

theorem trimming_trailing_data_can_actuate:
  "datagram_step 1 1 (NetworkDatagram (frame_bytes 1 final_entry_packet @ [0])) final_round_stopped=
      final_round_stopped \<and>
    A\<notin>physical_inside (engine final_round_stopped) \<and>
    A\<in>physical_inside (engine (unsafe_prefix_step 1 1
      (frame_bytes 1 final_entry_packet @ [0]) final_round_stopped))"
proof -
  have strict: "datagram_step 1 1 (NetworkDatagram (frame_bytes 1 final_entry_packet @ [0]))
      final_round_stopped=final_round_stopped"
    by (rule rejected_datagram_stutters[OF trailing_data_is_rejected])
  have trim: "take (6+(1::nat)) (frame_bytes 1 final_entry_packet @ [0])=frame_bytes 1 final_entry_packet"
    by (simp add: frame_bytes_def final_entry_packet_def)
  have config: "frame_config 1 1" by (simp add: frame_config_def epoch_capacity_def)
  have eq: "unsafe_prefix_step 1 1 (frame_bytes 1 final_entry_packet @ [0]) final_round_stopped=
      finite_activation_step 1 (Wire (DeliverEntry 1 A)) final_round_stopped"
    using datagram_roundtrip_exact[OF config, where p=final_entry_packet and s=final_round_stopped]
    by (simp add: unsafe_prefix_step_def trim final_entry_packet_def)
  show ?thesis using final_round_used_then_stopped stopped_final_round_can_still_enter
    by (simp only: strict eq; blast)
qed

text \<open>LocalOperation remains a trusted privilege boundary. This is not a
  network socket implementation, byte-stream reassembler, cryptographic identity
  check, deployment format standard, or firmware verification.\<close>

end
