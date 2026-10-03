theory Receiver_Binding
  imports Datagram_Activation
begin

text \<open>The ingress port is local configuration, not a field supplied by
  the datagram. A device port receives only commands addressed to that device;
  acknowledgements are received at the controller port. This binding is not
  cryptographic authentication. The existing authentic-history and physical
  observation assumptions remain part of the underlying protocol model.\<close>

datatype receiver_port = ControllerPort | DevicePort train

fun packet_destination where
  "packet_destination p = (case packet_kind p of
    EnterPacket \<Rightarrow> DevicePort (packet_train p)
  | FencePacket \<Rightarrow> DevicePort (packet_train p)
  | ClearPacket \<Rightarrow> ControllerPort)"

definition receiver_decode where
  "receiver_decode n L r bs = (case frame_decode n L bs of
    None \<Rightarrow> None
  | Some p \<Rightarrow> if packet_destination p=r then Some p else None)"

definition receiver_action where
  "receiver_action n L r bs = map_option packet_action (receiver_decode n L r bs)"

datatype receiver_event = ReceivedOn receiver_port "nat list"
  | ReceiverLocal datagram_local

fun decode_receiver_event where
  "decode_receiver_event n L (ReceivedOn r bs)=receiver_action n L r bs"
| "decode_receiver_event n L (ReceiverLocal a)=Some (local_action a)"

definition receiver_step where
  "receiver_step n L e s=(case decode_receiver_event n L e of
    None \<Rightarrow> s | Some a \<Rightarrow> finite_activation_step L a s)"

fun receiver_trace where
  "receiver_trace n L []=[]"
| "receiver_trace n L (e#es)=(case decode_receiver_event n L e of
    None \<Rightarrow> receiver_trace n L es
  | Some a \<Rightarrow> a#receiver_trace n L es)"

fun receiver_run where
  "receiver_run n L [] s=s"
| "receiver_run n L (e#es) s=receiver_run n L es (receiver_step n L e s)"

fun receiver_history where
  "receiver_history n L ev 0=activation_boot"
| "receiver_history n L ev (Suc t)=receiver_step n L (ev t) (receiver_history n L ev t)"

theorem receiver_decode_exact:
  "receiver_decode n L r bs=Some p \<longleftrightarrow>
    frame_decode n L bs=Some p \<and> packet_destination p=r"
  by (auto simp: receiver_decode_def split: option.splits if_splits)

theorem receiver_decode_correct_port:
  assumes "frame_decode n L bs=Some p"
  shows "receiver_decode n L (packet_destination p) bs=Some p"
  using assms by (simp add: receiver_decode_def)

theorem receiver_decode_roundtrip:
  assumes "frame_config n L" "packet_epoch p\<le>L"
  shows "receiver_decode n L (packet_destination p) (frame_bytes n p)=Some p"
  by (rule receiver_decode_correct_port[OF frame_decode_encode[OF assms]])

theorem receiver_decode_wrong_port:
  assumes "frame_decode n L bs=Some p" "packet_destination p\<noteq>r"
  shows "receiver_decode n L r bs=None"
  using assms by (simp add: receiver_decode_def)

theorem receiver_decode_unique_port:
  assumes "receiver_decode n L r bs=Some p" "receiver_decode n L r' bs=Some q"
  shows "p=q \<and> r=r'"
  using assms by (auto simp: receiver_decode_exact)

theorem receiver_decode_invalid_frame:
  "frame_decode n L bs=None \<Longrightarrow> receiver_decode n L r bs=None"
  by (simp add: receiver_decode_def)

theorem receiver_decode_invalid_config:
  "\<not>frame_config n L \<Longrightarrow> receiver_decode n L r bs=None"
  using frame_decode_rejects_configuration[where n=n and L=L and bs=bs]
  by (simp add: receiver_decode_def)

theorem receiver_action_exact:
  "receiver_action n L r bs=Some a \<longleftrightarrow>
    (\<exists>p. frame_decode n L bs=Some p \<and> packet_destination p=r \<and> a=packet_action p)"
  by (auto simp: receiver_action_def receiver_decode_exact split: option.splits)

theorem device_port_actions:
  assumes "receiver_action n L (DevicePort i) bs=Some a"
  shows "\<exists>k. a=Wire (DeliverEntry k i) \<or> a=Wire (DeliverFence k i)"
proof -
  obtain p where decoded: "frame_decode n L bs=Some p"
    and dest: "packet_destination p=DevicePort i" and act: "a=packet_action p"
    using assms by (simp only: receiver_action_exact; blast)
  show ?thesis using dest act by (cases "packet_kind p"; auto)
qed

theorem device_port_cannot_receive_ack:
  "receiver_action n L (DevicePort i) bs\<noteq>Some (Wire (ReceiveClearAck k j))"
  using device_port_actions[where n=n and L=L and i=i and bs=bs
    and a="Wire (ReceiveClearAck k j)"] by auto

theorem controller_port_actions:
  assumes "receiver_action n L ControllerPort bs=Some a"
  shows "\<exists>k i. a=Wire (ReceiveClearAck k i)"
proof -
  obtain p where decoded: "frame_decode n L bs=Some p"
    and dest: "packet_destination p=ControllerPort" and act: "a=packet_action p"
    using assms by (simp only: receiver_action_exact; blast)
  show ?thesis using dest act by (cases "packet_kind p"; auto)
qed

theorem controller_port_cannot_deliver_command:
  "receiver_action n L ControllerPort bs\<noteq>Some (Wire (DeliverEntry k i)) \<and>
    receiver_action n L ControllerPort bs\<noteq>Some (Wire (DeliverFence k i))"
  using controller_port_actions[where n=n and L=L and bs=bs]
  by fastforce

theorem receiver_network_cannot_generate_ack:
  "receiver_action n L r bs\<noteq>Some (Wire (SendClearAck k i))"
proof (cases r)
  case ControllerPort
  then show ?thesis
    using controller_port_actions[where n=n and L=L and bs=bs and a="Wire (SendClearAck k i)"]
    by auto
next
  case (DevicePort j)
  then show ?thesis
    using device_port_actions[where n=n and L=L and i=j and bs=bs and a="Wire (SendClearAck k i)"]
    by auto
qed

theorem receiver_local_exact:
  "receiver_step n L (ReceiverLocal a) s=finite_activation_step L (local_action a) s"
  by (simp add: receiver_step_def)

theorem receiver_local_ignores_frame_configuration:
  "receiver_step n L (ReceiverLocal a) s=receiver_step n' L (ReceiverLocal a) s"
  by (simp add: receiver_local_exact)

theorem receiver_rejection_stutters:
  "receiver_decode n L r bs=None \<Longrightarrow> receiver_step n L (ReceivedOn r bs) s=s"
  by (simp add: receiver_step_def receiver_action_def)

theorem receiver_acceptance_exact:
  "receiver_decode n L r bs=Some p \<Longrightarrow>
    receiver_step n L (ReceivedOn r bs) s=finite_activation_step L (packet_action p) s"
  by (simp add: receiver_step_def receiver_action_def)

theorem receiver_correct_port_matches_datagram:
  assumes "frame_decode n L bs=Some p"
  shows "receiver_step n L (ReceivedOn (packet_destination p) bs) s=
    datagram_step n L (NetworkDatagram bs) s"
  using receiver_acceptance_exact[OF receiver_decode_correct_port[OF assms], of s]
    accepted_datagram_exact[OF assms, of s] by simp

theorem receiver_wrong_port_stutters:
  assumes "frame_decode n L bs=Some p" "packet_destination p\<noteq>r"
  shows "receiver_step n L (ReceivedOn r bs) s=s"
  by (rule receiver_rejection_stutters[OF receiver_decode_wrong_port[OF assms]])

theorem receiver_roundtrip_exact:
  assumes "frame_config n L" "packet_epoch p\<le>L"
  shows "receiver_step n L (ReceivedOn (packet_destination p) (frame_bytes n p)) s=
    finite_activation_step L (packet_action p) s"
  by (rule receiver_acceptance_exact[OF receiver_decode_roundtrip[OF assms]])

theorem receiver_step_refines_finite:
  "receiver_step n L e s=s \<or> (\<exists>a. receiver_step n L e s=finite_activation_step L a s)"
  by (auto simp: receiver_step_def split: option.splits)

theorem receiver_run_refines_finite:
  "receiver_run n L es s=finite_activation_run L (receiver_trace n L es) s"
  by (induction es arbitrary: s) (auto simp: receiver_step_def split: option.splits)

theorem receiver_step_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (receiver_step n L e s)"
  by (auto simp: receiver_step_def intro: finite_activation_step_valid split: option.splits)

theorem receiver_run_valid:
  "finite_valid L s \<Longrightarrow> finite_valid L (receiver_run n L es s)"
  by (simp add: receiver_run_refines_finite finite_activation_run_valid)

theorem receiver_history_valid:
  "finite_valid L (receiver_history n L ev t)"
  by (induction t) (auto intro: finite_boot_valid receiver_step_valid)

theorem receiver_mutual_exclusion:
  "\<not> (A\<in>physical_inside (engine (receiver_history n L ev t)) \<and>
    B\<in>physical_inside (engine (receiver_history n L ev t)))"
  using receiver_history_valid[of L n ev t] fenced_physical_mutual_exclusion
  unfolding finite_valid_def activation_valid_def by blast

theorem receiver_exhaustion_persists:
  assumes "finite_valid L s" "committed_epoch (engine s)=L" "emission_stopped (engine s)"
  shows "committed_epoch (engine (receiver_run n L es s))=L \<and>
    emission_stopped (engine (receiver_run n L es s))"
  by (simp only: receiver_run_refines_finite; rule exhausted_run_keeps_epoch_and_stop[OF assms])

text \<open>An unbound ingress ignores the local receiving endpoint. The
  following witness compares that old dispatch rule with the receiver-bound
  rule: the A command delivered on B's port is rejected only by the latter.
  This is a target-binding failure, not a collision counterexample.\<close>

theorem wrong_device_port_rejects_final_entry:
  "receiver_step 1 1 (ReceivedOn (DevicePort B) (frame_bytes 1 final_entry_packet))
    final_round_stopped=final_round_stopped"
proof -
  have config: "frame_config 1 1" by (simp add: frame_config_def epoch_capacity_def)
  have bound: "packet_epoch final_entry_packet\<le>1" by (simp add: final_entry_packet_def)
  have different: "packet_destination final_entry_packet\<noteq>DevicePort B"
    by (simp add: final_entry_packet_def)
  show ?thesis
    by (rule receiver_wrong_port_stutters[OF frame_decode_encode[OF config bound] different])
qed

theorem ignoring_receiver_port_can_actuate_other_device:
  "receiver_step 1 1 (ReceivedOn (DevicePort B) (frame_bytes 1 final_entry_packet))
      final_round_stopped=final_round_stopped \<and>
    A\<notin>physical_inside (engine final_round_stopped) \<and>
    A\<in>physical_inside (engine
      (datagram_step 1 1 (NetworkDatagram (frame_bytes 1 final_entry_packet)) final_round_stopped))"
proof -
  have config: "frame_config 1 1" by (simp add: frame_config_def epoch_capacity_def)
  have unbound: "datagram_step 1 1 (NetworkDatagram (frame_bytes 1 final_entry_packet))
      final_round_stopped=finite_activation_step 1 (Wire (DeliverEntry 1 A)) final_round_stopped"
    using datagram_roundtrip_exact[OF config, where p=final_entry_packet and s=final_round_stopped]
    by (simp add: final_entry_packet_def)
  have empty: "A\<notin>physical_inside (engine final_round_stopped)"
    using final_round_used_then_stopped by simp
  have actuated: "A\<in>physical_inside (engine
      (datagram_step 1 1 (NetworkDatagram (frame_bytes 1 final_entry_packet)) final_round_stopped))"
    using stopped_final_round_can_still_enter by (simp only: unbound)
  show ?thesis using wrong_device_port_rejects_final_entry empty actuated by simp
qed

text \<open>The adapter assumes a trustworthy association between the local
  socket or device endpoint and receiver_port. It does not establish physical
  wiring, socket ownership, sender identity, cryptographic keys, or firmware
  behavior. A ClearPacket train field is a claimed source label, not proof of
  its sender. ReceiverLocal is a separate trusted interface and is not
  restricted by receiver_port. Rejected packets leave protocol state unchanged; logging and rate
  limits are outside this model. Local operations retain their existing rules,
  including when the frame configuration is invalid.\<close>

end
