theory Receiver_Codegen
  imports Receiver_Binding Frame_Codegen
begin

text \<open>The receiver argument is trusted local ingress configuration. It
  is not read from the datagram. Numeric port tags in the test interface use
  zero for the controller and one/two for devices A/B.\<close>

fun receiver_port_tag :: "receiver_port \<Rightarrow> nat" where
  "receiver_port_tag ControllerPort = 0"
| "receiver_port_tag (DevicePort A) = 1"
| "receiver_port_tag (DevicePort B) = 2"

definition receiver_port_of :: "nat \<Rightarrow> receiver_port option" where
  "receiver_port_of tag = (if tag=0 then Some ControllerPort
    else if tag=1 then Some (DevicePort A)
    else if tag=2 then Some (DevicePort B) else None)"

lemma receiver_port_roundtrip [simp]:
  "receiver_port_of (receiver_port_tag r)=Some r"
proof (cases r)
  case ControllerPort
  then show ?thesis by (simp add: receiver_port_of_def)
next
  case (DevicePort i)
  then show ?thesis by (cases i) (simp_all add: receiver_port_of_def)
qed

lemma receiver_port_of_sound:
  "receiver_port_of tag=Some r \<Longrightarrow> receiver_port_tag r=tag"
  by (auto simp: receiver_port_of_def split: if_splits)

definition receiver_decode_numbers where
  "receiver_decode_numbers n L port bs = (case receiver_port_of port of
    None \<Rightarrow> None | Some r \<Rightarrow> map_option
      (\<lambda>p. (packet_tag (packet_kind p),train_tag (packet_train p),packet_epoch p))
      (receiver_decode n L r bs))"

lemma receiver_numeric_invalid_port:
  "receiver_port_of port=None \<Longrightarrow> receiver_decode_numbers n L port bs=None"
  by (simp add: receiver_decode_numbers_def)

lemma receiver_numeric_roundtrip:
  assumes "frame_config n L" "packet_epoch p\<le>L" "packet_destination p=r"
  shows "receiver_decode_numbers n L (receiver_port_tag r) (frame_bytes n p)=
    Some (packet_tag (packet_kind p),train_tag (packet_train p),packet_epoch p)"
proof -
  have decoded: "receiver_decode n L r (frame_bytes n p)=Some p"
    using receiver_decode_roundtrip[OF assms(1,2)] assms(3) by simp
  show ?thesis by (simp add: receiver_decode_numbers_def decoded)
qed

lemma receiver_numeric_wrong_port:
  assumes "frame_decode n L bs=Some p" "packet_destination p\<noteq>r"
  shows "receiver_decode_numbers n L (receiver_port_tag r) bs=None"
  using receiver_decode_wrong_port[OF assms]
  by (simp add: receiver_decode_numbers_def)

text \<open>Only the bound receive gate and packet encoder are exported.
  Controller transitions, socket routing and authentication are not exported
  or implemented by this module.\<close>

export_code receiver_decode_numbers frame_encode_numbers nat_of_integer integer_of_nat
  in SML module_name ReceiverGate file_prefix ReceiverGate

end
