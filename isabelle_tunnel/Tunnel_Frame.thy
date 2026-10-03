theory Tunnel_Frame
  imports Encoded_Activation
begin

text \<open>A complete frame has six header bytes followed by a configured
  little-endian epoch field. The header carries two magic bytes, a version,
  a message tag, a train tag, and the epoch-field width. Parsing checks the
  whole list; it does not silently discard a suffix. This is a format check,
  not authentication or a stream-delimiting transport implementation.\<close>

datatype wire_kind = EnterPacket | FencePacket | ClearPacket

record tunnel_packet =
  packet_kind :: wire_kind
  packet_train :: train
  packet_epoch :: nat

fun packet_tag :: "wire_kind \<Rightarrow> nat" where
  "packet_tag EnterPacket = 1"
| "packet_tag FencePacket = 2"
| "packet_tag ClearPacket = 3"

definition packet_kind_of :: "nat \<Rightarrow> wire_kind option" where
  "packet_kind_of tag = (if tag=1 then Some EnterPacket
    else if tag=2 then Some FencePacket
    else if tag=3 then Some ClearPacket else None)"

fun train_tag :: "train \<Rightarrow> nat" where
  "train_tag A = 0"
| "train_tag B = 1"

definition packet_train_of :: "nat \<Rightarrow> train option" where
  "packet_train_of tag = (if tag=0 then Some A
    else if tag=1 then Some B else None)"

definition frame_config :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "frame_config n L \<longleftrightarrow> 0<n \<and> n<256 \<and> L<epoch_capacity n"

definition frame_bytes :: "nat \<Rightarrow> tunnel_packet \<Rightarrow> nat list" where
  "frame_bytes n p =
    [84,75,1,packet_tag (packet_kind p),train_tag (packet_train p),n] @
      epoch_bytes n (packet_epoch p)"

definition frame_encode ::
  "nat \<Rightarrow> nat \<Rightarrow> tunnel_packet \<Rightarrow> nat list option" where
  "frame_encode n L p = (if frame_config n L \<and> packet_epoch p\<le>L
    then Some (frame_bytes n p) else None)"

definition frame_decode ::
  "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> tunnel_packet option" where
  "frame_decode n L bs = (case bs of
    a # b # v # tag # who # width # payload \<Rightarrow>
      (if frame_config n L \<and> a=84 \<and> b=75 \<and> v=1 \<and> width=n then
        (case packet_kind_of tag of None \<Rightarrow> None | Some kind \<Rightarrow>
         (case packet_train_of who of None \<Rightarrow> None | Some i \<Rightarrow>
          (case epoch_decode n L payload of None \<Rightarrow> None | Some k \<Rightarrow>
            Some \<lparr>packet_kind=kind,packet_train=i,packet_epoch=k\<rparr>)))
       else None)
    | _ \<Rightarrow> None)"

lemma packet_kind_tag [simp]: "packet_kind_of (packet_tag kind)=Some kind"
  by (cases kind) (simp_all add: packet_kind_of_def)

lemma packet_train_tag [simp]: "packet_train_of (train_tag i)=Some i"
  by (cases i) (simp_all add: packet_train_of_def)

lemma packet_kind_of_sound:
  "packet_kind_of tag=Some kind \<Longrightarrow> packet_tag kind=tag"
  by (auto simp: packet_kind_of_def split: if_splits)

lemma packet_train_of_sound:
  "packet_train_of tag=Some i \<Longrightarrow> train_tag i=tag"
  by (auto simp: packet_train_of_def split: if_splits)

lemma packet_tag_byte [simp]: "packet_tag kind<256"
  by (cases kind) simp_all

lemma train_tag_byte [simp]: "train_tag i<256"
  by (cases i) simp_all

lemma frame_bytes_length [simp]: "length (frame_bytes n p)=6+n"
  by (simp add: frame_bytes_def)

lemma frame_bytes_digits:
  "n<256 \<Longrightarrow> \<forall>b\<in>set (frame_bytes n p). b<256"
  using epoch_bytes_digits[of n "packet_epoch p"]
  by (simp add: frame_bytes_def)

lemma frame_decode_encode:
  assumes "frame_config n L" "packet_epoch p\<le>L"
  shows "frame_decode n L (frame_bytes n p)=Some p"
proof -
  have capacity: "L<epoch_capacity n" using assms(1)
    by (simp add: frame_config_def)
  have epoch: "epoch_decode n L (epoch_bytes n (packet_epoch p))=Some (packet_epoch p)"
    by (rule epoch_decode_encode[OF capacity assms(2)])
  show ?thesis using assms epoch
    by (cases p) (simp add: frame_decode_def frame_bytes_def)
qed

lemma frame_decode_fields:
  assumes "frame_decode n L bs=Some p"
  obtains payload where
    "frame_config n L"
    "bs=[84,75,1,packet_tag (packet_kind p),train_tag (packet_train p),n] @ payload"
    "epoch_decode n L payload=Some (packet_epoch p)"
proof -
  obtain a b v tag who width payload where
    shape: "bs=a#b#v#tag#who#width#payload"
    using assms
    by (auto simp: frame_decode_def split: list.splits)
  obtain kind i k where config: "frame_config n L"
    and magic: "a=84" "b=75" "v=1" "width=n"
    and kind: "packet_kind_of tag=Some kind"
    and train: "packet_train_of who=Some i"
    and epoch: "epoch_decode n L payload=Some k"
    and packet: "p=\<lparr>packet_kind=kind,packet_train=i,packet_epoch=k\<rparr>"
    using assms
    by (auto simp: shape frame_decode_def split: option.splits if_splits)
  have kt: "packet_tag kind=tag" by (rule packet_kind_of_sound[OF kind])
  have it: "train_tag i=who" by (rule packet_train_of_sound[OF train])
  show ?thesis
  proof (rule that[of payload])
    show "frame_config n L" by (rule config)
    show "bs=[84,75,1,packet_tag (packet_kind p),train_tag (packet_train p),n] @ payload"
      using shape magic kt it by (simp add: packet)
    show "epoch_decode n L payload=Some (packet_epoch p)"
      using epoch by (simp add: packet)
  qed
qed

lemma frame_decode_canonical:
  assumes "frame_decode n L bs=Some p"
  shows "frame_bytes n p=bs"
proof -
  obtain payload where
    bs: "bs=[84,75,1,packet_tag (packet_kind p),train_tag (packet_train p),n] @ payload"
    and ep: "epoch_decode n L payload=Some (packet_epoch p)"
    by (rule frame_decode_fields[OF assms]) blast
  show ?thesis using epoch_decode_canonical[OF ep] bs
    by (simp add: frame_bytes_def)
qed

lemma frame_decode_sound:
  assumes "frame_decode n L bs=Some p"
  shows "frame_config n L \<and> packet_epoch p\<le>L \<and>
    length bs=6+n \<and> (\<forall>b\<in>set bs. b<256)"
proof -
  obtain payload where config: "frame_config n L"
    and ep: "epoch_decode n L payload=Some (packet_epoch p)"
    by (rule frame_decode_fields[OF assms]) blast
  have width: "n<256" using config by (simp add: frame_config_def)
  have bound: "packet_epoch p\<le>L" using epoch_decode_sound[OF ep] by blast
  show ?thesis using config bound frame_decode_canonical[OF assms]
    frame_bytes_digits[OF width, of p] by auto
qed

theorem frame_decode_exact:
  "frame_decode n L bs=Some p \<longleftrightarrow>
    frame_config n L \<and> packet_epoch p\<le>L \<and> bs=frame_bytes n p"
  using frame_decode_canonical frame_decode_sound frame_decode_encode by blast

theorem frame_checked_roundtrip:
  "frame_encode n L p=Some bs \<Longrightarrow> frame_decode n L bs=Some p"
  by (auto simp: frame_encode_def intro: frame_decode_encode split: if_splits)

theorem frame_decode_reencode:
  "frame_decode n L bs=Some p \<Longrightarrow> frame_encode n L p=Some bs"
  by (simp add: frame_decode_exact frame_encode_def)

theorem frame_decode_injective:
  assumes "frame_decode n L bs=Some p" "frame_decode n L cs=Some p"
  shows "bs=cs"
  using frame_decode_canonical[OF assms(1)] frame_decode_canonical[OF assms(2)]
  by simp

theorem frame_encode_injective:
  assumes "frame_encode n L p=Some bs" "frame_encode n L q=Some bs"
  shows "p=q"
proof -
  have dp: "frame_decode n L bs=Some p" by (rule frame_checked_roundtrip[OF assms(1)])
  have dq: "frame_decode n L bs=Some q" by (rule frame_checked_roundtrip[OF assms(2)])
  show ?thesis using dp dq by simp
qed

lemma frame_encode_rejects_configuration:
  "\<not> frame_config n L \<Longrightarrow> frame_encode n L p=None"
  by (simp add: frame_encode_def)

lemma frame_encode_rejects_range:
  "L<packet_epoch p \<Longrightarrow> frame_encode n L p=None"
  by (simp add: frame_encode_def)

lemma frame_decode_rejects_configuration:
  assumes "\<not> frame_config n L"
  shows "frame_decode n L bs=None"
proof (cases "frame_decode n L bs")
  case None
  then show ?thesis by simp
next
  case (Some p)
  show ?thesis using frame_decode_sound[OF Some] assms by fastforce
qed

lemma frame_decode_rejects_length:
  assumes "length bs\<noteq>6+n"
  shows "frame_decode n L bs=None"
proof (cases "frame_decode n L bs")
  case None
  then show ?thesis by simp
next
  case (Some p)
  show ?thesis using frame_decode_sound[OF Some] assms by fastforce
qed

lemma frame_decode_rejects_nonbyte:
  assumes "b\<in>set bs" "256\<le>b"
  shows "frame_decode n L bs=None"
proof (cases "frame_decode n L bs")
  case None
  then show ?thesis by simp
next
  case (Some p)
  show ?thesis using frame_decode_sound[OF Some] assms by fastforce
qed

lemma frame_decode_rejects_suffix:
  assumes "frame_decode n L bs=Some p" "suffix\<noteq>[]"
  shows "frame_decode n L (bs@suffix)=None"
  using frame_decode_sound[OF assms(1)] assms(2)
  by (intro frame_decode_rejects_length) auto

lemma frame_decode_rejects_magic:
  "a\<noteq>84 \<or> b\<noteq>75 \<Longrightarrow>
    frame_decode n L (a#b#v#tag#who#width#payload)=None"
  by (auto simp: frame_decode_def)

lemma frame_decode_rejects_version:
  "v\<noteq>1 \<Longrightarrow>
    frame_decode n L (a#b#v#tag#who#width#payload)=None"
  by (simp add: frame_decode_def)

lemma frame_decode_rejects_width:
  "width\<noteq>n \<Longrightarrow>
    frame_decode n L (a#b#v#tag#who#width#payload)=None"
  by (simp add: frame_decode_def)

lemma frame_decode_rejects_kind:
  "packet_kind_of tag=None \<Longrightarrow>
    frame_decode n L (a#b#v#tag#who#width#payload)=None"
  by (simp add: frame_decode_def)

lemma frame_decode_rejects_train:
  "packet_train_of who=None \<Longrightarrow>
    frame_decode n L (a#b#v#tag#who#width#payload)=None"
  by (simp add: frame_decode_def split: option.splits)

lemma frame_decode_rejects_epoch:
  "epoch_decode n L payload=None \<Longrightarrow>
    frame_decode n L (a#b#v#tag#who#width#payload)=None"
  by (simp add: frame_decode_def split: option.splits)

text \<open>ClearPacket represents a received clearance acknowledgement.
  Creating such an acknowledgement remains a local guarded protocol action.
  A valid kind or train tag does not establish the sender's identity.\<close>

end
