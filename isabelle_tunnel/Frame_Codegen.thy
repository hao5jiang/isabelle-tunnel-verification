theory Frame_Codegen
  imports Datagram_Activation "HOL-Library.Code_Target_Nat"
begin

definition frame_encode_numbers where
  "frame_encode_numbers n L tag who k = (case packet_kind_of tag of
    None \<Rightarrow> None | Some kind \<Rightarrow>
      (case packet_train_of who of None \<Rightarrow> None | Some i \<Rightarrow>
        frame_encode n L \<lparr>packet_kind=kind,packet_train=i,packet_epoch=k\<rparr>))"

definition frame_decode_numbers where
  "frame_decode_numbers n L bs = map_option
    (\<lambda>p. (packet_tag (packet_kind p), train_tag (packet_train p), packet_epoch p))
    (frame_decode n L bs)"

lemma frame_encode_numbers_typed:
  "frame_encode_numbers n L (packet_tag (packet_kind p)) (train_tag (packet_train p)) (packet_epoch p)=
    frame_encode n L p"
  by (cases p) (simp add: frame_encode_numbers_def)

lemma frame_decode_numbers_roundtrip:
  assumes "frame_config n L" "packet_epoch p\<le>L"
  shows "frame_decode_numbers n L (frame_bytes n p)=
    Some (packet_tag (packet_kind p),train_tag (packet_train p),packet_epoch p)"
  by (simp add: frame_decode_numbers_def frame_decode_encode[OF assms])

lemma frame_numeric_arguments_rejected:
  "packet_kind_of tag=None \<Longrightarrow> frame_encode_numbers n L tag who k=None"
  "packet_train_of who=None \<Longrightarrow> frame_encode_numbers n L tag who k=None"
  by (simp_all add: frame_encode_numbers_def split: option.splits)

text \<open>The exported boundary uses numeric tags but checks them before
  constructing typed packets. It does not include socket I/O or the controller.
  The runtime adapter must validate external integers before nat conversion.\<close>

export_code frame_encode_numbers frame_decode_numbers nat_of_integer integer_of_nat
  in SML module_name FrameCodec file_prefix FrameCodec

end
