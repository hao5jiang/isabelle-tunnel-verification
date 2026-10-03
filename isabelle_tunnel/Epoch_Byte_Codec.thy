theory Epoch_Byte_Codec
  imports Main
begin

text \<open>A checked, fixed-width, little-endian representation of epoch
  identifiers. Bytes are modelled by natural numbers with an explicit bound.
  This theory does not assert correctness of machine instructions, buffers,
  transport framing, or a storage implementation.\<close>

fun epoch_bytes :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "epoch_bytes 0 k = []"
| "epoch_bytes (Suc n) k = (k mod 256) # epoch_bytes n (k div 256)"

fun epoch_value :: "nat list \<Rightarrow> nat" where
  "epoch_value [] = 0"
| "epoch_value (b # bs) = b + 256 * epoch_value bs"

definition epoch_capacity :: "nat \<Rightarrow> nat" where
  "epoch_capacity n = 256 ^ n"

definition epoch_encode :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list option" where
  "epoch_encode n L k =
    (if L < epoch_capacity n \<and> k \<le> L
     then Some (epoch_bytes n k) else None)"

definition epoch_decode :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat option" where
  "epoch_decode n L bs =
    (if L < epoch_capacity n \<and> length bs = n \<and>
        (\<forall>b\<in>set bs. b < 256) \<and> epoch_value bs \<le> L
     then Some (epoch_value bs) else None)"

lemma epoch_capacity_positive [simp]: "0 < epoch_capacity n"
  by (simp add: epoch_capacity_def)

lemma epoch_bytes_length [simp]: "length (epoch_bytes n k) = n"
  by (induction n arbitrary: k) simp_all

lemma epoch_bytes_digits: "\<forall>b\<in>set (epoch_bytes n k). b < 256"
  by (induction n arbitrary: k) auto

lemma epoch_value_bound:
  assumes "\<forall>b\<in>set bs. b < 256"
  shows "epoch_value bs < epoch_capacity (length bs)"
  using assms
proof (induction bs)
  case Nil
  then show ?case by (simp add: epoch_capacity_def)
next
  case (Cons b bs)
  have digit: "b < 256" using Cons.prems by simp
  have tail: "epoch_value bs < epoch_capacity (length bs)"
    using Cons.IH Cons.prems by auto
  show ?case
    using digit tail
    by (simp add: epoch_capacity_def; arith)
qed

lemma epoch_value_bytes:
  assumes "k < epoch_capacity n"
  shows "epoch_value (epoch_bytes n k) = k"
  using assms
proof (induction n arbitrary: k)
  case 0
  then show ?case by (simp add: epoch_capacity_def)
next
  case (Suc n)
  have quotient: "k div 256 < epoch_capacity n"
    using Suc.prems
    by (simp add: epoch_capacity_def div_less_iff_less_mult mult.commute)
  have tail: "epoch_value (epoch_bytes n (k div 256)) = k div 256"
    by (rule Suc.IH[OF quotient])
  show ?case
    by (simp only: epoch_bytes.simps epoch_value.simps tail mod_mult_div_eq)
qed

lemma epoch_bytes_value:
  assumes "\<forall>b\<in>set bs. b < 256"
  shows "epoch_bytes (length bs) (epoch_value bs) = bs"
  using assms
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have digit: "b < 256" using Cons.prems by simp
  have tail: "epoch_bytes (length bs) (epoch_value bs) = bs"
    using Cons.IH Cons.prems by auto
  show ?case by (simp add: digit tail)
qed

lemma epoch_encode_accepted:
  assumes "epoch_encode n L k = Some bs"
  shows "L < epoch_capacity n" "k \<le> L" "bs = epoch_bytes n k"
  using assms by (auto simp: epoch_encode_def split: if_splits)

lemma epoch_encode_roundtrip:
  assumes "L < epoch_capacity n" "k \<le> L"
  shows "epoch_decode n L (epoch_bytes n k) = Some k"
proof -
  have bound: "k < epoch_capacity n" using assms by arith
  show ?thesis
    using assms epoch_bytes_digits[of n k] epoch_value_bytes[OF bound]
    by (simp add: epoch_decode_def)
qed

lemma epoch_checked_roundtrip:
  assumes "epoch_encode n L k = Some bs"
  shows "epoch_decode n L bs = Some k"
  using epoch_encode_accepted[OF assms]
    epoch_encode_roundtrip[of L n k]
  by simp

lemmas epoch_decode_encode = epoch_encode_roundtrip

lemma epoch_decode_accepted:
  assumes "epoch_decode n L bs = Some k"
  shows "L < epoch_capacity n" "length bs = n"
    "\<forall>b\<in>set bs. b < 256" "epoch_value bs = k" "k \<le> L"
  using assms by (auto simp: epoch_decode_def split: if_splits)

lemma epoch_decode_sound:
  assumes "epoch_decode n L bs = Some k"
  shows "L < epoch_capacity n \<and> k \<le> L \<and> length bs = n \<and>
    (\<forall>b\<in>set bs. b < 256) \<and> epoch_value bs = k"
  using epoch_decode_accepted[OF assms] by simp

lemma epoch_decode_canonical:
  assumes "epoch_decode n L bs = Some k"
  shows "epoch_bytes n k = bs"
  using epoch_decode_accepted[OF assms] epoch_bytes_value[of bs]
  by simp

lemma epoch_decode_reencode:
  assumes "epoch_decode n L bs = Some k"
  shows "epoch_encode n L k = Some bs"
  using epoch_decode_accepted[OF assms] epoch_decode_canonical[OF assms]
  by (simp add: epoch_encode_def)

lemma epoch_decode_injective:
  assumes "epoch_decode n L bs = Some k" "epoch_decode n L cs = Some k"
  shows "bs = cs"
  using epoch_decode_canonical[OF assms(1)]
    epoch_decode_canonical[OF assms(2)] by simp

lemma epoch_encode_rejects_range:
  assumes "L < k"
  shows "epoch_encode n L k = None"
  using assms by (simp add: epoch_encode_def)

lemma epoch_encode_rejects_configuration:
  assumes "epoch_capacity n \<le> L"
  shows "epoch_encode n L k = None"
  using assms by (simp add: epoch_encode_def)

lemma epoch_decode_rejects_length:
  assumes "length bs \<noteq> n"
  shows "epoch_decode n L bs = None"
  using assms by (simp add: epoch_decode_def)

lemma epoch_decode_rejects_nonbyte:
  assumes "b \<in> set bs" "256 \<le> b"
  shows "epoch_decode n L bs = None"
proof -
  have not_digits: "\<not> (\<forall>b\<in>set bs. b < 256)"
    using assms by fastforce
  show ?thesis by (simp add: epoch_decode_def not_digits)
qed

lemma epoch_decode_rejects_range:
  assumes "L < epoch_value bs"
  shows "epoch_decode n L bs = None"
  using assms by (simp add: epoch_decode_def)

lemma epoch_decode_rejects_configuration:
  assumes "epoch_capacity n \<le> L"
  shows "epoch_decode n L bs = None"
  using assms by (simp add: epoch_decode_def)

text \<open>Zero bytes represent only epoch zero when the configured cap is
  zero. Applications may impose a positive width as a separate policy.\<close>

lemma epoch_zero_width [simp]:
  "epoch_encode 0 0 0 = Some []"
  "epoch_decode 0 0 [] = Some 0"
  by (simp_all add: epoch_encode_def epoch_decode_def epoch_capacity_def)

end
