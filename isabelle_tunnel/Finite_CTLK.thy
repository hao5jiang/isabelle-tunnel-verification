theory Finite_CTLK
  imports "HOL-Library.While_Combinator"
begin

text \<open>Finite set-based CTLK core. EU and AF use least-fixed-point
  semantics. This is not an OBDD implementation or a SAT encoding.\<close>

datatype ('p, 'i) formula = Atom 'p | Neg "('p, 'i) formula"
  | Conj "('p, 'i) formula" "('p, 'i) formula"
  | Next "('p, 'i) formula"
  | EU "('p, 'i) formula" "('p, 'i) formula"
  | AF "('p, 'i) formula"
  | Know 'i "('p, 'i) formula"
  | Everyone "'i set" "('p, 'i) formula"
  | Distributed "'i set" "('p, 'i) formula"
  | Common "'i set" "('p, 'i) formula"

locale finite_model =
  fixes G :: "'s set" and T :: "'s \<Rightarrow> 's \<Rightarrow> bool"
    and obs :: "'i \<Rightarrow> 's \<Rightarrow> 'o"
    and V :: "'p \<Rightarrow> 's \<Rightarrow> bool"
  assumes finite_G: "finite G"
begin

definition pre where
  "pre R X = {s \<in> G. \<exists>t \<in> X. R s t}"
definition box where
  "box R X = G - pre R (G - X)"
definition erel where "erel J s t \<longleftrightarrow> (\<exists>i \<in> J. obs i s = obs i t)"
definition drel where "drel J s t \<longleftrightarrow> (\<forall>i \<in> J. obs i s = obs i t)"
definition untilF where "untilF P Q X = Q \<union> (P \<inter> pre T X)"
definition afF where "afF P X = P \<union> box T X"
definition spread where "spread R P X = P \<union> pre R X"
definition iterate where "iterate F = while (\<lambda>X. F X \<noteq> X) F {}"

lemma pre_mono: "X \<subseteq> Y \<Longrightarrow> pre R X \<subseteq> pre R Y"
  by (auto simp: pre_def)
lemma box_mono: "X \<subseteq> Y \<Longrightarrow> box R X \<subseteq> box R Y"
  by (auto simp: box_def pre_def)
lemma until_mono: "mono (untilF P Q)"
  unfolding mono_def untilF_def using pre_mono by blast
lemma af_mono: "mono (afF P)"
  unfolding mono_def afF_def using box_mono by blast
lemma spread_mono: "mono (spread R P)"
  unfolding mono_def spread_def using pre_mono by blast

theorem iteration_terminates:
  assumes "mono F" "\<And>X. X \<subseteq> G \<Longrightarrow> F X \<subseteq> G"
  shows "\<exists>Y. while_option (\<lambda>X. F X \<noteq> X) F {} = Some Y"
  using while_option_finite_subset_Some[OF assms finite_G] .

theorem iteration_correct:
  assumes "mono F" "\<And>X. X \<subseteq> G \<Longrightarrow> F X \<subseteq> G"
  shows "iterate F = lfp F"
  unfolding iterate_def using lfp_while[OF assms finite_G] by simp

lemma until_closed: "P \<subseteq> G \<Longrightarrow> Q \<subseteq> G \<Longrightarrow> untilF P Q X \<subseteq> G"
  by (auto simp: untilF_def pre_def)
lemma af_closed: "P \<subseteq> G \<Longrightarrow> afF P X \<subseteq> G"
  by (auto simp: afF_def box_def)
lemma spread_closed: "P \<subseteq> G \<Longrightarrow> spread R P X \<subseteq> G"
  by (auto simp: spread_def pre_def)

fun meaning :: "('p, 'i) formula \<Rightarrow> 's set" where
  "meaning (Atom p) = {s \<in> G. V p s}"
| "meaning (Neg p) = G - meaning p"
| "meaning (Conj p q) = meaning p \<inter> meaning q"
| "meaning (Next p) = pre T (meaning p)"
| "meaning (EU p q) = lfp (untilF (meaning p) (meaning q))"
| "meaning (AF p) = lfp (afF (meaning p))"
| "meaning (Know i p) = box (\<lambda>s t. obs i s = obs i t) (meaning p)"
| "meaning (Everyone J p) = box (erel J) (meaning p)"
| "meaning (Distributed J p) = box (drel J) (meaning p)"
| "meaning (Common J p) = G - lfp (spread (erel J) (G - meaning p))"

lemma meaning_closed: "meaning p \<subseteq> G"
  by (induction p) (auto simp: pre_def box_def untilF_def afF_def intro!: lfp_lowerbound)

lemma iterate_until:
  "P \<subseteq> G \<Longrightarrow> Q \<subseteq> G \<Longrightarrow> iterate (untilF P Q) = lfp (untilF P Q)"
  by (rule iteration_correct) (auto simp: untilF_def pre_def intro: until_mono)
lemma iterate_af:
  "P \<subseteq> G \<Longrightarrow> iterate (afF P) = lfp (afF P)"
  by (rule iteration_correct) (auto simp: afF_def box_def intro: af_mono)
lemma iterate_spread:
  "P \<subseteq> G \<Longrightarrow> iterate (spread R P) = lfp (spread R P)"
  by (rule iteration_correct) (auto simp: spread_def pre_def intro: spread_mono)

fun check :: "('p, 'i) formula \<Rightarrow> 's set" where
  "check (Atom p) = {s \<in> G. V p s}"
| "check (Neg p) = G - check p"
| "check (Conj p q) = check p \<inter> check q"
| "check (Next p) = pre T (check p)"
| "check (EU p q) = iterate (untilF (check p) (check q))"
| "check (AF p) = iterate (afF (check p))"
| "check (Know i p) = box (\<lambda>s t. obs i s = obs i t) (check p)"
| "check (Everyone J p) = box (erel J) (check p)"
| "check (Distributed J p) = box (drel J) (check p)"
| "check (Common J p) = G - iterate (spread (erel J) (G - check p))"

theorem checker_correct: "check p = meaning p"
  by (induction p) (simp_all add: iterate_until iterate_af iterate_spread meaning_closed)

lemma box_semantics:
  "s \<in> box R X \<longleftrightarrow> s \<in> G \<and> (\<forall>t \<in> G. R s t \<longrightarrow> t \<in> X)"
  by (auto simp: box_def pre_def)

theorem knowledge_factive: "s \<in> meaning (Know i p) \<Longrightarrow> s \<in> meaning p"
  by (auto simp: box_semantics)
theorem positive_introspection:
  "meaning (Know i (Know i p)) = meaning (Know i p)"
  by (auto simp: box_semantics)
theorem negative_introspection:
  "meaning (Know i (Neg (Know i p))) = meaning (Neg (Know i p))"
  by (auto simp: box_semantics; blast)
theorem everyone_semantics:
  "s \<in> meaning (Everyone J p) \<longleftrightarrow>
    s \<in> G \<and> (\<forall>i \<in> J. s \<in> meaning (Know i p))"
  by (auto simp: box_semantics erel_def)
theorem distributed_semantics:
  "s \<in> meaning (Distributed J p) \<longleftrightarrow>
    s \<in> G \<and> (\<forall>t \<in> G. (\<forall>i \<in> J. obs i s = obs i t) \<longrightarrow> t \<in> meaning p)"
  by (auto simp: box_semantics drel_def)

end
end
