theory Tunnel_CTLK
  imports Finite_CTLK Tunnel_Knowledge
begin

instance position :: finite
proof standard
  have eq: "(UNIV :: position set) = {Outside, Waiting, Inside}"
    by (auto; metis position.exhaust)
  show "finite (UNIV :: position set)" unfolding eq by simp
qed

definition encode_state :: "state \<Rightarrow> position \<times> position \<times> bool \<times> bool" where
  "encode_state s = (loc s A, loc s B, permit s A, permit s B)"

lemma encode_injective: "inj encode_state"
proof (rule injI)
  fix s t
  assume "encode_state s = encode_state t"
  then have vals: "loc s A = loc t A" "loc s B = loc t B"
    "permit s A = permit t A" "permit s B = permit t B"
    by (auto simp: encode_state_def)
  have L: "loc s = loc t"
  proof (rule ext)
    fix i
    show "loc s i = loc t i" using vals by (cases i) simp_all
  qed
  have P: "permit s = permit t"
  proof (rule ext)
    fix i
    show "permit s i = permit t i" using vals by (cases i) simp_all
  qed
  from L P show "s = t" by (cases s; cases t; simp)
qed

lemma finite_states: "finite (UNIV :: state set)"
  by (rule finite_imageD[OF finite_subset[OF subset_UNIV finite_UNIV] encode_injective])

definition statesG where "statesG = {s. reachable s}"
lemma finite_statesG: "finite statesG"
  by (rule finite_subset[OF subset_UNIV finite_states])

datatype tunnel_atom = InTunnel train | Collision | Truth
fun valuation where
  "valuation (InTunnel i) s = (loc s i = Inside)"
| "valuation Collision s = (\<not> safe s)"
| "valuation Truth s = True"

interpretation tunnel: finite_model statesG step "\<lambda>i s. loc s i" valuation
  by standard (rule finite_statesG)

definition Implies where "Implies p q = Neg (Conj p (Neg q))"
definition Globally where "Globally p = Neg (EU (Atom Truth) (Neg p))"

lemma meaning_know_bridge:
  "s \<in> tunnel.meaning (Know i p) \<longleftrightarrow>
   reachable s \<and> knows i (\<lambda>t. t \<in> tunnel.meaning p) s"
  by (simp only: tunnel.meaning.simps tunnel.box_semantics; auto simp: statesG_def knows_def)

lemma global_if_everywhere:
  assumes "tunnel.meaning p = statesG"
  shows "tunnel.meaning (Globally p) = statesG"
proof -
  have empty: "lfp (tunnel.untilF statesG {}) = {}"
    by (rule equalityI) (auto intro!: lfp_lowerbound simp: tunnel.untilF_def tunnel.pre_def)
  show ?thesis unfolding Globally_def
    by (simp only: tunnel.meaning.simps assms valuation.simps; simp add: empty)
qed

lemma knowledge_condition_everywhere:
  assumes "i \<noteq> j"
  shows "tunnel.meaning (Implies (Atom (InTunnel i)) (Know i (Neg (Atom (InTunnel j))))) = statesG"
  using inside_knows_other_out[OF _ _ assms]
  unfolding Implies_def
  by (simp only: tunnel.meaning.simps valuation.simps tunnel.box_def tunnel.pre_def;
      auto simp: statesG_def knows_def)

theorem chapter8_3_checked:
  assumes "i \<noteq> j" "reachable s"
  shows "s \<in> tunnel.check (Globally
    (Implies (Atom (InTunnel i)) (Know i (Neg (Atom (InTunnel j))))))"
  using global_if_everywhere[OF knowledge_condition_everywhere[OF assms(1)]] assms(2)
  by (simp only: tunnel.checker_correct; auto simp: statesG_def)

theorem safety_formula_checked:
  assumes "reachable s"
  shows "s \<in> tunnel.check (Globally (Neg (Atom Collision)))"
proof -
  have "tunnel.meaning (Neg (Atom Collision)) = statesG"
    using mutual_exclusion by (simp only: tunnel.meaning.simps valuation.simps; auto simp: statesG_def)
  from global_if_everywhere[OF this] assms show ?thesis
    by (simp only: tunnel.checker_correct; auto simp: statesG_def)
qed

definition execution where
  "execution s pi \<longleftrightarrow> pi 0 = s \<and> (\<forall>n. step (pi n) (pi (Suc n)))"

lemma execution_reachable:
  assumes "reachable s" "execution s pi"
  shows "reachable (pi n)"
  using assms unfolding execution_def
  by (induction n) (auto intro: reachable.advance)

theorem infinite_path_safety:
  assumes "reachable s" "execution s pi"
  shows "\<forall>n. safe (pi n)"
  using execution_reachable[OF assms] mutual_exclusion by blast

theorem infinite_path_knowledge:
  assumes "reachable s" "execution s pi" "i \<noteq> j"
  shows "\<forall>n. loc (pi n) i = Inside \<longrightarrow>
    knows i (\<lambda>t. loc t j \<noteq> Inside) (pi n)"
  using execution_reachable[OF assms(1,2)] inside_knows_other_out assms(3) by blast

theorem stuttering_execution: "execution s (\<lambda>_. s)"
  by (simp add: execution_def step.idle)

theorem waiting_forever_counterexample:
  "reachable s1 \<and> execution s1 (\<lambda>_. s1) \<and>
    (\<forall>n::nat. loc ((\<lambda>_. s1) n) A = Waiting)"
  using reachable.advance[OF reachable.initial edge01] stuttering_execution
  by (simp add: s1_def)

text \<open>With an idle self-loop at every state, unrestricted AF P adds
  no states beyond P. This formally exposes the missing fairness premise.\<close>

theorem af_cannot_force_progress:
  "tunnel.meaning (AF p) = tunnel.meaning p"
proof (rule equalityI)
  show "tunnel.meaning (AF p) \<subseteq> tunnel.meaning p"
    by (simp only: tunnel.meaning.simps, rule lfp_lowerbound)
       (auto simp: tunnel.afF_def tunnel.box_semantics; meson step.idle)
  have "mono (tunnel.afF (tunnel.meaning p))" by (rule tunnel.af_mono)
  then have unfold: "lfp (tunnel.afF (tunnel.meaning p)) =
    tunnel.afF (tunnel.meaning p) (lfp (tunnel.afF (tunnel.meaning p)))"
    by (rule lfp_unfold)
  show "tunnel.meaning p \<subseteq> tunnel.meaning (AF p)"
    using unfold by (simp only: tunnel.meaning.simps; auto simp: tunnel.afF_def)
qed

theorem eventual_entry_not_guaranteed:
  "s1 \<notin> tunnel.check (AF (Atom (InTunnel A)))"
  by (simp only: tunnel.checker_correct af_cannot_force_progress tunnel.meaning.simps valuation.simps;
      simp add: s1_def)

end
