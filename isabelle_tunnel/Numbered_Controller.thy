theory Numbered_Controller
  imports Delayed_Controller
begin

text \<open>Each admission starts a new unbounded natural-number generation.
  Entry and exit acknowledgements share that generation and have distinct
  message kinds. No restart, wraparound, or cryptographic authentication
  is modelled. Rejected input becomes a stuttering step of the old model.\<close>

datatype packet = Enqueue train | Schedule | EnterAck train nat | LeaveAck train nat
record numbered =
  core :: controller
  generation :: nat

definition numbered_boot where
  "numbered_boot = \<lparr>core=boot, generation=0\<rparr>"

fun decode :: "numbered \<Rightarrow> packet \<Rightarrow> input option" where
  "decode s (Enqueue i) = Some (Request i)"
| "decode s Schedule = Some Poll"
| "decode s (EnterAck i k) =
    (if k=generation s \<and> stage (core s)=Entering i then Some (EntryDone i) else None)"
| "decode s (LeaveAck i k) =
    (if k=generation s \<and> stage (core s)=Leaving i then Some (ExitDone i) else None)"

definition numbered_react where
  "numbered_react p s = (case decode s p of None \<Rightarrow> s | Some e \<Rightarrow>
    (let c = react e (core s) in
      s\<lparr>core:=c, generation:=(if stage (core s)=Ready \<and> stage c \<noteq> Ready
        then Suc (generation s) else generation s)\<rparr>))"

fun numbered_history where
  "numbered_history ev 0 = numbered_boot"
| "numbered_history ev (Suc n) = numbered_react (ev n) (numbered_history ev n)"

definition silent_input where
  "silent_input c = (case stage c of Entering i \<Rightarrow> EntryDone (other i) | _ \<Rightarrow> EntryDone A)"

lemma silent_stutters: "react (silent_input c) c = c"
  by (cases "stage c"; auto simp: silent_input_def; metis other_ne)

definition abstract_input where
  "abstract_input s p = (case decode s p of None \<Rightarrow> silent_input (core s) | Some e \<Rightarrow> e)"

theorem numbered_step_refines:
  "core (numbered_react p s) = react (abstract_input s p) (core s)"
  by (simp add: numbered_react_def abstract_input_def silent_stutters Let_def split: option.splits)

definition abstract_events where
  "abstract_events ev n = abstract_input (numbered_history ev n) (ev n)"

theorem numbered_trace_refines:
  "core (numbered_history ev n) = history (abstract_events ev) n"
  by (induction n) (simp_all add: numbered_boot_def numbered_step_refines abstract_events_def)

theorem numbered_valid: "valid (core (numbered_history ev n))"
  by (simp only: numbered_trace_refines; rule history_valid)

theorem numbered_safety:
  "\<not> (zone (core (numbered_history ev n)) A \<and> zone (core (numbered_history ev n)) B)"
  by (simp only: numbered_trace_refines; rule delayed_safety)

theorem numbered_accounting:
  "received (core (numbered_history ev n)) i =
    pending (core (numbered_history ev n)) i + served (core (numbered_history ev n)) i"
  by (simp only: numbered_trace_refines; rule no_lost_requests)

lemma generation_step:
  "generation (numbered_react p s) = generation s \<or>
   generation (numbered_react p s) = Suc (generation s)"
  by (auto simp: numbered_react_def Let_def split: option.splits)

lemma generation_mono_step:
  "generation s \<le> generation (numbered_react p s)"
  using generation_step[of p s] by auto

theorem generation_monotone:
  "mono (\<lambda>n. generation (numbered_history ev n))"
  by (simp add: mono_iff_le_Suc generation_mono_step)

theorem admission_changes_generation:
  assumes "stage (core s)=Ready" "stage (core (numbered_react p s)) \<noteq> Ready"
  shows "generation (numbered_react p s) = Suc (generation s)"
  using assms by (auto simp: numbered_react_def Let_def split: option.splits if_splits)

theorem mismatched_generation_ignored:
  assumes "k \<noteq> generation s"
  shows "numbered_react (EnterAck i k) s = s \<and> numbered_react (LeaveAck i k) s = s"
  using assms by (simp add: numbered_react_def Let_def)

theorem old_generation_stays_rejected:
  assumes "k < generation (numbered_history ev n)" "n \<le> m"
  shows "numbered_react (EnterAck i k) (numbered_history ev m) = numbered_history ev m \<and>
    numbered_react (LeaveAck i k) (numbered_history ev m) = numbered_history ev m"
proof -
  have "generation (numbered_history ev n) \<le> generation (numbered_history ev m)"
    by (rule monoD[OF generation_monotone assms(2)])
  then have "k \<noteq> generation (numbered_history ev m)" using assms(1) by arith
  then show ?thesis by (rule mismatched_generation_ignored)
qed

theorem entry_ack_idempotent:
  "numbered_react (EnterAck i k) (numbered_react (EnterAck i k) s) = numbered_react (EnterAck i k) s"
  by (auto simp: numbered_react_def Let_def split: if_splits)

theorem exit_ack_idempotent:
  "numbered_react (LeaveAck i k) (numbered_react (LeaveAck i k) s) = numbered_react (LeaveAck i k) s"
  by (auto simp: numbered_react_def Let_def split: if_splits)

theorem release_requires_matching_packet:
  assumes "stage (core s)=Leaving i" "p \<noteq> LeaveAck i (generation s)"
  shows "stage (core (numbered_react p s))=Leaving i \<and>
    zone (core (numbered_react p s)) i = zone (core s) i"
  using assms by (cases p) (auto simp: numbered_react_def Let_def)

text \<open>The liveness premise is on the accepted, translated event stream.
  Repeated stale packets alone do not satisfy this premise.\<close>

definition accepted_responsive where
  "accepted_responsive ev \<longleftrightarrow> responsive (abstract_events ev)"

theorem numbered_every_ticket_served:
  assumes "accepted_responsive ev" "target \<le> received (core (numbered_history ev n)) i"
  shows "\<exists>m\<ge>n. target \<le> served (core (numbered_history ev m)) i"
  using every_ticket_served[where ev="abstract_events ev" and target=target and n=n and i=i]
    assms by (simp only: accepted_responsive_def numbered_trace_refines)

fun waiting_phase where
  "waiting_phase (Entering i) = True"
| "waiting_phase (Leaving i) = True"
| "waiting_phase _ = False"

fun completion_packet where
  "completion_packet (Entering i) k = EnterAck i k"
| "completion_packet (Leaving i) k = LeaveAck i k"
| "completion_packet _ k = Schedule"

lemma matching_packet_translates:
  assumes "waiting_phase (stage (core s))"
  shows "abstract_input s (completion_packet (stage (core s)) (generation s)) =
    trigger (stage (core s))"
  using assms by (cases "stage (core s)") (simp_all add: abstract_input_def)

lemma waiting_packet_persistence:
  assumes "waiting_phase (stage (core s))"
    "p \<noteq> completion_packet (stage (core s)) (generation s)"
  shows "stage (core (numbered_react p s)) = stage (core s) \<and>
    generation (numbered_react p s) = generation s"
  using assms by (cases "stage (core s)"; cases p;
    auto simp: numbered_react_def Let_def)

definition packet_responsive where
  "packet_responsive ev \<longleftrightarrow>
    (\<forall>n. \<exists>m\<ge>n. ev m = Schedule) \<and>
    (\<forall>n. waiting_phase (stage (core (numbered_history ev n))) \<longrightarrow>
      (\<exists>m\<ge>n. ev m = completion_packet (stage (core (numbered_history ev n)))
        (generation (numbered_history ev n))))"

lemma packet_response_trigger:
  assumes resp: "packet_responsive ev"
    and waiting: "waiting_phase (stage (core (numbered_history ev n)))"
  shows "\<exists>m\<ge>n. abstract_events ev m = trigger (stage (core (numbered_history ev n)))"
proof (rule ccontr)
  let ?s = "numbered_history ev"
  let ?q = "stage (core (?s n))"
  let ?g = "generation (?s n)"
  assume absent: "\<not> (\<exists>m\<ge>n. abstract_events ev m = trigger ?q)"
  have persist: "stage (core (?s (n+d))) = ?q \<and> generation (?s (n+d)) = ?g" for d
  proof (induction d)
    case 0
    then show ?case by simp
  next
    case (Suc d)
    have w: "waiting_phase (stage (core (?s (n+d))))" using waiting Suc.IH by simp
    have different: "ev (n+d) \<noteq> completion_packet (stage (core (?s (n+d)))) (generation (?s (n+d)))"
    proof
      assume eq: "ev (n+d) = completion_packet (stage (core (?s (n+d)))) (generation (?s (n+d)))"
      have "abstract_events ev (n+d) = trigger ?q"
        using matching_packet_translates[OF w] Suc.IH eq
        by (simp add: abstract_events_def)
      then show False using absent by auto
    qed
    show ?case using waiting_packet_persistence[OF w different] Suc.IH by simp
  qed
  obtain m where later: "n \<le> m" and packet: "ev m = completion_packet ?q ?g"
    using resp waiting by (auto simp: packet_responsive_def)
  have same: "stage (core (?s m)) = ?q \<and> generation (?s m) = ?g"
    using persist[of "m-n"] later by simp
  have w: "waiting_phase (stage (core (?s m)))" using same waiting by simp
  have "abstract_events ev m = trigger ?q"
    using matching_packet_translates[OF w] same packet
    by (simp add: abstract_events_def)
  then show False using absent later by blast
qed

theorem packet_responsive_is_sufficient:
  assumes "packet_responsive ev"
  shows "accepted_responsive ev"
proof -
  have polls: "\<exists>m\<ge>n. abstract_events ev m = Poll" for n
  proof -
    obtain m where "n \<le> m" "ev m = Schedule"
      using assms by (auto simp: packet_responsive_def)
    then show ?thesis by (auto simp: abstract_events_def abstract_input_def)
  qed
  have entries: "stage (core (numbered_history ev n)) = Entering i \<Longrightarrow>
    \<exists>m\<ge>n. abstract_events ev m = EntryDone i" for n i
    using packet_response_trigger[OF assms, of n] by simp
  have exits: "stage (core (numbered_history ev n)) = Leaving i \<Longrightarrow>
    \<exists>m\<ge>n. abstract_events ev m = ExitDone i" for n i
    using packet_response_trigger[OF assms, of n] by simp
  show ?thesis using polls entries exits
    by (auto simp only: accepted_responsive_def responsive_def numbered_trace_refines[symmetric])
qed

theorem packet_every_ticket_served:
  assumes "packet_responsive ev" "target \<le> received (core (numbered_history ev n)) i"
  shows "\<exists>m\<ge>n. target \<le> served (core (numbered_history ev m)) i"
  by (rule numbered_every_ticket_served[OF packet_responsive_is_sufficient[OF assms(1)] assms(2)])

text \<open>A number is not evidence of physical completion. A packet with
  the current number, owner, and phase is accepted by this layer without
  checking its sender or a sensor. The next theorem records that boundary.\<close>

theorem current_number_can_advance:
  assumes "stage (core s)=Entering i"
  shows "served (core (numbered_react (EnterAck i (generation s)) s)) i = Suc (served (core s) i)"
  using assms by (simp add: numbered_react_def)

end
