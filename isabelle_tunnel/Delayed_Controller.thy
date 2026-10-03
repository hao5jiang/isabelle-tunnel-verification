theory Delayed_Controller
  imports Round_Robin
begin

datatype phase = Ready | Entering train | Occupied train | Leaving train
datatype input = Request train | Poll | EntryDone train | ExitDone train

record controller =
  stage :: phase
  priority :: train
  pending :: "train \<Rightarrow> nat"
  received :: "train \<Rightarrow> nat"
  served :: "train \<Rightarrow> nat"
  zone :: "train \<Rightarrow> bool"

definition boot :: controller where
  "boot = \<lparr>stage=Ready, priority=A, pending=(\<lambda>_.0), received=(\<lambda>_.0),
    served=(\<lambda>_.0), zone=(\<lambda>_.False)\<rparr>"

fun reserved where
  "reserved Ready i = False"
| "reserved (Entering j) i = (i=j)"
| "reserved (Occupied j) i = (i=j)"
| "reserved (Leaving j) i = (i=j)"

definition valid where
  "valid c \<longleftrightarrow>
    (\<forall>i. received c i = pending c i + served c i) \<and>
    (\<forall>i. zone c i = reserved (stage c) i) \<and>
    (case stage c of Ready \<Rightarrow> True
      | Entering i \<Rightarrow> 0 < pending c i \<and> priority c = other i
      | Occupied i \<Rightarrow> priority c = other i
      | Leaving i \<Rightarrow> priority c = other i)"

definition grant_to where
  "grant_to i c = c\<lparr>stage:=Entering i, priority:=other i,
    zone:=(zone c)(i:=True)\<rparr>"

fun react :: "input \<Rightarrow> controller \<Rightarrow> controller" where
  "react (Request i) c = c\<lparr>pending:=(pending c)(i:=Suc (pending c i)),
     received:=(received c)(i:=Suc (received c i))\<rparr>"
| "react Poll c = (case stage c of
      Ready \<Rightarrow> (if pending c (priority c)>0 then grant_to (priority c) c
        else if pending c (other (priority c))>0 then grant_to (other (priority c)) c else c)
    | Occupied i \<Rightarrow> c\<lparr>stage:=Leaving i\<rparr>
    | _ \<Rightarrow> c)"
| "react (EntryDone i) c = (if stage c = Entering i then
    c\<lparr>stage:=Occupied i, pending:=(pending c)(i:=pending c i - 1),
      served:=(served c)(i:=Suc (served c i))\<rparr> else c)"
| "react (ExitDone i) c = (if stage c = Leaving i then
    c\<lparr>stage:=Ready, zone:=(zone c)(i:=False)\<rparr> else c)"

fun history :: "(nat \<Rightarrow> input) \<Rightarrow> nat \<Rightarrow> controller" where
  "history ev 0 = boot"
| "history ev (Suc n) = react (ev n) (history ev n)"

lemma other_other [simp]: "other (other i) = i" by (cases i) simp_all
lemma other_ne [simp]: "other i \<noteq> i" by (cases i) simp_all
lemma other_A [simp]: "other i = A \<longleftrightarrow> i = B" by (cases i) simp_all
lemma other_B [simp]: "other i = B \<longleftrightarrow> i = A" by (cases i) simp_all

lemma boot_valid: "valid boot"
  by (simp add: valid_def boot_def)

lemma react_valid:
  assumes "valid c"
  shows "valid (react e c)"
  using assms
  by (cases e; cases "stage c";
      auto simp: valid_def grant_to_def train_all split: if_splits; presburger)

theorem history_valid: "valid (history ev n)"
  by (induction n) (auto intro: boot_valid react_valid)

theorem no_lost_requests:
  "received (history ev n) i = pending (history ev n) i + served (history ev n) i"
  using history_valid[of ev n] by (simp add: valid_def)

theorem request_is_recorded:
  "pending (react (Request i) c) i = Suc (pending c i) \<and>
   received (react (Request i) c) i = Suc (received c i) \<and>
   served (react (Request i) c) i = served c i"
  by simp

theorem service_requires_entry_confirmation:
  "served (react e c) i > served c i \<Longrightarrow>
    e = EntryDone i \<and> stage c = Entering i"
  by (cases e; cases "stage c") (auto simp: grant_to_def split: if_splits)

theorem delayed_safety:
  "\<not> (zone (history ev n) A \<and> zone (history ev n) B)"
  using history_valid[of ev n]
  by (cases "stage (history ev n)") (auto simp: valid_def)

theorem exit_confirmation_required:
  assumes "stage c = Leaving i" "e \<noteq> ExitDone i"
  shows "stage (react e c) = Leaving i \<and> zone (react e c) i = zone c i"
  using assms by (cases e) auto

theorem entry_delay_keeps_reservation:
  assumes "stage c = Entering i" "e \<noteq> EntryDone i"
  shows "stage (react e c) = Entering i \<and> zone (react e c) i = zone c i"
  using assms by (cases e) auto

lemma served_mono_step: "served c i \<le> served (react e c) i"
  by (cases e; cases "stage c") (auto simp: grant_to_def)

lemma pending_persists:
  assumes "valid c" "served (react e c) i = served c i"
  shows "pending c i \<le> pending (react e c) i"
  using assms by (cases e; cases "stage c") (auto simp: valid_def grant_to_def)

fun rank :: "train \<Rightarrow> controller \<Rightarrow> nat" where
  "rank i c = (case stage c of
      Ready \<Rightarrow> (if priority c = i then 2 else 7)
    | Entering j \<Rightarrow> (if j=i then 1 else 5)
    | Occupied j \<Rightarrow> (if j=i then 9 else 4)
    | Leaving j \<Rightarrow> (if j=i then 8 else 3))"

fun trigger where
  "trigger Ready = Poll"
| "trigger (Entering i) = EntryDone i"
| "trigger (Occupied i) = Poll"
| "trigger (Leaving i) = ExitDone i"

lemma rank_nonincrease:
  assumes "valid c" "pending c i>0" "served (react e c) i = served c i"
  shows "rank i (react e c) \<le> rank i c"
  using assms
  by (cases e; cases "stage c"; cases i; cases "priority c";
      auto simp: valid_def grant_to_def train_all split: if_splits train.splits;
      metis train.exhaust)

lemma trigger_progress:
  assumes "valid c" "pending c i>0" "served (react (trigger (stage c)) c) i = served c i"
  shows "rank i (react (trigger (stage c)) c) < rank i c"
  using assms
  by (cases "stage c"; cases i; cases "priority c";
      auto simp: valid_def grant_to_def train_all split: if_splits train.splits;
      metis train.exhaust)

lemma same_rank_stage:
  "rank i c = rank i d \<Longrightarrow> stage c = stage d"
  by (cases "stage c"; cases "stage d"; cases i;
      auto split: if_splits train.splits; metis train.exhaust)

text \<open>The environment continues polling and eventually delivers a
  truthful matching completion for each outstanding action. Signals outside
  their matching phase are ignored. Freshness and physical truth of a
  matching signal are environmental assumptions, not established here.\<close>

definition responsive where
  "responsive ev \<longleftrightarrow>
    (\<forall>n. \<exists>m\<ge>n. ev m=Poll) \<and>
    (\<forall>n i. stage (history ev n)=Entering i \<longrightarrow> (\<exists>m\<ge>n. ev m=EntryDone i)) \<and>
    (\<forall>n i. stage (history ev n)=Leaving i \<longrightarrow> (\<exists>m\<ge>n. ev m=ExitDone i))"

lemma responsive_trigger:
  "responsive ev \<Longrightarrow> \<exists>m\<ge>n. ev m = trigger (stage (history ev n))"
  by (cases "stage (history ev n)") (auto simp: responsive_def)

lemma served_history_mono: "mono (\<lambda>n. served (history ev n) i)"
  by (simp add: mono_iff_le_Suc served_mono_step)

lemma received_mono_step: "received c i \<le> received (react e c) i"
  by (cases e; cases "stage c") (auto simp: grant_to_def)

lemma received_history_mono: "mono (\<lambda>n. received (history ev n) i)"
  by (simp add: mono_iff_le_Suc received_mono_step)

theorem next_service:
  assumes resp: "responsive ev" and queued: "pending (history ev n) i > 0"
  shows "\<exists>m\<ge>n. served (history ev m) i > served (history ev n) i"
proof (rule ccontr)
  assume never: "\<not> (\<exists>m\<ge>n. served (history ev m) i > served (history ev n) i)"
  have same: "served (history ev m) i = served (history ev n) i" if "m\<ge>n" for m
    using monoD[OF served_history_mono[where ev=ev and i=i] that] never that by auto
  have eqstep: "served (react (ev m) (history ev m)) i = served (history ev m) i"
    if "m\<ge>n" for m
    using same[OF that] same[of "Suc m"] that by simp
  have pm: "mono (\<lambda>k. pending (history ev (n+k)) i)"
    unfolding mono_iff_le_Suc
    by (auto intro: pending_persists[OF history_valid] simp: eqstep)
  have positive: "pending (history ev m) i > 0" if "m\<ge>n" for m
    using monoD[OF pm, of 0 "m-n"] queued that by simp
  have rm: "antimono (\<lambda>k. rank i (history ev (n+k)))"
    unfolding antimono_iff_le_Suc
  proof
    fix k
    have ge: "n+k \<ge> n" by simp
    have "rank i (react (ev (n+k)) (history ev (n+k))) \<le> rank i (history ev (n+k))"
      by (rule rank_nonincrease[OF history_valid positive[OF ge] eqstep[OF ge]])
    then show "rank i (history ev (n + Suc k)) \<le> rank i (history ev (n+k))"
      by (simp only: add_Suc_right history.simps)
  qed
  have ex: "\<exists>r::nat. \<exists>k\<ge>n. rank i (history ev k)=r" by blast
  obtain r where witness: "\<exists>k\<ge>n. rank i (history ev k)=r"
    and least: "\<forall>v<r. \<not> (\<exists>k\<ge>n. rank i (history ev k)=v)"
    using iffD1[OF exists_least_iff ex] by blast
  obtain k where k: "k\<ge>n" "rank i (history ev k)=r" using witness by blast
  have lower: "r \<le> rank i (history ev j)" if "j\<ge>n" for j
    using least that by (metis not_le)
  obtain m where m: "m\<ge>k" "ev m=trigger (stage (history ev k))"
    using responsive_trigger[OF resp, of k] by blast
  have mn: "m\<ge>n" using m(1) k(1) by simp
  have upper: "rank i (history ev m) \<le> rank i (history ev k)"
    using antimonoD[OF rm, of "k-n" "m-n"] k(1) m(1) by simp
  have ranks: "rank i (history ev m) = rank i (history ev k)"
    using lower[OF mn] upper k(2) by simp
  have stages: "stage (history ev m) = stage (history ev k)"
    by (rule same_rank_stage[OF ranks])
  have trigger: "ev m=trigger (stage (history ev m))" using m(2) stages by simp
  have decrease: "rank i (history ev (Suc m)) < rank i (history ev m)"
    using trigger_progress[OF history_valid positive[OF mn]] eqstep[OF mn]
    by (simp add: trigger)
  have "Suc m\<ge>n" using mn by simp
  from lower[OF this] decrease ranks k(2) show False by simp
qed

theorem every_ticket_served:
  assumes resp: "responsive ev" and admitted: "target \<le> received (history ev n) i"
  shows "\<exists>m\<ge>n. target \<le> served (history ev m) i"
  using admitted
proof (induction target arbitrary: n)
  case 0
  show ?case by auto
next
  case (Suc target)
  obtain k where k: "k\<ge>n" "target \<le> served (history ev k) i"
    using Suc.IH[of n] Suc.prems by auto
  show ?case
  proof (cases "Suc target \<le> served (history ev k) i")
    case True
    with k(1) show ?thesis by blast
  next
    case False
    have count_eq: "served (history ev k) i=target" using k(2) False by simp
    have rec: "Suc target \<le> received (history ev k) i"
      using monoD[OF received_history_mono[where ev=ev and i=i] k(1)] Suc.prems by simp
    have pending: "pending (history ev k) i > 0"
      using no_lost_requests[of ev k i] rec count_eq by arith
    obtain m where m: "m\<ge>k" "served (history ev m) i > served (history ev k) i"
      using next_service[OF resp pending] by blast
    have "m\<ge>n" using m(1) k(1) by simp
    with m(2) count_eq show ?thesis by auto
  qed
qed

corollary each_request_event_served:
  assumes "responsive ev" "ev n=Request i"
  shows "\<exists>m\<ge>Suc n. received (history ev (Suc n)) i \<le> served (history ev m) i"
  by (rule every_ticket_served[OF assms(1)]) simp

definition stalled_input where
  "stalled_input n = (if n=0 then Request A else Poll)"

definition stalled_state where
  "stalled_state = grant_to A (react (Request A) boot)"

lemma stalled_prefix: "history stalled_input (2+k) = stalled_state"
proof (induction k)
  case 0
  show ?case by (simp add: numeral_eq_Suc stalled_input_def stalled_state_def boot_def)
next
  case (Suc k)
  show ?case using Suc.IH
    by (simp add: stalled_input_def stalled_state_def grant_to_def boot_def)
qed

theorem missing_completion_stalls:
  "pending (history stalled_input (2+k)) A = 1 \<and>
   served (history stalled_input (2+k)) A = 0 \<and>
   zone (history stalled_input (2+k)) A \<and>
   \<not> zone (history stalled_input (2+k)) B"
  by (simp only: stalled_prefix; simp add: stalled_state_def grant_to_def boot_def)

end
