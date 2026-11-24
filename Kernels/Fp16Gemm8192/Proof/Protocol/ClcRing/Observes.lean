-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Values
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Group
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.Order
public import Lemmas.Clc.ClcReadSources
public import Lemmas.Kernel.ExitChain
public import Lemmas.Order.DependencyWitness
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive

@[expose] public section

/-! # The CLC responses observed by the selected readers and by the consumers

A consumer's successful response poll observes the request whose notification is the response
barrier's completion numbered by its earlier successful polls. Its warp group's named barrier
orders the poll before the arrival of that ordinal, and the group's first thread orders the
arrival of that ordinal before the acknowledgements of the same generation: the poll precedes,
in the dependency order, the completion of every request numbered above its count
(`cons_chain`), so the completions before it are at most its count plus one and it found the
phase of its count plus one (`cons_poll_phase`). A selected reader's poll observes the same
request through its consumer selector (`sel_observed`, in `Values.lean`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The acknowledgement chain of a selected consumer `b`, without naming the reader.** -/
theorem ack_sync_sel (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10}
    {h ki pc cta : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hi : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) (hct : cta ∈ tg) (hcc : cta / 2 = c)
    {m : Nat} (hm : m < issuesBefore L X c h ki) :
    ∃ g a ea, consumerSel L c b g = true ∧ X.get (g, a) = some ea ∧
      (∃ tx n rel sc, ea.kind = .arrive ((slot L c).empty 0) tx n rel sc) ∧
      arrivals ((slot L c).empty 0) ((X.tr g).take a) = m ∧ MSync L X (g, a) (h, ki) := by
  obtain ⟨a, ea, hea, hk, hcnt, hms⟩ := ack_sync_thr hpre hX ht b hi hct hcc hm
  exact ⟨thr L X c b, a, ea, thr_sel hpre c b, hea, hk, hcnt, hms⟩

/-- Agreement below an ordinal holds below every smaller one. -/
theorem agreeBelow_mono {m n : Nat} (hmn : m ≤ n) (hag : OutputRing.ResponsesAgreeBelow L X n) :
    OutputRing.ResponsesAgreeBelow L X m := by
  intro c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2 hc1 hc2 hw1 hw2
    heq hlt
  exact hag c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2 hc1 hc2 hw1
    hw2 heq (by omega)

/-- The selected consumer of CTA parity `k` and warp group `q`: lane 0 of warp `4q`. -/
def firstB (k q : Fin 2) : Fin 10 :=
    ⟨6 + 2 * k.val + q.val, by have := k.isLt; have := q.isLt; omega⟩

theorem firstB_facts (k q : Fin 2) :
    ctaOf (firstB k q) = k.val ∧ warpOf (firstB k q) = 4 * q.val ∧
      laneZero (firstB k q) = true := by
  fin_cases k <;> fin_cases q <;> decide


/-- **The group-first thread's barrier arrivals before its acknowledgement.** The thread of
consumer `b`, lane 0 of warp `4q`, before its acknowledgement with `m` earlier ones made its
group's CLC barrier arrival of every ordinal `m' ≤ m`. -/
theorem first_bar (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {q : Nat} (hq : q < 2)
    (hbw : warpOf b = 4 * q) {f a : Nat} {ea : Event} (hsel : consumerSel L c b f = true)
    (hfa : X.get (f, a) = some ea)
    (hka : ∃ tx n rel sc, ea.kind = .arrive ((slot L c).empty 0) tx n rel sc) {m m' : Nat}
    (harr : arrivals ((slot L c).empty 0) ((X.tr f).take a) = m) (hm' : m' ≤ m) :
    ∃ j pcx, j < a ∧ X.IsBarrier (f, j) (q + 1) (some 128) pcx ∧
      ((X.tr f).take j).countP (Execution.isBarId (q + 1)) = m' := by
  obtain ⟨tx, n, rel, sc, hka⟩ := hka
  have hfl : f < L.threads := Frame.lt_of_get hX hfa
  have hsel' := hsel
  simp only [consumerSel, decide_eq_true_eq] at hsel'
  obtain ⟨hf1, hf2, -⟩ := hsel'
  have hcb := ctaOf_lt b
  have hkrw : ea.kind = .arrive (Bar.loc L (2 * (f / L.block / 2)) ⟨.clc, 0, false⟩) tx n rel sc :=
    by
    rw [hka]
    have h2 : 2 * (f / L.block / 2) = 2 * c := by omega
    rw [h2]
    rfl
  obtain ⟨r, hσr, hwr⟩ := arrive_role hX ht hfl hfa (b := ⟨.clc, 0, false⟩)
    (cta := 2 * (f / L.block / 2)) hkrw Nat.one_pos
  rcases r with l | mm | sd | c'
  · simp only [roleWarp] at hwr; omega
  · simp only [roleWarp] at hwr; omega
  · simp only [roleWarp] at hwr; omega
  have hc0 : c'.clcHold = 0 := ht.ack_hold hfl hfa hσr hkrw
  have hab := ht.arrival_budget (b := ⟨.clc, 0, false⟩) (cta := 2 * (f / L.block / 2)) hfl hfa
    hσr hkrw Nat.one_pos
  simp only [Bar.gate, Bar.gateSlack] at hab
  have hloc1 : Bar.loc L (2 * (f / L.block / 2)) ⟨.clc, 0, false⟩ = (slot L c).empty 0 := by
    have h2 : 2 * (f / L.block / 2) = 2 * c := by omega
    simp only [slot, h2]
  rw [hloc1, harr] at hab
  have htq : Consumer.tidOf L f / 32 / 4 + 1 = q + 1 := by
    show f % L.block / 32 / 4 + 1 = q + 1
    rw [hf2, hbw]
    omega
  have hcc1 := ht.cons_clc hfl hfa hσr
  rw [hc0, Nat.add_zero, htq] at hcc1
  have hcount : m' + 1 ≤ ((X.tr f).take a).countP (Execution.isBarId (q + 1)) := by
    rw [← hcc1]; omega
  obtain ⟨j, x, hjl, hjx, hxbar, hcj⟩ := exists_nthEv (X := X) hcount
  have hkind : ∃ pcx cnt, x = ⟨pcx, .bar (q + 1) cnt⟩ := by
    obtain ⟨pcx, kx⟩ := x
    cases kx with
    | bar id' cnt' m' =>
      simp only [Execution.isBarId, beq_iff_eq] at hxbar
      cases m'
      · exact ⟨pcx, cnt', by rw [hxbar]⟩
      · subst hxbar
        exact (hX.noBarArrive Fact.out _ _ _ _ hjx).elim
    | _ => simp [Execution.isBarId] at hxbar
  obtain ⟨pcx, cnt, rfl⟩ := hkind
  obtain ⟨d, hσj⟩ := Frame.event_state ht.sound hX ht.tracked hjx nofun
  obtain ⟨cj, rfl⟩ := ht.bar_role hfl hjx hσj rfl
  have hcnt : cnt = some 128 := by
    have := (ht.cons_out hfl hjx hσj).2.2.2.2.1 (q + 1) cnt rfl
    rcases this with ⟨-, -, hc⟩ | ⟨-, hid, hc⟩
    · exact hc
    · exfalso
      simp only [Consumer.outId] at hid
      omega
  subst hcnt
  exact ⟨j, pcx, hjl, hjx, hcj⟩

/-- **Step 1: a request's group chain.** A request of cluster `c` that the leader issued after
`m` earlier requests is preceded, in the group `q` of a thread `g` of the request's cluster, by
the group arrival of ordinal `m`, and every event of `g` before that arrival precedes the
request. -/
theorem grp_request (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {q : Nat} (hq : q < 2)
    (hbw : warpOf b = 4 * q) {g : Nat} (hgt : g < L.threads) (hgc : g / L.block = 2 * c + ctaOf b)
    (hgw : (g % L.block) / 32 ∈ OutputRing.group q)
    {h ki pc cta : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hi : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) (hct : cta ∈ tg) (hcc : cta / 2 = c)
    {m : Nat} (hm : m < issuesBefore L X c h ki) (hag : OutputRing.ResponsesAgreeBelow L X m) :
    ∃ i pc', X.IsBarrier (g, i) (q + 1) (some 128) pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId (q + 1)) = m ∧
        ∀ e, e < i → baseCausality L X (g, e) (h, ki) := by
  obtain ⟨f, a, ea, hsel, hfa, hka, harr, hms⟩ :=
    ack_sync_sel hpre hX ht (b := b) hi hct hcc hm
  have hfl : f < L.threads := Frame.lt_of_get hX hfa
  obtain ⟨j, pcx, hjl, hIB, hcj⟩ := first_bar hX ht hq hbw hsel hfa hka harr le_rfl
  have hjf : j + 1 < (X.tr f).length :=
    Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hjl) (len_of_get hfa)
  have hcta : g / L.block = f / L.block := by rw [hgc, sel_cta hsel]
  obtain ⟨i, pc', hIBg, hcountg⟩ := ClcGroup.member_arrival hpre hX ht hq hIB hjf
    (show OutputRing.ResponsesAgreeBelow L X (((X.tr f).take j).countP _) by rw [hcj]; exact hag)
    hcta hgt hgw
  refine ⟨i, pc', hIBg, ?_, ?_⟩
  · rw [hcountg]
    exact hcj
  · intro e he
    have hsame : SameCta L g f := ⟨hgt, hfl, hcta⟩
    have hbe := ClcGroup.baseCausality_of_ordinal hpre hX ht hq hsame hIBg hIB hjf
      hcountg he hjl (len_of_get hfa)
    exact Relation.TransGen.tail hbe (Or.inr (Or.inr (Or.inl hms)))

/-- **Step 1 for a consumer thread.** The group chain of a consumer `g` of warp below 8, for a
request of its own cluster. -/
theorem grp_group (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g : Nat} (hgt : g < L.threads)
    (hw : g % L.block / 32 < 8) {h ki pc cta : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hi : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) (hct : cta ∈ tg)
    (hcc : cta / 2 = g / L.block / 2) {m : Nat} (hm : m < issuesBefore L X (g / L.block / 2) h ki)
    (hag : OutputRing.ResponsesAgreeBelow L X m) :
    ∃ i pc', X.IsBarrier (g, i) (Consumer.tidOf L g / 32 / 4 + 1) (some 128) pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) = m ∧
        ∀ e, e < i → baseCausality L X (g, e) (h, ki) := by
  have hq2 : Consumer.tidOf L g / 32 / 4 < 2 := by
    show g % L.block / 32 / 4 < 2
    omega
  have hfac := firstB_facts ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩
    ⟨Consumer.tidOf L g / 32 / 4, hq2⟩
  refine grp_request hpre hX ht (c := g / L.block / 2)
    (b := firstB ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨Consumer.tidOf L g / 32 / 4, hq2⟩)
    hq2 hfac.2.1 hgt ?_ ?_ hi hct hcc hm hag
  · rw [hfac.1]
    show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
    omega
  · simp only [OutputRing.group, Finset.mem_insert, Finset.mem_singleton, Consumer.tidOf]
    omega

/-- A group arrival's consumer sits at its group barrier site, holding its response. -/
theorem group_arrival_site (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {g i q pc' : Nat} (hq : q < 2)
    (hi : X.IsBarrier (g, i) (q + 1) (some 128) pc') (hgt : g < L.threads) :
    ∃ c', Frame.stateAt (code L) X g i = some (some (.inr (.cons c'))) ∧ c'.site = .clcBar := by
  obtain ⟨-, -, c', hσ⟩ := ClcGroup.group_bar_facts hX ht hq hi hgt
  refine ⟨c', hσ, ?_⟩
  rcases (ht.cons_out hgt hi hσ).2.2.2.2.1 (q + 1) (some 128) rfl with ⟨hs, -, -⟩ | ⟨-, hid, -⟩
  · exact hs
  · exfalso
    simp only [Consumer.outId] at hid
    omega

/-- **Step 2: a successful poll precedes the group arrival of its ordinal.** -/
theorem poll_before_group (ht : ThreadFacts L X) {g i j q pc' : Nat} {c' : Consumer.D}
    (hgt : g < L.threads) (hq : Consumer.tidOf L g / 32 / 4 = q)
    (hi : X.IsBarrier (g, i) (q + 1) (some 128) pc')
    (hσi : Frame.stateAt (code L) X g i = some (some (.inr (.cons c')))) (hsite : c'.site = .clcBar)
    (hj : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) =
      ((X.tr g).take i).countP (Execution.isBarId (q + 1))) : j < i := by
  have hc := ht.cons_clc hgt hi hσi
  have hclc : c'.clcHold = 1 := by simp [Consumer.D.clcHold, hsite]
  rw [hclc] at hc
  subst hq
  by_contra hn
  have hle : i ≤ j := Nat.le_of_not_lt hn
  have hmono := okPolls_mono (X := X) (g := g) (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) hle
  omega

/-- The response barrier of CTA `C`, as the full object of its cluster's slot. -/
abbrev respFull (L : Launch) (C : Nat) : Loc :=
  (slot L (C / 2)).full ⟨C % 2, Nat.mod_lt _ (by norm_num)⟩

theorem respFull_eq (L : Launch) (C : Nat) : Bar.loc L C ⟨.clc, 0, true⟩ = respFull L C := by
  show Bar.loc L C ⟨.clc, 0, true⟩ = Bar.loc L (2 * (C / 2) + C % 2) ⟨.clc, 0, true⟩
  rw [show 2 * (C / 2) + C % 2 = C by omega]

/-- The completions of a response barrier's causal prefix count as the object's completed
transactions. -/
theorem countP_completion_eq (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {k : Fin 2} {xs : List (Record Ref)} (hxs : ∀ q ∈ xs, q ∈ X.objects ((slot L c).full k)) :
    xs.countP isCompletion = completedTxCount xs := by
  unfold completedTxCount
  refine List.countP_congr fun q hq => ?_
  have hqm := hxs q hq
  rw [isCompletion_iff]
  cases ha : q.action <;> cases hf : q.fault <;> simp
  case completeTx.none n' => exact full_uniform hX ht q hqm n' ha hf

/-- A completion of a response barrier is the notification of a request of the cluster's leader
for the CTA the barrier belongs to. -/
theorem completion_request (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {k : Fin 2} {d : Record Ref} (hd : d ∈ X.objects ((slot L c).full k))
    (hc : isCompletion d = true) :
    ∃ h ki, d.id = .async (h, ki) (.notify (.cta (2 * c + k.val))) := by
  have ha := ((isCompletion_iff d).mp hc).1
  cases full_src hX ht hd with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive _ _ ha' => rw [ha] at ha'; cases ha'
  | notify _ _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ _ _ hby => exact absurd hby (by simp [Bar.copyBy])
  | @clc h ki pc cc sp tg dd hid he htg ha' hσ hby hmb hcta hcl =>
    refine ⟨h, ki, ?_⟩
    rw [hid, hcta]

/-- The `n`-th completion of a response barrier sits in the object's log with exactly `n`
completed transactions before it. -/
theorem nth_completion (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {k : Fin 2} {n : Nat}
    (hcnt : n + 1 ≤ (X.objects ((slot L c).full k)).countP isCompletion) :
    ∃ jd d, (X.objects ((slot L c).full k))[jd]? = some d ∧ isCompletion d = true ∧
      completedTxCount ((X.objects ((slot L c).full k)).take jd) = n := by
  obtain ⟨jd, d, hjd, hdc, hcount⟩ := MbarRing.Slot.exists_nth_countP isCompletion hcnt
  refine ⟨jd, d, hjd, hdc, ?_⟩
  rw [← countP_completion_eq hX ht (fun q hq => List.mem_of_mem_take hq)]
  exact hcount

/-- Two CLC barrier arrivals of a group with the same ordinal, the second passed, are of one
barrier generation. -/
theorem same_key (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {q : Nat} (hq : q < 2) {g i f j pc pc' : Nat} (hsame : SameCta L g f)
    (he : X.IsBarrier (g, i) (q + 1) (some 128) pc)
    (hf : X.IsBarrier (f, j) (q + 1) (some 128) pc') (hpassed : j + 1 < (X.tr f).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId (q + 1)) =
      ((X.tr f).take j).countP (Execution.isBarId (q + 1))) :
    ∃ key, CtaBarK L X (g, i) key ∧ CtaBarK L X (f, j) key :=
  have hG := OutputRing.group_shape hpre hq (id := q + 1) (by omega)
  have hS := ClcGroup.clc_sources hX ht hq
  have hft : f < L.threads := Frame.lt_of_get hX hf
  NamedBar.reached_same_key_of_passed hX hG.pos hG.target hG.id_lt hsame he hf hpassed
    (hS.sync he (Frame.lt_of_get hX he)).1 (hS.prefixFor hX (e := (f, j)) hft) hordinal
    (fun idx _ => hS.completed hX (NamedBar.cta_lt hft) (idx + 1)) rfl hG.bound

/-- **The group chain of a consumer's poll.** A consumer thread `g`'s successful response poll
with `n` earlier ones precedes, in the dependency order, the completion of every request
numbered above `n`: the poll resumes `g`'s group barrier arrival of ordinal `n`, a witness of the
group-first thread's `bar.sync` of that ordinal; that thread's acknowledgement of the use before
the request follows its return and is a witness of the leader's poll that resumes the
request. -/
theorem cons_chain (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j pc p : Nat} {acq : Bool} {sc : MbarScope} (hg : g < L.threads)
    (hw : g % L.block / 32 < 8)
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hag : OutputRing.ResponsesAgreeBelow L X
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j)))
    {f : Fin 2} {s : Nat} (hx : ((0 : Fin 1), s) ∈ SF L X (g / L.block / 2) f)
    (hs : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) < s) :
    Relation.TransGen (DepStep L kernel X) (.thread (g, j), true)
      (item L X (g / L.block / 2) f s, false) := by
  have hacyc := hX.depAcyclic
  set c := g / L.block / 2 with hc
  set n := okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) with hn
  set R := ring hpre hX ht c with hR
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hgP := R.guardP f (0, s' + 1) hx (s' + 1) (by omega) le_rfl
  have hpres := MbarRing.Round.Slot.present_of_guard hgP
  have hq2 : Consumer.tidOf L g / 32 / 4 < 2 := by
    show g % L.block / 32 / 4 < 2
    omega
  set k : Fin 2 := ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩ with hk
  set q : Fin 2 := ⟨Consumer.tidOf L g / 32 / 4, hq2⟩ with hqd
  have hfac := firstB_facts k q
  obtain ⟨hy, hobs⟩ := R.observes_empty hacyc (a := 0) (n := s') hpres (firstB k q)
  obtain ⟨x, hxm, hxid, -⟩ := (mem_SE hX).mp hy
  obtain ⟨ea, hea⟩ : X.RefPresent (.thread (ackEv L X c (firstB k q) s')) :=
    hxid ▸ object_record_present hX.tma hxm
  obtain ⟨pca, txa, na, rela, sca, rfl⟩ := ack_event hea
  obtain ⟨-, hcnt⟩ := ack_spec hea
  have hselF := thr_sel (X := X) hpre c (firstB k q)
  obtain ⟨j1, pcx, hj1, hIBf, hcj1⟩ := first_bar hX ht (q := q.val) hq2 hfac.2.1 hselF hea
    ⟨_, _, _, _, rfl⟩ hcnt (m' := n) (by omega)
  set fT := thr L X c (firstB k q) with hfT
  have hfl : fT < L.threads := Frame.lt_of_get hX hea
  have hjf : j1 + 1 < (X.tr fT).length :=
    Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hj1) (len_of_get hea)
  have hcta : g / L.block = fT / L.block := by
    rw [sel_cta hselF, hfac.1]
    show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
    omega
  have hgw : (g % L.block) / 32 ∈ OutputRing.group q.val := by
    simp only [OutputRing.group, Finset.mem_insert, Finset.mem_singleton, hqd, Consumer.tidOf]
    omega
  obtain ⟨i, pc', hIBg, hcountg⟩ := ClcGroup.member_arrival hpre hX ht hq2 hIBf hjf
    (show OutputRing.ResponsesAgreeBelow L X (((X.tr fT).take j1).countP _) by
      rw [hcj1]; exact hag) hcta hg hgw
  obtain ⟨c', hσi, hsite⟩ := group_arrival_site hX ht hq2 hIBg hg
  have hji : j < i := poll_before_group ht hg rfl hIBg hσi hsite (by rw [hcountg, hcj1])
  have hsame : SameCta L g fT := ⟨hg, hfl, hcta⟩
  obtain ⟨key, hk1, hk2⟩ := same_key hpre hX ht hq2 hsame hIBg hIBf hjf hcountg
  have hG1 : Resumes kernel X (g, j) (g, i) := by
    obtain ⟨ex, hspin⟩ := ht.wait_spins hg he
    exact Resumes.of_spin he hspin rfl hji (len_of_get hIBg)
  obtain ⟨key', hk', hdone⟩ := ctaBarDone_of_returned hX hIBf hjf
  obtain rfl : key = key' := CtaBarK.key_unique hX.ctaBar hk2 hk'
  obtain ⟨ic, hcomp⟩ := hdone
  have hW1 : Witness L X (.thread (g, i)) (fT, j1) :=
    Witness.of_ctaBarCounted hk2 hcomp (CtaBarK.arrival hk1) hcta
  have hG2 : Resumes kernel X (fT, j1) (ackEv L X c (firstB k q) s') :=
    Resumes.of_blocking hIBf (b := false) rfl ⟨rfl, hj1, len_of_get hea⟩
  exact (((((Relation.TransGen.single (DepStep.of_resumes L hG1)).tail
    (DepStep.of_witness L hW1)).tail (DepStep.of_resumes L hG2)).tail
    (DepStep.of_witness L hobs)).tail (DepStep.of_resumes L hgP)).trans_left
    (R.issueF f (0, s' + 1) hx)

/-- **Step 2: the phase of a consumer's response poll.** A consumer thread's successful response
poll with `n` earlier ones found phase `n + 1`: at least by the parity of its polls, at most by
the completions before it, which are of requests numbered at most `n` (`cons_chain`). -/
theorem cons_poll_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j pc p : Nat} {acq : Bool} {sc : MbarScope} (hg : g < L.threads)
    (hw : g % L.block / 32 < 8)
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hag : OutputRing.ResponsesAgreeBelow L X
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j))) :
    ∃ i w st, (X.objects (respFull L (g / L.block)))[i]? = some w ∧ w.id = .thread (g, j) ∧
      w.reply.waited = some true ∧ stateBefore (X.objects (respFull L (g / L.block))) i = some st ∧
      st.phase = okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 ∧
      observedAt (X.objects (respFull L (g / L.block))) i =
        some (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j)) := by
  classical
  set n := okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) with hn
  have he' : X.get (g, j) = some ⟨pc, .wait (respFull L (g / L.block)) p true acq sc⟩ := by
    rw [← respFull_eq]; exact he
  have hch := (hX.tma.2.2.1 (respFull L (g / L.block))).1
  have hni := objects_noInval hX ht (respFull L (g / L.block))
  have hlt : n < okPolls (respFull L (g / L.block)) (X.tr g) := by
    have h1 := MbarRing.Poll.okPoll_get he'
    have h2 := MbarRing.Poll.okPolls_mono (respFull L (g / L.block)) (X.tr g)
      (show j + 1 ≤ (X.tr g).length from len_of_get he)
    rw [List.take_length] at h2
    rw [hn, respFull_eq]
    omega
  obtain ⟨i, w, p', hi, hwid, -, hww, -, hsel⟩ :=
    MbarRing.Poll.record hX (poll_clean (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos) hlt
  have hi : (X.objects (respFull L (g / L.block)))[i]? = some w := hi
  have hwid : w.id = .thread (g, MbarRing.Poll.nth X (respFull L (g / L.block)) g n) := hwid
  have hsel : selectedBefore (objectThreadSelected g) (X.objects (respFull L (g / L.block))) i =
    n := hsel
  have hnth : MbarRing.Poll.nth X (respFull L (g / L.block)) g n = j := by
    rw [hn, respFull_eq]
    exact MbarRing.Poll.nth_eq he'
  rw [hnth] at hwid
  obtain ⟨st, hst, hge, -⟩ := hch.selected_poll_phase_ge hni (objectThreadSelected g) (δ := 0)
    (by omega) (resp_alt hpre hX ht g (2 * (g / L.block / 2) + g / L.block % 2)) hi
    (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
  have hil : i ≤ (X.objects (respFull L (g / L.block))).length :=
    (List.getElem?_eq_some_iff.mp hi).1.le
  have hle : st.phase ≤ completedTxCount ((X.objects (respFull L (g / L.block))).take i) :=
    (resp_unitTx hpre hX ht (2 * (g / L.block / 2) + g / L.block % 2)).phase_le_completed
      (by norm_num) hch hni hil hst
  have hcnt : completedTxCount ((X.objects (respFull L (g / L.block))).take i) ≤ n + 1 := by
    have h := countP_take_le_card hch.1 isDone (i := i)
      ((Finset.range (n + 1)).image (item L X (g / L.block / 2)
        ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩)) (fun k hk r hr hd => by
        obtain ⟨hf, m, ha⟩ := isDone_iff.mp hd
        obtain ⟨s, hid⟩ := item_of_completion hpre hX ht (List.mem_of_getElem? hr) ha
        have hx : ((0 : Fin 1), s) ∈ SF L X (g / L.block / 2)
            ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩ :=
          (mem_SF hX).mpr ⟨r, List.mem_of_getElem? hr, hid, hf⟩
        refine Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr ?_, hid.symm⟩
        by_contra hgt
        exact MbarRing.Round.Slot.not_before_of_reach hX (m := respFull L (g / L.block))
          (cons_chain hpre hX ht hg hw he hag hx (by omega)) ⟨k, i, r, w, hr, hid, hi, hwid, hk⟩)
    exact h.trans (Finset.card_image_le.trans (by simp))
  have hph : st.phase = n + 1 := by
    rw [hsel] at hge
    omega
  obtain ⟨st', p'', hst', -, -, hcomp⟩ := hch.okPoll hi hww
  rw [hst] at hst'
  cases hst'
  refine ⟨i, w, st, hi, hwid, hww, hst, hph, ?_⟩
  simp only [observedAt, hi, Option.bind_some, hcomp, hph]
  simp

/-- **Step 3: a consumer's successful response poll observes the request numbered by its count of
earlier successful polls.** -/
theorem poll_obs (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hag : OutputRing.ResponsesAgreeBelow L X
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j))) :
    ∃ h ki s tg, X.ClcIssue (h, ki) s tg ∧ ClcObserved L X (h, ki) (g / L.block) (g, j) ∧
      issuesBefore L X (g / L.block / 2) h ki =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) := by
  obtain ⟨iw, w, st, hw, hwid, hww, -, -, ho⟩ := cons_poll_phase hpre hX ht hg hw he hag
  obtain ⟨jd, d, hjd, hd, hdf, ha, hid, hph, -⟩ := observes_request hpre hX ht hw hww ho
  have hdm := List.mem_of_getElem? hd
  have hwf := (hX.tma.2.2.1 _).1.waited_no_fault hw hww
  have hcc : 2 * (g / L.block / 2) + g / L.block % 2 = g / L.block := by omega
  have hid' : d.id = .async (producer L X (g / L.block / 2), reqIdx L X (g / L.block / 2)
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j)))
      (.notify (.cta (g / L.block))) := by
    rw [hid]
    simp only [item, Ref.async.injEq, Part.notify.injEq, Target.cta.injEq, true_and]
    exact hcc
  obtain ⟨s, tg, hi, hct, hnot, hloc⟩ := hX.clc_notified hdm hid'
  obtain ⟨d0, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨hacq, -⟩ := (ht.sync_flags hg he hσ).1 _ _ _ _ _ rfl
  have hloc' : respFull L (g / L.block) = { s.mbar with cta := g / L.block } := hloc
  obtain ⟨pci, hei⟩ := hi
  refine ⟨_, _, s, tg, ⟨pci, hei⟩, ⟨rfl, hg, sc, _, _, ⟨rfl, s, tg, ⟨pci, hei⟩, hct, hnot, rfl⟩,
    ⟨⟨pc, p, ?_⟩, ?_⟩⟩, issuesBefore_reqIdx hei⟩
  · rw [he, hacq, ← hloc', ← respFull_eq]
  · rw [← hloc']
    exact ⟨jd, iw, d, w, _, hd, hid', hdf, hw, hwid, hwf, hww, hjd, hph, ho,
      (objects_noInval hX ht _).sameLifetime jd iw⟩

/-- The notified CTA is one of the request's targets. -/
theorem clcObs_mem {i : EvId} {c : Nat} {w : EvId} {s : Clc.Spec} {tg : List Nat}
    (ho : ClcObserved L X i c w) (hi : X.ClcIssue i s tg) : c ∈ tg := by
  obtain ⟨s1, tg1, hi1, hct1, -⟩ := ho.2.2.choose_spec.clc
  obtain ⟨-, rfl⟩ := Execution.ClcIssue.unique hi1 hi
  exact hct1

/-- The leader's cluster: the producer of cluster `c` is on the cluster's CTA 0. -/
theorem producer_cta (hpre : Pre P L mem0) (c : Nat) : producer L X c / L.block = 2 * c := by
  have h := producer_sel (X := X) hpre c
  simp only [consumerSel, decide_eq_true_eq] at h
  have h2 : ctaOf (2 : Fin 10) = 0 := rfl
  rw [h2] at h
  omega

/-- The leader scheduler is warp 10 of its CTA. -/
theorem producer_warp (hpre : Pre P L mem0) (c : Nat) : producer L X c % L.block / 32 = 10 := by
  have h := producer_sel (X := X) hpre c
  simp only [consumerSel, decide_eq_true_eq] at h
  have h2 : warpOf (2 : Fin 10) = 10 := rfl
  rw [h2] at h
  exact h.2.1

/-- **Step 6: the memory order of a consumer's response read.** Every write to the
response buffer is the request's own, or visible to it, or is ordered after the read: an earlier
request's write is visible through the poll that observed it, and a later request's write through
the proxy fence that precedes the group arrival of the same ordinal. -/
theorem cons_horder (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X)
    {g j pc p : Nat} {acq : Bool} {sc : MbarScope} (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    (hag : OutputRing.ResponsesAgreeBelow L X
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j)))
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    {h ki : Nat} {s : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue (h, ki) s tg)
    (hObs : ClcObserved L X (h, ki) (g / L.block) (g, j))
    (hcount : issuesBefore L X (g / L.block / 2) h ki =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j))
    {pcr : Nat} {src : Acc} {bs : List (Option Byte)}
    (hrd : X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩)
    (hfoot : src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta,
      0, false⟩) :
    ∀ k < src.size, ∀ other footprint bytes, X.MemWrites other footprint bytes →
      footprint.Covers (src.loc.at k) →
        other = .async (h, ki) (.write (.cta (g / L.block))) ∨
          modelCausality L X (src.loc.at k) other (.async (h, ki) (.write (.cta (g / L.block)))) ∨
            modelCausality L X (src.loc.at k) (.thread (g, j + 1)) other := by
  have hct : g / L.block ∈ tg := clcObs_mem hObs hi
  obtain ⟨pci, hei⟩ := hi
  obtain ⟨hp, hmb, hresp, -⟩ := issue_facts hpre hX ht hei hct rfl
  have hfoot' : src.SameFootprint ⟨{ s.response with cta := g / L.block }, 16, false, false, .cta,
    0, false⟩ := by
    rw [hresp]
    exact hfoot
  have hq2 : Consumer.tidOf L g / 32 / 4 < 2 := by
    show g % L.block / 32 / 4 < 2
    omega
  have hsc : ∀ h'', h'' / L.block = 2 * (g / L.block / 2) → h'' < L.threads →
      SameCluster L g h'' := by
    intro h'' hh' hlt
    refine ⟨hg, hlt, ?_⟩
    simp only [clusterOfCta_eq hpre]
    omega
  have hhc : h / L.block = 2 * (g / L.block / 2) := by
    rw [hp]
    exact producer_cta hpre _
  intro k hk other fp bytes hwr hc
  have hk16 : k < 16 := by
    rw [hfoot.2] at hk
    exact hk
  have hl : src.loc.at k = ⟨.shared, g / L.block, L.sharedBase + 144 + k⟩ := by
    rw [hfoot.1]
    rfl
  obtain ⟨⟨h', ki'⟩, s', tg', rfl, ⟨pc', hei'⟩, hct'⟩ :=
    hrw (g / L.block) k hk16 other fp bytes hwr (hl ▸ hc)
  obtain ⟨hp', hmb', -, -⟩ := issue_facts hpre hX ht hei' hct' rfl
  have hhh : h' = h := hp'.trans hp.symm
  clear hp'
  subst h'
  rcases Nat.lt_trichotomy (issuesBefore L X (g / L.block / 2) h ki')
      (issuesBefore L X (g / L.block / 2) h ki) with hlt | heq | hgt
  · -- an earlier request: the poll that observed it precedes this request
    right
    left
    obtain ⟨wo, pco, po, acqo, sco, hwo, heo, hcwo⟩ := nth_poll (X := X) (g := g) (j := j)
      (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
      (o := issuesBefore L X (g / L.block / 2) h ki') (by rw [← hcount]; exact hlt)
    obtain ⟨h2, ki2, s2, tg2, hi2, hObs2, hcount2⟩ := poll_obs hpre hX ht hg hw heo
      (agreeBelow_mono (by rw [hcwo, ← hcount]; exact hlt.le) hag)
    have hct2 := clcObs_mem hObs2 hi2
    obtain ⟨pci2, hei2⟩ := hi2
    obtain ⟨hp2, hmb2, -, -⟩ := issue_facts hpre hX ht hei2 hct2 rfl
    have hh2 : h2 = h := hp2.trans hp.symm
    clear hp2
    subst h2
    have hkk := issues_inj (c := g / L.block / 2) hei2 hei' (by simp [clcIssuesTo, hmb2])
      (by simp [clcIssuesTo, hmb']) (hcount2.trans hcwo)
    subst ki2
    obtain ⟨im, pcm, hIBm, hcountm, hbm⟩ := grp_group hpre hX ht hg hw hei hct rfl hlt
      (agreeBelow_mono (by rw [← hcount]; exact hlt.le) hag)
    obtain ⟨cm, hσm, hsitem⟩ := group_arrival_site hX ht hq2 hIBm hg
    have hwo_lt : wo < im := poll_before_group ht hg rfl hIBm hσm hsitem (hcwo.trans hcountm.symm)
    have hbwo : baseCausality L X (g, wo) (h, ki) := hbm wo hwo_lt
    have hcovers : AsyncCovers X (h, ki') (.write (.cta (g / L.block))) (src.loc.at k) :=
      ⟨fp, true, hwr.intent, hc⟩
    obtain ⟨r0, -, -, hw0⟩ := hObs.2.2.choose_spec.clc_response_write hX.clc ⟨pci, hei⟩
    refine ⟨.inl ⟨Frame.lt_of_get hX hei, Frame.lt_of_get hX hei, rfl⟩,
      .direct ⟨hcovers, ?_,
        .inl ⟨(g, wo), .inr ⟨_, hObs2.2.2.choose_spec, clcObs_scopes hX ht hObs2⟩, hbwo⟩⟩⟩
    exact ⟨_, true, hw0.intent, (hfoot'.covers _).mp (Acc.covers_at hk)⟩
  · -- this request: the same arrival
    left
    have hkk := issues_inj (c := g / L.block / 2) hei' hei (by simp [clcIssuesTo, hmb'])
      (by simp [clcIssuesTo, hmb]) heq
    subst hkk
    rfl
  · -- a later request: this read is released to it through a proxy fence before the group arrival
    right
    right
    obtain ⟨in_, pcn, hIBn, hcountn, hbn⟩ := grp_group hpre hX ht hg hw hei' hct' rfl
      (m := okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j))
      (by rw [← hcount]; exact hgt) hag
    obtain ⟨cn, hσn, hsiten⟩ := group_arrival_site hX ht hq2 hIBn hg
    have hcl := ht.cons_clc hg hIBn hσn
    have hclc1 : cn.clcHold = 1 := by simp [Consumer.D.clcHold, hsiten]
    rw [hclc1, hcountn] at hcl
    obtain ⟨jf, fe, hjfl, hfe, hfk, hokf⟩ := ht.cons_clc_fence hg hIBn hσn hsiten
    have hj1 : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take (j + 1)) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 := by
      have hjget : (X.tr g)[j]? =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ := he
      rw [List.take_add_one, hjget, Option.toList_some, okPolls_snoc, okPoll_wait rfl]
      simp
    have hjf1 : j + 1 < jf := by
      rcases Nat.lt_or_ge (j + 1) jf with h1 | h1
      · exact h1
      · exfalso
        rcases Nat.lt_or_eq_of_le h1 with h2 | h2
        · have hmono := okPolls_mono (X := X) (g := g)
            (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (show jf ≤ j by omega)
          omega
        · subst h2
          rw [hrd] at hfe
          cases hfe
          cases hfk
    have hb1 : baseCausality L X (g, j + 1) (g, jf) :=
      Relation.TransGen.single (Or.inl (po_of_not_access rfl hjf1 (len_of_get hfe)
        (Execution.get_not_access hfe hfk (fun _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))))
    have hb2 : baseCausality L X (g, jf) (h, ki') := hbn jf hjfl
    have hcovers : AsyncCovers X (h, ki') (.write (.cta (g / L.block))) (src.loc.at k) :=
      ⟨fp, true, hwr.intent, hc⟩
    refine ⟨hcovers, .inl ⟨(g, jf), some (.shared .cta), none, ⟨fe.pc, ?_⟩, hg, ⟨?_, ?_⟩,
      hsc h hhc (Frame.lt_of_get hX hei), hb1, hb2⟩⟩
    · rw [hfe]
      cases fe
      simp only at hfk
      rw [hfk]
    · rw [hl]
    · rw [hl]

/-- **The response a consumer's successful poll observes**, with the ordinal of its request. -/
theorem cons_observed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X) {g j pc p : Nat}
    {acq : Bool} {sc : MbarScope} {c : Consumer.D} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g j = some (some (.inr (.cons c))))
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hag : OutputRing.ResponsesAgreeBelow L X
      (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j))) :
    ∃ i s tg r, X.ClcIssue i s tg ∧ i.1 / L.block = 2 * (g / L.block / 2) ∧
      i.1 % L.block / 32 = 10 ∧
      ((X.tr i.1).take i.2).countP
          (clcIssuesTo (Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, true⟩)) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) ∧
      ClcObserved L X i (g / L.block) (g, j) ∧ (X.clc i).resolved = some r ∧
      ∀ pcr (src : Acc) bs, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ →
        bs = (Value.clc r).toBytes.map some := by
  have hw : g % L.block / 32 < 8 := by
    have := ht.role_warp hg (idx_le he) hσ
    simp only [roleWarp] at this
    exact this
  obtain ⟨h, ki, s, tg, hi, hObs, hcount⟩ := poll_obs hpre hX ht hg hw he hag
  obtain ⟨r, hres, -, -⟩ := hObs.2.2.choose_spec.clc_response_write hX.clc hi
  have hct := clcObs_mem hObs hi
  obtain ⟨pci, hei⟩ := hi
  have hi' : X.ClcIssue (h, ki) s tg := ⟨pci, hei⟩
  obtain ⟨hp, -, hresp, -⟩ := issue_facts hpre hX ht hei hct rfl
  have hcta := producer_cta (X := X) hpre (g / L.block / 2)
  have hwp := producer_warp (X := X) hpre (g / L.block / 2)
  rw [← hp] at hcta hwp
  refine ⟨(h, ki), s, tg, r, hi', hcta, hwp, hcount, hObs, hres, ?_⟩
  intro pcr src bs hrd hfoot
  have hread : X.MemReads (.thread (g, j + 1)) src bs := .inl ⟨pcr, hrd⟩
  have hjr : j + 1 < (X.tr g).length := len_of_get hrd
  have hhb : baseCausality L X (g, j) (g, j + 1) :=
    .single (.inl (po_of_source_not_access rfl (by omega) hjr (by simp [he, Event.acc])))
  have hfoot' : src.SameFootprint ⟨{ s.response with cta := g / L.block }, 16, false, false, .cta,
    0, false⟩ := by
    rw [hresp]
    exact hfoot
  obtain ⟨r', hres', -, hbytes⟩ :=
    hObs.2.2.choose_spec.clc_read_bytes_of_ordered_reuse hX hi' hread hfoot'
      (clcObs_scopes hX ht hObs) hhb
    (cons_horder hpre hX ht hrw hg hw hag he hi' hObs hcount hrd hfoot)
  rw [hres] at hres'
  cases hres'
  exact hbytes

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
