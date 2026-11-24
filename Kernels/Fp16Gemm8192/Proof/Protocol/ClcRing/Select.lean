-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Slot
public import Lemmas.Protocol.Poller
public import Lemmas.Protocol.ClcNotify

@[expose] public section

/-! # The threads of the CLC response ring

Every record of a cluster's response and acknowledgement barriers arises as `BarSource` says
(`full_src`, `empty_src`). Two threads of one consumer selector that use the ring's objects in
role states are one (`sel_eq`): the selector's lane-0 thread, or its warp's elected lane. The
leader scheduler (`producer`, the selector of consumer 2 polling the acknowledgement barrier)
issues every cancellation request of its cluster, on its CTA's response barrier, after one more
successful acknowledgement poll than its earlier requests (`issue_facts`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A fault-free arrival expecting the response's bytes. -/
def isArrival (q : Record Ref) : Bool := decide (q.action = .arrive 1 16 ∧ q.fault = none)

/-- A fault-free completion of one response. -/
def isCompletion (q : Record Ref) : Bool := decide (q.action = .completeTx 16 ∧ q.fault = none)

theorem isArrival_iff (q : Record Ref) :
    isArrival q = true ↔ q.action = .arrive 1 16 ∧ q.fault = none := by
  simp [isArrival]

theorem isCompletion_iff (q : Record Ref) :
    isCompletion q = true ↔ q.action = .completeTx 16 ∧ q.fault = none := by
  simp [isCompletion]

/-- The source of a record of response barrier `k`. -/
theorem full_src (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {k : Fin 2} {r : Record Ref} (hr : r ∈ X.objects ((slot L c).full k)) :
    BarSource L X ⟨.clc, 0, true⟩ (2 * c + k.val) r :=
  bar_source (b := ⟨.clc, 0, true⟩) hX ht Nat.one_pos hr

/-- The state an arrival on a ring barrier fires from. -/
theorem arrive_role (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g k : Nat}
    {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) {b : Bar} {cta tx n : Nat} {rel : Bool} {sc : MbarScope}
    (hk : e.kind = .arrive (b.loc L cta) tx n rel sc) (hb : b.Valid) :
    ∃ r, Frame.stateAt (code L) X g k = some (some (.inr r)) ∧ roleWarp (g % L.block / 32) r := by
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by rintro pc f rfl; cases hk)
  obtain ⟨hby, -⟩ := (ht.ring_event hg he hσ).arrive _ _ _ _ _ _ hk hb
  obtain ⟨r, rfl⟩ := Bar.role_of (.inr (.inl hby))
  exact ⟨r, hσ, ht.role_warp hg (idx_le he) hσ⟩

/-- The election site of the roles of the elected warps. -/
theorem electPc_of_warp {w : Nat} {r : Prologue.Role} (hr : roleWarp w r) (hw : 8 ≤ w) :
    r.electPc = some (if w = 11 then Prologue.Site.roleElect.pc
      else if w = 10 then Scheduler.Site.elect.pc else Mma.Site.elect.pc) := by
  cases r with
  | loader l => simp only [roleWarp] at hr; subst hr; rfl
  | sched s => simp only [roleWarp] at hr; subst hr; rfl
  | mma m =>
    simp only [roleWarp] at hr
    obtain ⟨-, h | h⟩ := hr <;> subst h <;> rfl
  | cons c => simp only [roleWarp] at hr; omega

/-- Two threads of one consumer's selector that use mbarriers in role states are one. -/
theorem sel_unique (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g h j k : Nat} {e f : Event}
    {r r' : Prologue.Role} (hg : consumerSel L c b g = true) (hh : consumerSel L c b h = true)
    (he : X.get (g, j) = some e) (hf : X.get (h, k) = some f)
    (hσ : Frame.stateAt (code L) X g j = some (some (.inr r)))
    (hσ' : Frame.stateAt (code L) X h k = some (some (.inr r')))
    (hrw : roleWarp (g % L.block / 32) r) (hrw' : roleWarp (h % L.block / 32) r')
    (hke : ObjectKind e.kind) (hkf : ObjectKind f.kind) : g = h := by
  have hblock := hpre.block
  simp only [consumerSel, decide_eq_true_eq] at hg hh
  by_cases hz : laneZero b = true
  · have h1 := hg.2.2 hz
    have h2 := hh.2.2 hz
    have h3 := hg.1.trans hh.1.symm
    have h4 := hg.2.1.trans hh.2.1.symm
    rw [hblock] at h3 h4
    omega
  · have key : ∀ b : Fin 10, laneZero b = false → 8 ≤ warpOf b := by decide
    have hw8 : 8 ≤ warpOf b := key b (by simpa using hz)
    rw [hg.2.1] at hrw
    rw [hh.2.1] at hrw'
    exact elected_unique hX ht (hg.1.trans hh.1.symm) (hg.2.1.trans hh.2.1.symm) he hf hσ hσ'
      (electPc_of_warp hrw hw8) (electPc_of_warp hrw' hw8) hke hkf

/-- A thread of the cluster's ten consumers that arrives on the acknowledgement barrier
belongs to one of their selectors. -/
theorem sel_of_ack (hpre : Pre P L mem0) {c g : Nat} {r : Prologue.Role}
    (hby : Bar.arriveBy L g (.inr r) ⟨.clc, 0, false⟩) (hrw : roleWarp (g % L.block / 32) r)
    (hc : g / L.block / 2 = c) : ∃ b, consumerSel L c b g = true := by
  have hblock := hpre.block
  simp only [Bar.arriveBy] at hby
  rcases hby with ⟨l, hl⟩ | ⟨⟨mm, hm⟩, hlead⟩ | ⟨sd, hs⟩ | ⟨⟨cs, hcs⟩, hfirst⟩
  · cases hl
    simp only [roleWarp] at hrw
    refine ⟨⟨g / L.block - 2 * c, by simp only [hblock] at *; omega⟩, ?_⟩
    simp only [consumerSel, decide_eq_true_eq]
    rcases (by omega : g / L.block - 2 * c = 0 ∨ g / L.block - 2 * c = 1) with h | h <;>
      simp only [h] <;> simp [ctaOf, warpOf, laneZero] <;> simp only [hblock] at * <;> omega
  · cases hm
    simp only [roleWarp] at hrw
    refine ⟨⟨4 + (g % L.block / 32 - 8), by simp only [hblock] at *; omega⟩, ?_⟩
    simp only [consumerSel, decide_eq_true_eq]
    rcases hrw.2 with h | h <;> simp only [h] <;> simp [ctaOf, warpOf, laneZero] <;>
      simp only [hblock] at * <;> omega
  · cases hs
    simp only [roleWarp] at hrw
    refine ⟨⟨2 + (g / L.block - 2 * c), by simp only [hblock] at *; omega⟩, ?_⟩
    simp only [consumerSel, decide_eq_true_eq]
    rcases (by omega : g / L.block - 2 * c = 0 ∨ g / L.block - 2 * c = 1) with h | h <;>
      simp only [h] <;> simp [ctaOf, warpOf, laneZero] <;> simp only [hblock] at * <;> omega
  · cases hcs
    simp only [roleWarp] at hrw
    simp only [Consumer.first, Consumer.tidOf, decide_eq_true_eq, Nat.or_eq_zero_iff] at hfirst
    refine ⟨⟨6 + 2 * (g / L.block - 2 * c) + g % L.block / 128, by simp only [hblock] at *; omega⟩,
      ?_⟩
    simp only [consumerSel, decide_eq_true_eq]
    rcases (by omega : g / L.block - 2 * c = 0 ∨ g / L.block - 2 * c = 1) with h | h <;>
      rcases (by omega : g % L.block / 128 = 0 ∨ g % L.block / 128 = 1) with h' | h' <;>
      simp only [h, h'] <;> simp [ctaOf, warpOf, laneZero] <;> simp only [hblock] at * <;> omega

/-- A selector's polls and arrivals on the ring are one thread's: a thread of the selector
that polls a response barrier or arrives on a ring barrier is `g`, when `g` of the selector
does too. -/
theorem sel_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g h j k : Nat} {e f : Event}
    (hg : consumerSel L c b g = true) (hh : consumerSel L c b h = true)
    (he : X.get (g, j) = some e) (hf : X.get (h, k) = some f)
    (hge : ∃ r, Frame.stateAt (code L) X g j = some (some (.inr r)) ∧ roleWarp (g % L.block / 32) r)
    (hke : ObjectKind e.kind) (hkf : ObjectKind f.kind)
    (hhf : ∃ r, Frame.stateAt (code L) X h k = some (some (.inr r)) ∧
      roleWarp (h % L.block / 32) r) :
    h = g := by
  obtain ⟨r, hσ, hrw⟩ := hge
  obtain ⟨r', hσ', hrw'⟩ := hhf
  exact (sel_unique hpre hX ht hg hh he hf hσ hσ' hrw hrw' hke hkf).symm

/-- The role state of a thread's successful poll of a response barrier. -/
theorem poll_state (ht : ThreadFacts L X) {g j pc p cta : Nat} {acq : Bool} {sc : MbarScope}
    (hX : Consistent L kernel Prod mem0 X)
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L cta ⟨.clc, 0, true⟩) p true acq sc⟩) :
    ∃ r, Frame.stateAt (code L) X g j = some (some (.inr r)) ∧ roleWarp (g % L.block / 32) r := by
  obtain ⟨r, hσ, hrw⟩ := wait_role hX ht (Frame.lt_of_get hX he) he rfl
  exact ⟨r, hσ, hrw⟩

/-- The leader scheduler: the thread of selector 2 that polls the acknowledgement barrier. -/
def producer (L : Launch) (X : Execution) (c : Nat) : Nat :=
  pollerOf X (consumerSel L c 2) ((slot L c).empty 0) (2 * c * L.block + 32 * 10)

theorem producer_sel (hpre : Pre P L mem0) (c : Nat) : consumerSel L c 2 (producer L X c) = true :=
    by
  have hblock := hpre.block
  refine pollerOf_sel ?_
  simp only [consumerSel, decide_eq_true_eq, hblock]
  simp [ctaOf, warpOf, laneZero]
  omega

theorem producer_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hg : consumerSel L c 2 g = true)
    (he : X.get (g, j) = some ⟨pc, .wait ((slot L c).empty 0) p true acq sc⟩) :
    g = producer L X c := by
  refine pollerOf_eq (fun hg hh he he' => ?_) hg he
  exact (sel_eq hpre hX ht hg hh he he' (wait_role hX ht (Frame.lt_of_get hX he) he rfl) trivial
    trivial (wait_role hX ht (Frame.lt_of_get hX he') he' rfl)).symm

/-- The cancellation requests of cluster `c`'s leader before its event `k`. -/
def issuesBefore (L : Launch) (X : Execution) (c h k : Nat) : Nat :=
  ((X.tr h).take k).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩))

/-- A cancellation request targeting a CTA of cluster `c` is the cluster's leader scheduler's,
on its CTA's response barrier and response buffer, issued after more successful acknowledgement
polls than its earlier requests. -/
theorem issue_facts (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c h ki pc cta : Nat} {sp : Clc.Spec} {tg : List Nat}
    (he : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) (hct : cta ∈ tg) (hcc : cta / 2 = c) :
    h = producer L X c ∧ sp.mbar = Bar.loc L (2 * c) ⟨.clc, 0, true⟩ ∧
      sp.response = ⟨.shared, 2 * c, L.sharedBase + 144⟩ ∧
      issuesBefore L X c h ki + 1 ≤ okPolls ((slot L c).empty 0) ((X.tr h).take ki) := by
  have hblock := hpre.block
  have hh := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨b, hb, hby, hmb, hresp, hcl⟩ := (ht.ring_event hh he hσ).clc _ _ rfl
  obtain ⟨rg, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  obtain rfl : s = 0 := by omega
  obtain ⟨⟨sd, rfl⟩, hlead⟩ := hby
  have hw := ht.role_warp hh (idx_le he) hσ
  simp only [roleWarp] at hw
  have hcta' : h / L.block = 2 * c := by have := hcl cta hct; omega
  have hsel : consumerSel L c 2 h = true := by
    simp only [consumerSel, decide_eq_true_eq]
    simp [ctaOf, warpOf, laneZero]
    omega
  have hcb := ht.clc_budget (b := ⟨.clc, 0, true⟩) hh he hσ rfl hmb Nat.one_pos
  have hloc : (Bar.partner ⟨.clc, 0, true⟩).loc L (h / L.block) = (slot L c).empty 0 := by
    simp only [Bar.partner, Bool.not_true, slot, hcta']
  rw [hloc, hmb, hcta'] at hcb
  simp only [Bar.issues, Nat.one_mul] at hcb
  obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := h) (k := ki)
    (m := (slot L c).empty 0) (by omega)
  refine ⟨producer_eq hpre hX ht hsel he', by rw [hmb, hcta'], by rw [hresp, hcta']; rfl, hcb⟩

/-- A completion of a response barrier is the notification of a request of the cluster's leader
scheduler. -/
theorem issuer (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {k : Fin 2} {d : Record Ref}
    (hd : d ∈ X.objects ((slot L c).full k)) {h ki : Nat}
    (hid : d.id = .async (h, ki) (.notify (.cta (2 * c + k.val)))) :
    h = producer L X c ∧ (∃ pc sp tg, X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩ ∧
      sp.mbar = Bar.loc L (2 * c) ⟨.clc, 0, true⟩) ∧
      issuesBefore L X c h ki + 1 ≤ okPolls ((slot L c).empty 0) ((X.tr h).take ki) := by
  obtain ⟨s, tg, ⟨pc, he⟩, hct, -, -⟩ := hX.clc_notified hd hid
  obtain ⟨hp, hmb, -, hcb⟩ := issue_facts (c := c) hpre hX ht he hct (by have := k.isLt; omega)
  exact ⟨hp, ⟨pc, s, tg, he, hmb⟩, hcb⟩

/-- Two requests of one thread with the same number of earlier requests are one event. -/
theorem issues_inj {h k1 k2 : Nat} {c : Nat} {e1 e2 : Event}
    (he1 : X.get (h, k1) = some e1) (he2 : X.get (h, k2) = some e2)
    (hi1 : clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩) e1 = true)
    (hi2 : clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩) e2 = true)
    (heq : issuesBefore L X c h k1 = issuesBefore L X c h k2) : k1 = k2 := by
  have key : ∀ {a b : Nat} {ea : Event}, X.get (h, a) = some ea →
      clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩) ea = true → a < b → b ≤ (X.tr h).length →
      issuesBefore L X c h a + 1 ≤ issuesBefore L X c h b := by
    intro a b ea hea hia hab hb
    have hal : a < (X.tr h).length := len_of_get hea
    have hsub := List.Sublist.countP_le (p := clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩))
      (List.take_sublist_take_left (l := X.tr h) (show a + 1 ≤ b by omega))
    unfold issuesBefore
    rw [List.take_add_one, List.countP_append] at hsub
    have : (X.tr h)[a]? = some ea := hea
    rw [this] at hsub
    simp [hia] at hsub
    omega
  rcases Nat.lt_trichotomy k1 k2 with h12 | h12 | h12
  · have := key he1 hi1 h12 (len_of_get he2).le
    omega
  · exact h12
  · have := key he2 hi2 h12 (len_of_get he1).le
    omega

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
