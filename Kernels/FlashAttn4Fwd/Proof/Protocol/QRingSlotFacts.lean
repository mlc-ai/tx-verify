-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlot
public import Lemmas.Protocol.PairTmaRing.Faults
public import Lemmas.Protocol.PairTmaRing.Ordered
public import Lemmas.Protocol.PairTmaRing.Blocker
public import Lemmas.Protocol.PairTmaRing.Drain

@[expose] public section

/-! # The facts of a Q or KV ring slot

The generic facts of a slot of either ring (`Rings.slot L X c b`, `b` a full barrier), from the
pair TMA ring library under `hyp`; `QRing` and `KvRing` state them per stage and slot.

* **Fault freedom** (`ring_fault_free`): every record of every ring barrier of every CTA is
  fault-free, the drain's arrival on `qFull 1` without copies included. The even CTA's barriers
  are a slot's; the odd CTA's full barriers have no record but their initialization.
* **Bytes ordered** (`bytes_ordered`, `modelCausality_ordered`): a copy and an MMA read of one byte
  of a ring region are of one slot; numbering the copy by its use (`copyUse`: its thread's earlier
  copies on the slot over the copies per use) and the read by its use (`readUse`: its thread's
  earlier commits to the slot), the copy precedes the read when its use is at most the read's, and
  follows it otherwise.
* **Blockers** (`empty_blocked`, `full_blocked`): a producer whose empty barrier ends in the
  phase its next poll does not find has one use outstanding, and the consumer notified exactly
  that phase; the full barrier's last phase awaits the leader's arrival or a copy.
* **The drain** (`drain_unobserved`): after a producer's drain (`RingFacts.drain`) the consumer
  completed no poll of the full barrier for the use the drain released, so the drain's arrival
  on `qFull 1` without copies leaves an unobserved phase; so the producer's drain poll, its last
  successful poll of its empty barrier, has every notification of the barrier before its record
  (`drain_observes`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace Rings

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Regions -/

/-- The regions of two full barriers of the rings meet only when they are one region. -/
theorem region_inj {b b' : FBar} {c c' : Nat} {l : Loc} (hb : b.isFull) (hb' : b'.isFull)
    (h : InRegion L c b l) (h' : InRegion L c' b' l) : b = b' ∧ c = c' := by
  obtain ⟨-, hc, h1, h2⟩ := h
  obtain ⟨-, hc', h1', h2'⟩ := h'
  refine ⟨?_, hc.symm.trans hc'⟩
  cases b <;> cases b' <;> simp_all [FBar.isFull, FBar.regionOff, FBar.regionSize] <;> omega

/-! ### Fault freedom -/

theorem isFull_or_isEmpty {b : FBar} (h : b.ring) : b.isFull ∨ b.isEmpty := by
  cases b <;> simp_all [FBar.ring, FBar.isFull, FBar.isEmpty]

theorem partner_isFull {b : FBar} (h : b.isEmpty) : b.partner.isFull := by
  cases b <;> simp_all [FBar.isEmpty, FBar.isFull, FBar.partner]

theorem partner_partner' {b : FBar} (h : b.isEmpty) : b.partner.partner = b := by
  cases b <;> simp_all [FBar.isEmpty, FBar.partner]

/-- The odd CTA's full barriers have no record but their initialization. -/
theorem odd_full_init (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X)
    (htm : TmemFacts L X) {b : FBar} (hb : b.isFull) {cta : Nat} (hodd : cta % 2 = 1)
    {r : Record Ref} (hr : r ∈ X.objects (b.loc L cta)) : ∃ n, r.action = .init n := by
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact ⟨_, ha⟩
  | inval _ he _ => exact absurd he htm.no_inval
  | wait _ he _ =>
    obtain ⟨hc, h1, -⟩ := ht.poll (Frame.lt_of_get hX he) he (isFull_ring hb)
    have := (h1 hb).2
    omega
  | arrive _ he _ =>
    obtain ⟨-, hc, h0, -⟩ := ht.arrive (Frame.lt_of_get hX he) he (isFull_ring hb)
    omega
  | tensor _ he hm _ =>
    obtain ⟨-, hc, -⟩ := ht.issue (Frame.lt_of_get hX he) he hm (isFull_ring hb)
    unfold pairBase at hc
    omega
  | increment _ he _ => exact absurd he htm.no_arriveOn
  | arriveOn _ he _ _ _ => exact absurd he htm.no_arriveOn
  | bulk _ he _ _ _ => exact absurd he htm.no_bulk
  | commit _ he htg _ =>
    have := (ht.commit (Frame.lt_of_get hX he) he htg (isFull_ring hb)).1
    rw [not_isEmpty hb] at this
    cases this
  | clc _ he _ _ _ => exact absurd he htm.no_clc

/-- **Every record of every ring barrier is fault-free.** -/
theorem ring_fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : RingInit L X) {b : FBar} (hb : b.ring)
    (cta : Nat) {r : Record Ref} (hr : r ∈ X.objects (b.loc L cta)) : r.fault = none := by
  rcases isFull_or_isEmpty hb with hf | he
  · by_cases hodd : cta % 2 = 1
    · obtain ⟨n, ha⟩ := odd_full_init hX ht htm hf hodd hr
      obtain ⟨r0, -, -, hf0, hu⟩ := hinit cta b hb r hr
      rw [hu r hr ⟨n, ha⟩]
      exact hf0
    · have hc : cta = 2 * (cta / 2) := by omega
      have H := hyp hpre hX ht htm hinit hf (cta / 2)
      rw [hc] at hr
      exact PairTmaRing.fault_free hX H (.inl rfl) hr
  · have H := hyp hpre hX ht htm hinit (partner_isFull he) (cta / 2)
    have hm : b.loc L cta = (slot L X (cta / 2) b.partner).empty
        ⟨cta % 2, Nat.mod_lt _ (by decide)⟩ := by
      simp only [slot, partner_partner' he]
      congr 1
      omega
    rw [hm] at hr
    exact PairTmaRing.fault_free hX H (.inr ⟨_, rfl⟩) hr

/-! ### Bytes ordered -/

/-- The use of copy `i` on slot `b` of pair `c`: its thread's earlier copies on the slot over the
copies per use. -/
def copyUse (L : Launch) (X : Execution) (c : Nat) (b : FBar) (i : EvId) : Nat :=
  ((X.tr i.1).take i.2).countP (issuesTo (b.loc L (2 * c))) / b.copies

/-- The use of MMA `i` reading slot `b` of pair `c`: its thread's earlier commits to the slot. -/
def readUse (L : Launch) (X : Execution) (c : Nat) (b : FBar) (i : EvId) : Nat :=
  ((X.tr i.1).take i.2).countP (commitsTo (b.partner.loc L (2 * c)))

/-- A `cta_group::2` MMA or copy is a Tensor Core asynchronous operation. -/
theorem tcAsync_of_pairTc {i : EvId} (h : PairTc X i) : X.TcAsync i :=
  h.elim (fun ⟨d, s, a, m, hm, _⟩ => .inl ⟨d, s, a, m, hm⟩) fun ⟨c, hc, _⟩ => .inr (.inl ⟨c, hc⟩)

theorem lt_of_pairTc (hX : Consistent L kernel asms mem0 X) {i : EvId} (h : PairTc X i) :
    i.1 < L.threads := by
  obtain ⟨g, k⟩ := i
  rcases h with ⟨d, sp, ac, mk, ⟨pc, he⟩, -⟩ | ⟨c, ⟨pc, he⟩, -⟩ <;>
    exact Frame.lt_of_get hX he

/-- A copy writing a byte of slot `b`'s region in CTA `cta` is a producer's copy on the slot of
pair `cta / 2`. -/
theorem write_slot (ht : RingFacts L X) {b : FBar}
    (hb : b.isFull) {cta gl kl x y z : Nat} {l : Loc} (hl : InRegion L cta b l)
    (hw : AsyncCovers X (gl, kl) (.write (.load x y z)) l) :
    ∃ pc al sp, X.get (gl, kl) = some ⟨pc, .tensorIssue al sp⟩ ∧
      sp.mbar = b.loc L (2 * (cta / 2)) ∧ ctaOf L gl = cta := by
  obtain ⟨pc, al, sp, b', he, hb', hm, hl'⟩ := ht.write hw
  obtain ⟨rfl, hc⟩ := region_inj hb' hb hl' hl
  refine ⟨pc, al, sp, he, ?_, hc⟩
  rw [hm, pairBase, hc]

/-- An MMA reading a byte of slot `b`'s region in CTA `cta` is the consumer of the slot of pair
`cta / 2`. -/
theorem read_slot (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X) {b : FBar}
    (hb : b.isFull) {cta gm km idx : Nat} {isB : Bool} {l : Loc} (hl : InRegion L cta b l)
    (hr : AsyncCovers X (gm, km) (.mmaRead isB idx) l) :
    PairTc X (gm, km) ∧ gm = (slot L X (cta / 2) b).cons 0 ∧
      readUse L X (cta / 2) b (gm, km) + 1 ≤
        okPolls (b.loc L (2 * (cta / 2))) ((X.tr gm).take km) := by
  obtain ⟨hT, hw, hc, hlead, hbud⟩ := ht.read hr hb hl
  have hg := lt_of_pairTc hX hT
  have h := leadOf_eq hX hg hlead
  rw [hw, hc] at h
  rw [hc] at hbud
  exact ⟨hT, h.symm, hbud⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X)
    (htm : TmemFacts L X) (hinit : RingInit L X) {b : FBar}
include hpre hX ht htm hinit

/-- **A copy and an MMA read of one ring byte are ordered by their uses**: the copy precedes
the read when its use is at most the read's, and follows it otherwise. -/
theorem bytes_ordered (hb : b.isFull) {cta gl kl gm km x y z idx : Nat} {isB : Bool} {l : Loc}
    (hl : InRegion L cta b l) (hw : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hr : AsyncCovers X (gm, km) (.mmaRead isB idx) l) :
    (copyUse L X (cta / 2) b (gl, kl) ≤ readUse L X (cta / 2) b (gm, km) →
      AsyncBefore L X l ((gl, kl), .write (.load x y z)) ((gm, km), .mmaRead isB idx)) ∧
    (readUse L X (cta / 2) b (gm, km) < copyUse L X (cta / 2) b (gl, kl) →
      AsyncBefore L X l ((gm, km), .mmaRead isB idx) ((gl, kl), .write (.load x y z))) := by
  have H := hyp hpre hX ht htm hinit hb (cta / 2)
  obtain ⟨pc, al, sp, he, hm, -⟩ := write_slot ht hb hl hw
  obtain ⟨hT, hgm, hpol⟩ := read_slot hX ht hb hl hr
  subst hgm
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · exact PairTmaRing.copy_before_read hX H (PairTmaRing.tcAsync_lt (tcAsync_of_pairTc hT)) he hm
      ((Nat.add_le_add_right hle 1).trans hpol) hw hr
  · obtain ⟨a, rfl, -, -, hbud⟩ := full_issue hX ht hb he hm
    rw [ctaOf_lead hpre a] at hbud
    have hq : copyUse L X (cta / 2) b ((slot L X (cta / 2) b).prod a, kl) <
        okPolls (b.partner.loc L (2 * (cta / 2) + a.val))
          ((X.tr ((slot L X (cta / 2) b).prod a)).take kl) := by
      unfold copyUse
      dsimp only
      exact (Nat.div_lt_iff_lt_mul (copies_pos hb)).mpr (by rw [Nat.mul_comm _ b.copies]; omega)
    refine (PairTmaRing.read_before_copy hX H (tcAsync_of_pairTc hT) he ?_ hr hw).1
    rw [PairTmaRing.commits_tcAsync_succ (tcAsync_of_pairTc hT)]
    have h2 : readUse L X (cta / 2) b ((slot L X (cta / 2) b).cons 0, km) + 2 ≤
        okPolls (b.partner.loc L (2 * (cta / 2) + a.val))
          ((X.tr ((slot L X (cta / 2) b).prod a)).take kl) := by omega
    exact h2

/-- **The ordered pair as visibility**: a copy and an MMA read of one ring byte are ordered one
way or the other (`modelCausality`, the async-to-async order of a `cta_group::2` pair). -/
theorem modelCausality_ordered (hb : b.isFull) {cta gl kl gm km x y z idx : Nat} {isB : Bool}
    {l : Loc} (hl : InRegion L cta b l) (hw : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hr : AsyncCovers X (gm, km) (.mmaRead isB idx) l) :
    modelCausality L X l (.async (gl, kl) (.write (.load x y z)))
        (.async (gm, km) (.mmaRead isB idx)) ∨
      modelCausality L X l (.async (gm, km) (.mmaRead isB idx))
          (.async (gl, kl) (.write (.load x y z)))
      := by
  obtain ⟨h1, h2⟩ := bytes_ordered hpre hX ht htm hinit hb hl hw hr
  obtain ⟨pc, al, sp, he, -, hcl⟩ := write_slot ht hb hl hw
  obtain ⟨hT, hgm, -⟩ := read_slot hX ht hb hl hr
  have hgl := Frame.lt_of_get hX he
  have hgm' := lt_of_pairTc hX hT
  have hcm : ctaOf L gm = 2 * (cta / 2) := by rw [hgm]; exact ctaOf_cons hpre 0
  have hgr := hpre.grid
  have hcg := cta_lt hgl
  have hcg' := cta_lt hgm'
  have hsc : ∀ {u v : Nat}, u < L.grid → v < L.grid → u / 2 = v / 2 →
      SameCtaGroup L .two u v := by
    intro u v hu hv huv
    rw [sameCtaGroup_iff]
    refine ⟨⟨hu, hv, ?_⟩, ?_⟩
    · simp [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster, huv]
    · simp only [Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster, CtaGroup.size]
      omega
  have hlc : l.cta < L.grid := by rw [hl.2.1, ← hcl]; exact hcg
  have hlg : l.cta / 2 = ctaOf L gl / 2 := by rw [hl.2.1, hcl]
  have hmg : ctaOf L gm / 2 = ctaOf L gl / 2 := by rw [hcm, hcl]; omega
  have hp1 : PairAsync L l gl gm :=
    ⟨hl.1, hsc hcg hcg' hmg.symm, hsc hcg hlc hlg.symm⟩
  have hp2 : PairAsync L l gm gl :=
    ⟨hl.1, hsc hcg' hcg hmg, hsc hcg' hlc (hlg.trans hmg.symm).symm⟩
  by_cases hle : copyUse L X (cta / 2) b (gl, kl) ≤ readUse L X (cta / 2) b (gm, km)
  · exact .inl (modelCausality_pair_direct hp1 (.inr hT) (h1 hle))
  · exact .inr (modelCausality_pair_direct hp2 (.inl hT) (h2 (by omega)))

/-! ### Blockers and the drain -/

/-- **A blocked full barrier awaits its arrival or a copy.** -/
theorem full_blocked (hb : b.isFull) (c : Nat) {before : State}
    (hstate : stateBefore (X.objects (b.loc L (2 * c))) (X.objects (b.loc L (2 * c))).length =
      some before) :
    arrivalUnits (X.objects (b.loc L (2 * c))) = before.phase ∨
      (arrivalUnits (X.objects (b.loc L (2 * c))) = before.phase + 1 ∧
        completedTxCount (X.objects (b.loc L (2 * c))) < 2 * b.copies * (before.phase + 1)) :=
  PairTmaRing.full_short hX (hyp hpre hX ht htm hinit hb c) hstate

end Rings

end
end PTX.Kernels.FlashAttn4Fwd.Proof
