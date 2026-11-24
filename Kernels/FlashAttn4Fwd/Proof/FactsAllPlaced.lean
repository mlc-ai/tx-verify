-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.FactsAllCross
public import Kernels.FlashAttn4Fwd.Proof.SafeFacts
public import Kernels.FlashAttn4Fwd.Proof.ProgressSources
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaExit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccessRoles
public import Lemmas.Flow.NotNc
public import Lemmas.Tcgen05.MmaBytePair

@[expose] public section

/-! # The placement of the accesses and the tensor stores' boxes

The fields `storeBoxes`, `sharedPlaced`, `globalPlaced` and `globalWrites` of `ThreadInputs`, from
the thread layer's structures:

* **Boxes** (`storeBoxes`). Every tensor store is the store of an O map box at column `64 hh`
  (`StoreFacts.spec`), which starts 16-byte aligned (`Safety.tile_aligned`).
* **No non-coherent read** (`no_nc`). The kernel's assumptions allow no non-coherent load, so no
  event is one (`fires_not_nc`).
* **Shared bytes** (`sharedPlaced`). An access covering a shared byte is a thread's access, an MMA
  operand read, a tensor store's source read or a tensor load's write (`Execution.shared_intent`;
  the kernel has no CLC request and no bulk copy). A thread's access is of its own CTA
  (`AsyncFacts.access_own`), by a softmax thread to the statistics words
  (`Cross.soft_access_range`), by a correction thread to the statistics words or the staging
  buffers (`Cross.corr_access_range`), or by the MMA warp to the base word (`mma_access`); no other
  warp accesses memory (`Cross.access_warp13`). An MMA operand read is in a ring region of a CTA
  of its issuer's pair (`MmaReadsRings`, `RingFacts.read`); a tensor store reads a staging buffer
  of its CTA (`StoreSrc`); a tensor load writes a ring region of its CTA (`RingFacts.write`).
* **Global bytes** (`globalPlaced`, `globalWrites`). A thread accesses shared memory only
  (`OlderFacts.access_shared`). A tensor load reads an element byte of Q, K or V
  (`SmemElements.copy_readLoc`); a tensor store writes an element byte of O (as
  `Result.slot_write`). The other asynchronous accesses are of shared memory, or are absent from
  the kernel (no reduction, prefetch, CLC request or bulk copy). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Placed

/-- A footprint slot's indices are the slot's coordinates. -/
theorem slotAt_val {outer : Nat} {d : TensorDescriptor.Descriptor outer} {x y k : Nat}
    {slot : TensorTransfer.Slot d} (h : TensorTransfer.slotAt d x y k = some slot) :
    slot.1.val = x ∧ slot.2.1.val = y ∧ slot.2.2.val = k := by
  unfold TensorTransfer.slotAt at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **An element byte of a tensor lies in the tensor.** -/
theorem element_inTensor {base rows batch head row d k : Nat} (hb : batch < P.b)
    (hh : head < P.h) (hr : row < rows) (hd : d < 128) (hk : k < 2) :
    Safety.InTensor P base rows ((elementLoc P base rows batch head row d).at k) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [elementLoc, Loc.at]
    omega
  simp only [elementLoc, Loc.at, tensorBytes]
  have h1 : ((batch * rows + row) * P.h + head) * 128 + d < P.b * rows * P.h * 128 := by
    have e1 : batch * rows + row < P.b * rows := by
      calc batch * rows + row < batch * rows + rows := by omega
        _ = (batch + 1) * rows := by ring
        _ ≤ P.b * rows := Nat.mul_le_mul_right _ hb
    have e2 : (batch * rows + row) * P.h + head < P.b * rows * P.h := by
      calc (batch * rows + row) * P.h + head < (batch * rows + row) * P.h + P.h := by omega
        _ = (batch * rows + row + 1) * P.h := by ring
        _ ≤ P.b * rows * P.h := Nat.mul_le_mul_right _ e1
    omega
  have e3 : 256 * P.b * P.h * rows = P.b * rows * P.h * 128 * 2 := by ring
  omega

/-- A ring region is in the Q ring or the KV ring. -/
theorem region_rings {c : Nat} {b : FBar} {l : Loc} (hb : b.isFull) (h : InRegion L c b l) :
    Safety.InQRing L l ∨ Safety.InKvRing L l := by
  obtain ⟨hs, -, h1, h2⟩ := h
  cases b with
  | qFull st =>
    have := st.isLt
    simp only [FBar.regionOff, FBar.regionSize] at h1 h2
    exact .inl ⟨hs, by omega, by omega⟩
  | kvFull s =>
    have := s.isLt
    simp only [FBar.regionOff, FBar.regionSize] at h1 h2
    exact .inr ⟨hs, by omega, by simp only [sharedBytes]; omega⟩
  | _ => cases hb

/-- The thread of an access is launched. -/
theorem access_lt (hX : Consistent L kernel asms mem0 X) {g k : Nat} {a : Acc} {w : Bool}
    (h : X.Access (g, k) a w) : g < L.threads := by
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩ <;>
    exact Frame.lt_of_get hX he

/-- The kernel's assumptions allow no non-coherent load. -/
theorem asms_noNc (pc : Nat) : asms.any (·.ncLoads pc) = false := by
  simp [asms, Assumptions.all, Assumptions.idealArith, Assumptions.clusterMbar,
    Assumptions.approx, Assumptions.swExp2, Assumptions.peerBit, Assumptions.tcLd,
    Assumptions.commitOrder, Assumptions.pollAgree, Assumption.idealReal,
    Assumption.clusterScopeMbarAt, Assumption.approxExact, Assumption.segmentExact,
    Assumption.pairEvenAt, Assumption.tcLdDataflowAt, Assumption.commitOrderAt,
    Assumption.pollAgreeAt]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- **No event is a non-coherent read.** -/
theorem no_nc {i : EvId} {a : Acc} {bs : List (Option Byte)} : ¬ X.NcReads i a bs := by
  rintro ⟨pc, he⟩
  obtain ⟨d, t, ins, o, -, -, -, -, -, hf⟩ :=
    event_origin hpre hX (tracked hpre hX) (J := fun _ _ _ => True)
      (fun g _ => Cross.trueJ_run L g) he nofun
  exact fires_not_nc (asms_noNc _) hf rfl

omit hpre in
/-- **The tensor stores' boxes start aligned.** -/
theorem storeBoxes (hs : StoreFacts P L X) : Safety.StoreBoxes X := by
  rintro ⟨g, k⟩ addr s ⟨pc, he⟩
  obtain ⟨st, hh, -, -, -, -, -, hspec⟩ := hs.spec (Frame.lt_of_get hX he) he
  subst hspec
  simp only [oSpec, oOrigin]
  exact Safety.tile_aligned rfl _ _ _ _

/-- A tensor store's write of a global byte is a byte of O. -/
theorem store_write (hs : StoreFacts P L X) {i : EvId} {x y k : Nat} {a : Acc} {l : Loc}
    (hf : X.AsyncFootprint i (.write (.store x y k)) a) (hc : a.Covers l) :
    Safety.InTensor P P.oBase P.sq l := by
  obtain ⟨s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hf
  have hco := itemCoords hpre
  have hg := Frame.lt_of_get hX hget
  obtain ⟨st, hh, -, -, -, -, hj, hspec⟩ := hs.spec hg hget
  rw [hspec] at hloc
  obtain ⟨hx, hy, hk⟩ := Result.oSpec_slot hloc
  obtain ⟨hb, hhd, -⟩ := Result.tile_lt hpre hco hj
  have hrow := Result.row_lt hpre hco hj st.isLt hy
  rw [Result.oSpec_writeLoc hx hy hk hh.isLt hrow hhd hb] at hloc
  rw [← Rings.covers_one hc hsz, ← Option.some.inj hloc]
  exact element_inTensor hb hhd hrow (by omega) hk

/-- A tensor load's read of a global byte is a byte of Q, K or V. -/
theorem load_read (hr : RingFacts L X) (hcp : RingCopies P L X) (ha : AsyncFacts P L X)
    {i : EvId} {x y k : Nat} {a : Acc} {l : Loc}
    (hf : X.AsyncFootprint i (.read (.load x y k)) a) (hc : a.Covers l) :
    Safety.InTensor P P.qBase P.sq l ∨ Safety.InTensor P P.kBase P.sk l ∨
      Safety.InTensor P P.vBase P.sk l := by
  obtain ⟨sp, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hf
  obtain ⟨g, j⟩ := i
  have hg := Frame.lt_of_get hX hget
  obtain ⟨b, hfull, hm, hsp⟩ := Safety.load_source hX hr hcp ha hget
  have hw := ha.copy_started hg hget hm hfull
  set cnt := ((X.tr g).take j).countP (issuesTo (b.loc L (pairBase L g)))
  subst hsp
  rw [TensorCopy.readLoc_source] at hloc
  obtain ⟨slot, hslot, -⟩ := Option.bind_eq_some_iff.mp hloc
  obtain ⟨rfl, rfl, rfl⟩ := slotAt_val hslot
  obtain ⟨hx, hy, hz⟩ := copy_slot hfull cnt slot
  obtain ⟨hbt, hhd, hrw, hd, hl⟩ := SmemElements.copy_readLoc hpre hfull cnt hw hx hy hz
  rw [TensorCopy.readLoc_source, hloc] at hl
  rw [← Rings.covers_one hc hsz, Option.some.inj hl]
  have hin := element_inTensor (base := SmemElements.inputBase P b) hbt hhd hrw hd hz
  cases b with
  | qFull st => exact .inl hin
  | kvFull s =>
    by_cases hs : s.val % 2 = 0
    · simp only [SmemElements.inputBase, SmemElements.inputRows, hs, ↓reduceIte] at hin ⊢
      exact .inr (.inl hin)
    · simp only [SmemElements.inputBase, SmemElements.inputRows, hs, ↓reduceIte] at hin ⊢
      exact .inr (.inr hin)
  | _ => cases hfull

/-- **Every global write is of O.** -/
theorem globalWrites (hs : StoreFacts P L X) (ho : OlderFacts P L X) (hr : RingFacts L X)
    (htm : TmemFacts L X) : Safety.GlobalWrites P X := by
  intro e a l hI hc hsp
  have hsa : a.loc.space ≠ .shared := fun h => hsp (hc.1.trans h)
  rcases e with ⟨g, k⟩ | ⟨i, p⟩
  · exact absurd (ho.access_shared hI) hsa
  obtain ⟨hw, hf⟩ := hI
  cases p with
  | writeStore x y k => exact store_write hpre hX hs hf hc
  | writeLoad x y k =>
    obtain ⟨pc', a', sp, b, -, -, -, hreg⟩ := hr.write (g := i.1) (k := i.2) ⟨a, true, ⟨hw, hf⟩, hc⟩
    exact absurd hreg.1 hsp
  | writeCta c =>
    obtain ⟨s, tg, ⟨pc, hci⟩, -⟩ := hf
    exact (htm.no_clc hci).elim
  | writeCopy =>
    obtain ⟨s, ⟨pc, hb⟩, -⟩ := hf
    exact (htm.no_bulk hb).elim
  | writeElem j =>
    obtain ⟨s, ⟨pc, hb⟩, -⟩ := hf
    exact (htm.no_bulk hb).elim
  | writePrefetch x y k => exact hf.elim
  | _ => simp [Part.writes] at hw

/-- **Every touched global byte is in a tensor.** -/
theorem globalPlaced (hs : StoreFacts P L X) (ho : OlderFacts P L X) (hr : RingFacts L X)
    (hcp : RingCopies P L X) (ha : AsyncFacts P L X) (htm : TmemFacts L X) (hsc : ScoreFacts L X)
    (hout : OutputFacts L X) : Safety.GlobalPlaced P X := by
  intro e a l ht hc hsp
  have hsa : a.loc.space ≠ .shared := fun h => hsp (hc.1.trans h)
  rcases ht with ⟨w, hI⟩ | ⟨i, bs, rfl, hnc⟩
  swap
  · exact (no_nc hpre hX hnc).elim
  rcases e with ⟨g, k⟩ | ⟨i, p⟩
  · exact absurd (ho.access_shared hI) hsa
  obtain ⟨hw, hf⟩ := hI
  cases p with
  | writeStore x y k => exact .inr (.inr (.inr (store_write hpre hX hs hf hc)))
  | writeLoad x y k =>
    obtain ⟨pc', a', sp, b, -, -, -, hreg⟩ := hr.write (g := i.1) (k := i.2) ⟨a, w, ⟨hw, hf⟩, hc⟩
    exact absurd hreg.1 hsp
  | writeCta c =>
    obtain ⟨s, tg, ⟨pc, hci⟩, -⟩ := hf
    exact (htm.no_clc hci).elim
  | writeCopy =>
    obtain ⟨s, ⟨pc, hb⟩, -⟩ := hf
    exact (htm.no_bulk hb).elim
  | writeElem j =>
    obtain ⟨s, ⟨pc, hb⟩, -⟩ := hf
    exact (htm.no_bulk hb).elim
  | readLoad x y k =>
    rcases load_read hpre hX hr hcp ha hf hc with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  | readStore x y k =>
    obtain ⟨s, addr, ⟨pc, hget⟩, hloc, -⟩ := hf
    obtain ⟨-, st, -, hsrc⟩ := hout.store_tma (Frame.lt_of_get hX hget) hget
    exact absurd (hsrc.2.1 x y k a.loc hloc).1 hsa
  | readPrefetch x y k =>
    obtain ⟨s, addr, ⟨pc, hget⟩, -⟩ := hf
    exact (ha.no_prefetch hget).elim
  | readCopy =>
    rcases hf with ⟨s, ⟨pc, hb⟩, -⟩ | ⟨pc, hpf⟩
    · exact (htm.no_bulk hb).elim
    · exact (htm.no_prefetch hpf).elim
  | oldElem j =>
    obtain ⟨s, r, ⟨pc, hb⟩, -⟩ := hf
    exact (htm.no_bulk hb).elim
  | oldStore x y k =>
    obtain ⟨s, addr, ⟨pc, hget⟩, hred, -⟩ := hf
    obtain ⟨-, st, -, hsrc⟩ := hout.store_tma (Frame.lt_of_get hX hget) hget
    rw [hsrc.1] at hred
    cases hred
  | mmaRead isB idx =>
    obtain ⟨-, ⟨d, s, acc, mask, -, hbl⟩ | ⟨c, -, -, ⟨pc, hci⟩, -⟩⟩ := hf
    · exact absurd (TcMma.OperandSpec.byteLoc_shared hbl) hsa
    · exact (hsc.no_cp _ _ ⟨pc, hci⟩).elim
  | _ => exact hf.elim

/-- **Every touched shared byte is in a region of a launched CTA.** -/
theorem sharedPlaced (ho : OlderFacts P L X) (hr : RingFacts L X) (ha : AsyncFacts P L X)
    (htm : TmemFacts L X) (hout : OutputFacts L X) (hmma : MmaReadsRings L X) :
    Safety.SharedPlaced L X := by
  have ht := tracked hpre hX
  have hgr := hpre.grid
  intro e a l hT hc hs
  rcases hT with ⟨w, hI⟩ | ⟨i, bs, rfl, hnc⟩
  swap
  · exact (no_nc hpre hX hnc).elim
  rcases Execution.shared_intent hI hc hs with ⟨⟨g, k⟩, rfl, hA⟩ | ⟨i, isB, idx, rfl⟩ |
    ⟨i, x, y, k, rfl⟩ | ⟨i, x, y, k, rfl⟩ | ⟨i, c, s, tg, -, ⟨pc, hci⟩, -⟩ |
    ⟨i, q, s, -, ⟨pc, hb⟩⟩ | ⟨i, -, ⟨pc, hpf⟩⟩
  · have hg := access_lt hX hA
    have hown := ha.access_own hA (ho.access_shared hA)
    refine ⟨by rw [hc.2.1, hown]; exact cta_lt hg, ?_⟩
    have h13 := Cross.access_warp13 hpre hX ht hA
    by_cases h8 : warpOf L g < 8
    · obtain ⟨h1, h2⟩ := Cross.soft_access_range hpre hX ht h8 hA hc
      exact .inr (.inl ⟨hs, h1, h2⟩)
    by_cases h12 : warpOf L g < 12
    · rcases Cross.corr_access_range hpre hX ht (by omega) h12 hA hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inr (.inl ⟨hs, h1, h2⟩)
      · exact .inr (.inr (.inl ⟨hs, h1, h2⟩))
    · obtain ⟨hloc, hsz⟩ := mma_access hpre hX ht (by omega) hA
      obtain ⟨-, -, h1, h2⟩ := hc
      rw [hloc] at h1 h2
      rw [hsz] at h2
      simp only [Mma.baseAt] at h1 h2
      exact .inl ⟨hs, by omega, by omega⟩
  · obtain ⟨c, b, hb, hreg⟩ := hmma i isB idx l ⟨a, w, hI, hc⟩ hs
    obtain ⟨-, -, hcta, -⟩ := hr.read (g := i.1) (k := i.2) ⟨a, w, hI, hc⟩ hb hreg
    obtain ⟨-, ⟨d, s, acc, mask, ⟨pc, hget⟩, -⟩ | ⟨c, k, cta, ⟨pc, hci⟩, -⟩⟩ := hI.2
    · have hg := cta_lt (Frame.lt_of_get hX hget)
      refine ⟨by rw [hreg.2.1]; omega, .inr (.inr (.inr (region_rings hb hreg)))⟩
    · have hg := cta_lt (Frame.lt_of_get hX hci)
      refine ⟨by rw [hreg.2.1]; omega, .inr (.inr (.inr (region_rings hb hreg)))⟩
  · obtain ⟨-, sp, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hI
    have hg := Frame.lt_of_get hX hget
    obtain ⟨-, st, hst, hsrc⟩ := hout.store_tma hg hget
    have hl := hsrc.2.1 x y k a.loc hloc
    rw [Rings.covers_one hc hsz] at hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    exact ⟨by rw [h2]; exact cta_lt hg, .inr (.inr (.inl ⟨h1, by omega, by omega⟩))⟩
  · obtain ⟨pc, a', sp, b, hget, hb, -, hreg⟩ := hr.write (g := i.1) (k := i.2) ⟨a, w, hI, hc⟩
    exact ⟨by rw [hreg.2.1]; exact cta_lt (Frame.lt_of_get hX hget),
      .inr (.inr (.inr (region_rings hb hreg)))⟩
  · exact (htm.no_clc hci).elim
  · exact (htm.no_bulk hb).elim
  · exact (htm.no_prefetch hpf).elim

end

end Placed

end
end PTX.Kernels.FlashAttn4Fwd.Proof
