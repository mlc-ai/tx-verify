-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputTrace
import Lemmas.Tensor.TensorCompleteConsistentRead

public section

/-! # The kernel's non-coherent loads have no overlapping write intent -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX AsyncCopy PTX.Flow Wg0 Result

/-- Pending and performed global writes have the same output bounds. -/
theorem global_write_intent_range {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {w : Ref} {a : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hWrite : X.Intent w a true) (hCover : a.Covers l) (hGlobal : l.space = .global) :
    (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P) ∨
      (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P) := by
  have hSpace : a.loc.space = .global := hCover.1.symm.trans hGlobal
  cases w with
  | thread i =>
    change X.Access i a true at hWrite
    rcases hWrite with ⟨_, _, h⟩ | ⟨bs, hw, _⟩ | ⟨_, _, hr⟩
    · cases h
    · exact global_write_range hpre hs hX ht (bs := bs) (w := .thread i) (.inl hw) hCover hGlobal
    · exact (GlobalWrites.no_rmw hX hr).elim
  | async i p =>
    obtain ⟨hKind, hFoot⟩ := hWrite
    cases p <;> try contradiction
    case writeCopy =>
      obtain ⟨_, h, _⟩ := hFoot
      exact (GlobalWrites.no_copy hX h).elim
    case writeElem =>
      obtain ⟨_, h, _⟩ := hFoot
      exact (GlobalWrites.no_copy hX h).elim
    case writeCta =>
      obtain ⟨_, _, h, _⟩ := hFoot
      exact (GlobalWrites.no_clc hX h).elim
    case writeLoad x y k =>
      obtain ⟨_, _, hIssue, hLoc, _⟩ := hFoot
      have h := (TensorSharedBounds.write_loc_windows hpre hX hs ht hIssue hLoc).1
      cases h.symm.trans hSpace
    case writeStore x y k =>
      obtain ⟨s, addr, hIssue, hLoc, hSize⟩ := hFoot
      obtain ⟨tag, he⟩ := hIssue
      have hg := Frame.lt_of_get hX he
      obtain ⟨d, j, hd, hj⟩ := GlobalWrites.outputTile_site hs hX ht ⟨tag, he⟩
      have hw := Wg0OutputControl.outputWarp hX (hs _ hg).machine he hd hj
      obtain ⟨_, hSpec⟩ :=
        Wg0OutputTrace.tileSpec hpre hX (hs _ hg).machine ⟨tag, he⟩ hd hj
      rw [hSpec, TensorStore.writeLoc] at hLoc
      cases hSlot : TensorTransfer.slotAt (outputSpec P L i.1 j).descriptor x y k with
      | none => simp [hSlot] at hLoc
      | some slot =>
        have ⟨hXc, hYc, hBc⟩ := TensorCopy.slotAt_coordinates hSlot
        obtain ⟨hx, hy, hk⟩ := outputShape P L i.1 j
        have hx' : slot.1.val < 64 := hx ▸ slot.1.isLt
        have hy' : slot.2.1.val < 64 := hy ▸ slot.2.1.isLt
        have hk' : slot.2.2.val < 2 := hk ▸ slot.2.2.isLt
        let out : OutputSlot := (⟨slot.1.val, hx'⟩, ⟨slot.2.1.val, hy'⟩, ⟨slot.2.2.val, hk'⟩)
        have hout : tensorOutputSlot P L i.1 j out = slot := by
          rcases slot with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
          rfl
        have hb := Wg1Mma.eOf_lt_b hpre (g := i.1)
        have hq := Wg1Mma.queryOf_lt hpre hg
        rw [hSlot, Option.bind_some, ← hout, outputSlot_destination P L i.1 j out hw hq hb] at hLoc
        change a.loc.InRange a.size l at hCover
        rw [hSize, ← Option.some.inj hLoc] at hCover
        exact .inl (outputRange hb hq hy' (outputColumn_lt j hw hx') hk' hCover)

private theorem no_input_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {a fp : Acc} {l : Loc} {w : Ref} {base width : Nat}
    (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hRead : FitsInput a base width) (hCover : a.Covers l)
    (hWrite : X.Intent w fp true) (hwc : fp.Covers l)
    (hOut : Apart width (tensorBytes P) base P.outBase)
    (hLse : Apart width (lseBytes P) base P.lseBase) : False := by
  obtain ⟨hGlobal, hLo, hHi⟩ := hRead
  obtain ⟨hSpace, _, hFootLo, hFootHi⟩ := hCover
  have hlo : base ≤ l.addr := by omega
  have hhi : l.addr < base + width := by omega
  rcases global_write_intent_range hpre hs hX ht hWrite hwc (hSpace.trans hGlobal) with hw | hw
  · unfold Apart at hOut
    rcases hOut with h | h <;> omega
  · unfold Apart at hLse
    rcases hLse with h | h <;> omega

/-- No selected non-coherent read conflicts with an issued write, including pending TMA stores. -/
theorem ncReadOnly_safe {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ Assumptions.ncReadOnly.ub L mem0 X := by
  rintro ⟨⟨g, i⟩, tag, a, bs, w, fp, l, he, hNc, hCover, hWrite, hwc⟩
  have hInput := NcInputTrace.footprint hpre hX hs ht he hNc rfl
  have exclude {base width : Nat} (hFits : FitsInput a base width) :=
    no_input_write hpre hs hX ht hFits hCover hWrite hwc
  cases hInput with
  | mainLength hPtr hFits =>
    exact exclude hFits (hpre.topkLenApartO _ hPtr) (hpre.topkLenApartLse _ hPtr)
  | extraLength hPtr hFits =>
    exact exclude hFits (hpre.extraTopkLenApartO _ hPtr) (hpre.extraTopkLenApartLse _ hPtr)
  | sink hPtr hFits => exact exclude hFits (hpre.sinkApartO _ hPtr) (hpre.sinkApartLse _ hPtr)
  | mainIndices hFits => exact exclude hFits hpre.idxApartO hpre.idxApartLse
  | extraIndices hPos hFits =>
    exact exclude hFits (hpre.extraIdxApartO hPos) (hpre.extraIdxApartLse hPos)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
