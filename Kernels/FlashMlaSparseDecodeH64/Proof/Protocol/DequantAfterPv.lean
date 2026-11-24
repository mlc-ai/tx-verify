-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmCompletion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing
import Lemmas.Order.OrderBaseCausality

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # The PV completion before dequantized-buffer reuse -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantAfterPv

open PTX PTX.Flow PTX.MbarRing AsyncCopy GemmRing

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {cta issuer j : Nat} {lane : Fin 128} {new : Wg2.D} {e : Event}

set_option maxRecDepth 4096 in
/-- A dequantizer writing a reused slot has acquired the actual previous PV commit for it. -/
theorem prior_commit_of_store (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (he : X.get (producer L cta lane, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X (producer L cta lane) j =
      some (some (.wg2 new)))
    (hsite : ∃ r s, new.site = .store r s) (hu : 0 < new.block / 2) :
    let g := producer L cta lane
    let m := empty L cta (rawSlot new.block)
    ∃ (w wt parity c ct : Nat) (sp : TcCommit.Spec) (rank : Fin 16) (d : Wg1Mma.D),
      w < j ∧ X.get (g, w) = some ⟨wt, .wait m parity true true .cta⟩ ∧
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧ sp.mbar = m ∧
      TcCommit.target sp rank = some m ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      ctaOf L issuer = cta ∧ d.site = .pvCommit ∧ d.i + 2 = new.block ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w) ∧
      baseCausality L X (g, w) (g, j) := by
  dsimp only
  let g := producer L cta lane
  let slot := rawSlot new.block
  let m := empty L cta slot
  let u := new.block / 2
  have hg := Frame.lt_of_get hX he
  have hCta : ctaOf L g = cta := by
    have hl := lane.isLt
    simp only [g, RawRing.consumer, ctaOf, hpre.block]
    omega
  obtain ⟨_, hWCount⟩ := Wg2GemmTrace.composed_write_counts hpre
    ((hs g hg).produces (hX.thr g hg)) hd hsite
  change okPolls (empty L (ctaOf L g) slot) ((X.tr g).take j) = u + 1 at hWCount
  rw [hCta] at hWCount
  obtain ⟨w, wt, parity, acq, sc, hwj, hw, hCount⟩ := Poll.exists_nth hWCount.ge
  obtain ⟨rfl, rfl⟩ := RingSourceSites.actual_wait_acquire hX hw rfl
  have hW : Poll.nth X m g u = w := by rw [← hCount]; exact Poll.nth_eq hw
  let R := dequantRing (slot := slot) hpre hX hs hmma
  have hPresent : X.RefPresent (.thread (R.wE lane (u - 1 + 1))) := by
    change X.RefPresent (.thread (g, Poll.nth X m g (u - 1 + 1)))
    rw [show u - 1 + 1 = u by dsimp [u]; omega, hW]
    exact ⟨_, hw⟩
  obtain ⟨hMember, hWitness⟩ := R.observes_empty hX.depAcyclic hPresent 0
  change (0, u - 1) ∈ Notify.S X m issuer m at hMember
  let c := Notify.cm X issuer m (u - 1)
  let rank := Notify.rank X m issuer m (u - 1)
  change Witness L X (.async (issuer, c) (.tcNotify rank))
    (g, Poll.nth X m g (u - 1 + 1)) at hWitness
  rw [show u - 1 + 1 = u by dsimp [u]; omega, hW] at hWitness
  obtain ⟨_, ct, sp, hc, hMbar, hTarget, hCCount⟩ :=
    (reuse_obj hpre hX hs hmma (slot := slot)).S_rec hMember
  have hIL := Frame.lt_of_get hX hc
  obtain ⟨_, hICta, d, hSlot, hIShape, hD⟩ :=
    actual_notification hpre hX (fun _ hg => Machine.code_sound hpre hg) hc rfl hTarget
  have hPv : d.site = .pvCommit := by
    rcases hIShape with ⟨h, _⟩ | ⟨_, h⟩
    · cases h
    · exact h
  have hPrev := Wg1MmaGemmTrace.composed_count_here hpre hIL .pv
    ((hs issuer hIL).produces (hX.thr issuer hIL)) hD hSlot
  simp only [Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hPrev
  change ((X.tr issuer).take c).countP (commitsTo (empty L (ctaOf L issuer) slot)) =
    d.i / 2 at hPrev
  rw [hICta] at hPrev
  change ((X.tr issuer).take c).countP (commitsTo m) = u - 1 at hCCount
  have hBlock : d.i + 2 = new.block := by
    change d.i % 2 = new.block % 2 at hSlot
    have hUse : d.i / 2 = new.block / 2 - 1 := hPrev.symm.trans hCCount
    omega
  have hOrder : baseCausality L X (g, w) (g, j) :=
    .single (.inl (po_of_source_not_access rfl hwj (PTX.len_of_get he) (by rw [hw]; rfl)))
  exact ⟨w, wt, parity, c, ct, sp, rank, d, hwj, hw, hc, hMbar, hTarget, hD, hICta, hPv,
    hBlock, hWitness, hOrder⟩

/-- Any earlier QK or PV issue of the same slot is covered by the completion acquired before the
current dequantization store. This also covers issues from generations preceding the observed
commit's generation. -/
theorem earlier_operand_completed {g i index : Nat} {old : Wg1Mma.D} {isB : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hCta : ctaOf L g = cta) (hOp : X.TcAsync (g, i))
    (hOld : Frame.stateAt (Machine.code P L) X g i = some (some (.mma old)))
    (hOldSite : (∃ k, old.site = .qkMma k) ∨ (∃ k, old.site = .pvMma k))
    (hBefore : old.i < new.block) (hSameSlot : old.i % 2 = new.block % 2)
    (he : X.get (producer L cta lane, j) = some e)
    (hNew : Frame.stateAt (Machine.code P L) X (producer L cta lane) j =
      some (some (.wg2 new)))
    (hStore : ∃ r s, new.site = .store r s) :
    let w := producer L cta lane
    X.AsyncPresent (g, i) .mmaDone ∧
      ∃ acquire < j, AsyncFinished L X (g, i) (.mmaRead isB index) (w, acquire) ∧
        baseCausality L X (w, acquire) (w, j) := by
  have hNotElect : old.site ≠ .elect := by
    rcases hOldSite with ⟨k, h⟩ | ⟨k, h⟩ <;> simp [h]
  have hg := hmma g i old hCta hOld hNotElect
  subst g
  have hu : 0 < new.block / 2 := by omega
  obtain ⟨w, tag, parity, c, ct, sp, rank, d, hwj, hw, hc, hMbar, hTarget, hState, hICta, hPv,
    hBlock, hWitness, hBase⟩ := prior_commit_of_store hpre hX hs hmma he hNew hStore hu
  let producerThread := producer L cta lane
  let slot := rawSlot new.block
  let m := empty L cta slot
  have hIL := Frame.lt_of_get hX hc
  have hTrace := (hs issuer hIL).produces (hX.thr issuer hIL)
  have hOldCount := Wg1MmaGemmTrace.composed_count_here hpre hIL .pv
    hTrace hOld (show old.i % 2 = slot.val from hSameSlot)
  have hOldOpen : Wg1MmaGemmTrace.completed .pv old.site = false := by
    rcases hOldSite with ⟨k, h⟩ | ⟨k, h⟩ <;> rw [h] <;> rfl
  simp only [hOldOpen, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hOldCount
  change ((X.tr issuer).take i).countP (commitsTo (empty L (ctaOf L issuer) slot)) =
    old.i / 2 at hOldCount
  rw [hICta] at hOldCount
  have hCommitSlot : d.i % 2 = slot.val := by
    change d.i % 2 = new.block % 2
    omega
  have hCommitCount := Wg1MmaGemmTrace.composed_count_here hpre hIL .pv hTrace hState hCommitSlot
  simp only [Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    at hCommitCount
  change ((X.tr issuer).take c).countP (commitsTo (empty L (ctaOf L issuer) slot)) =
    d.i / 2 at hCommitCount
  rw [hICta] at hCommitCount
  have hOrder : i < c := by
    by_contra! hge
    have hne : c ≠ i := by
      intro heq
      subst c
      rw [hState] at hOld
      have hEq := Machine.ThreadD.mma.inj (Option.some.inj (Option.some.inj hOld))
      rw [← hEq, hPv] at hOldSite
      rcases hOldSite with ⟨k, h⟩ | ⟨k, h⟩ <;> cases h
    have hMono := countP_take_mono (commitsTo m) (X.tr issuer) (show c + 1 ≤ i by omega)
    have hTick : commitsTo m ⟨ct, .tc (.commit sp)⟩ = true :=
      by simp [commitsTo, m, slot, hMbar]
    have hInc := countP_take_succ hc hTick
    rw [hInc, hCommitCount, hOldCount] at hMono
    omega
  have hTracks : TracksMma X (issuer, i) (issuer, c) :=
    ⟨rfl, hOrder, hOp, sp, ⟨ct, hc⟩⟩
  have hProducer := Frame.lt_of_get hX he
  have hProducerCta : ctaOf L producerThread = cta := by
    have hLane := lane.isLt
    simp only [producerThread, RawRing.consumer, ctaOf, hpre.block]
    omega
  have hSame : ctaOf L issuer = ctaOf L producerThread := hICta.trans hProducerCta.symm
  have hScope : ScopesMeet L .cluster issuer .cta producerThread :=
    ⟨⟨hIL, hProducer, congrArg L.clusterOfCta hSame⟩, hProducer, hIL, hSame.symm⟩
  obtain ⟨hDone, hFinished⟩ := completed_read hX ⟨ct, hc⟩ hTarget hTracks hScope hw hWitness
  exact ⟨hDone, w, hwj, hFinished, hBase⟩

/-- The completion-and-acquire path applies to an actual earlier B-operand read at any byte. -/
theorem earlier_b_read_completed {g i index : Nat} {old : Wg1Mma.D} {l : Loc} {b : Option Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hCta : ctaOf L g = cta) (hRead : X.MmaRead (g, i) true index l b)
    (hOld : Frame.stateAt (Machine.code P L) X g i = some (some (.mma old)))
    (hOldSite : (∃ k, old.site = .qkMma k) ∨ (∃ k, old.site = .pvMma k))
    (hBefore : old.i < new.block) (hSameSlot : old.i % 2 = new.block % 2)
    (he : X.get (producer L cta lane, j) = some e)
    (hNew : Frame.stateAt (Machine.code P L) X (producer L cta lane) j =
      some (some (.wg2 new)))
    (hStore : ∃ r s, new.site = .store r s) :
    let w := producer L cta lane
    X.AsyncPresent (g, i) .mmaDone ∧
      ∃ acquire < j, AsyncFinished L X (g, i) (.mmaRead true index) (w, acquire) ∧
        baseCausality L X (w, acquire) (w, j) := by
  have hOp : X.TcAsync (g, i) := by
    rcases hRead.1 with ⟨d, s, a, m, hIssue, _⟩ | ⟨_, _, _, _, h⟩
    · exact .inl ⟨d, s, a, m, hIssue⟩
    · cases h.1
  exact earlier_operand_completed hpre hX hs hmma hCta hOp hOld hOldSite hBefore hSameSlot
    he hNew hStore

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantAfterPv
