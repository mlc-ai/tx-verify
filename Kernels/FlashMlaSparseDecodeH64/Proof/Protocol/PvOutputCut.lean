-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvCausalCut
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RescaleTmemReadSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputPayload
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescaleGainTrace

@[expose] public section

/-! # The PV completions available at a softmax output load wait -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvOutputCut

open PTX PTX.Flow AsyncCopy GemmRing OutputTmemReadSource
open PvAccumulatorSource (Issue)
open MachineTracking (Dismisses)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g cut issuer limit : Nat}

/-- An observed commit covers every PV issue through the selected output block. -/
structure Cut (P : Params) (L : Launch) (X : Execution) (g cut issuer limit : Nat) : Prop where
  probabilities : PvCausalCut.Cut P L X g cut limit
  cta : ctaOf L issuer = ctaOf L g
  completes : ∀ {i : Nat} {d : Wg1Mma.D} {k : Fin 8},
    Issue L X issuer i d.i k →
    Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma d)) →
    d.site = .pvMma k → d.i ≤ limit →
    X.async.mmaDone (issuer, i) = true ∧
      ∀ {j e}, cut ≤ j → X.get (g, j) = some e → TcMma.DoneBefore L X (issuer, i) (g, j)

private theorem cut_of_observation {w c tag ct parity : Nat} {m : Loc}
    {sp : TcCommit.Spec} {rank : Fin 16} {scope : MbarScope}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hProb : PvCausalCut.Cut P L X g cut limit) (hCta : ctaOf L issuer = ctaOf L g)
    (hw : X.get (g, w) = some ⟨tag, .wait m parity true true scope⟩)
    (hBefore : w < cut) (hc : X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩)
    (hTarget : TcCommit.target sp rank = some m)
    (hObs : Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w))
    (hOrder : ∀ {i : Nat} {d : Wg1Mma.D} {k : Fin 8}, Issue L X issuer i d.i k →
      Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma d)) →
      d.site = .pvMma k → d.i ≤ limit → i < c) :
    Cut P L X g cut issuer limit := by
  refine ⟨hProb, hCta, ?_⟩
  intro i d k hi hd hsite hLe
  have hLt := hOrder hi hd hsite hLe
  have ht : TracksMma X (issuer, i) (issuer, c) :=
    ⟨rfl, hLt, .inl ⟨_, _, _, _, hi⟩, sp, ct, hc⟩
  have hDone := (hX.tcCommit _ _ (hObs.waitObserves_tcNotify hw).1).2 _ ht
  refine ⟨hDone, fun hAfter he => ?_⟩
  exact done_before_event_of_observed hX hi hLt hc hTarget hw hObs hCta
    (hBefore.trans_le hAfter) he

variable {tag : Nat} {d : Wg0.D} {tile : Fin 4} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hmma : MmaIssuer P L X (ctaOf L g) issuer)
include hpre hX hs hmma

/-- A rescale wait has already seen the QK commit which completes all prior PV blocks. -/
theorem of_rescale_wait (hd : Frame.stateAt (Machine.code P L) X g cut = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) (hw : X.get (g, cut) = some ⟨tag, .tc .waitLd⟩)
    (hPrior : ∀ w, baseCausality L X w (g, cut) → ¬ Dismisses P L X w) :
    Cut P L X g cut issuer (d.block - 1) := by
  have hg := Frame.lt_of_get hX hw
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hw hd
  have hInv : Wg0.Inv P L g d := hInv
  have hPos := Wg0RescaleGainTrace.rescale_block_pos (PTX.len_of_get hw).le hd
    (by rw [hsite]; rfl)
  have hCount := Wg0BarrierCount.count_at_wg0 hpre hX (hs g hg).machine hw hd
  simp only [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, hsite] at hCount
  have hProb : PvCausalCut.Cut P L X g cut (d.block - 1) :=
    ⟨⟨_, hw⟩, by have := hInv.blockLt; omega, by omega, hPrior⟩
  obtain ⟨w, wt, parity, c, ct, scope, sp, rank, d', hLt, hWait, hc, hTarget, hState,
    hCta, hBlock, hObs⟩ :=
    RescaleTmemReadSource.actual_earlier_qk_in_rescale hpre hX hs hmma hd
      (by rw [hsite]; rfl) hw
  refine cut_of_observation hX hProb hCta hWait hLt hc hTarget hObs ?_
  intro i q k hi hq hSite hLe
  by_contra! hNot
  have hEq := Wg1Mma.block_order hNot hState hq
  omega

/-- An epilogue load wait has already seen the last PV commit. -/
theorem of_output_wait (hd : Frame.stateAt (Machine.code P L) X g cut = some (some (.wg0 d)))
    (hsite : d.site = .oWait tile) (hw : X.get (g, cut) = some ⟨tag, .tc .waitLd⟩)
    (hPrior : ∀ w, baseCausality L X w (g, cut) → ¬ Dismisses P L X w) :
    Cut P L X g cut issuer d.block := by
  have hg := Frame.lt_of_get hX hw
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hw hd
  have hInv : Wg0.Inv P L g d := hInv
  have hCount := Wg0BarrierCount.count_at_wg0 hpre hX (hs g hg).machine hw hd
  simp only [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, hsite] at hCount
  have hProb : PvCausalCut.Cut P L X g cut d.block :=
    ⟨⟨_, hw⟩, hInv.blockLt, by omega, hPrior⟩
  obtain ⟨ld, hLd, q, e, words, hq, hqSite, he, _, _, hFields⟩ :=
    Wg0OutputPayload.at_wait hpre hX hg (hs g hg).machine hd hsite
  obtain ⟨_, _, _, _, hQInv, _, _⟩ := Frame.fired_site hs hX he hq
  have hQInv : Wg0.Inv P L g q := hQInv
  obtain ⟨w, hWlt, wt, scope, hWait, old, hOld, hOldSite, hOldBlock⟩ :=
    Wg0OutputVisits.pvWaitBeforeLoad_state hpre hX hg (hs g hg).machine hQInv hq hqSite
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre rfl hInv.wg
  have hOld' : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L (ctaOf L g) lane) w =
      some (some (.wg0 old)) := by rwa [← hLane]
  let m := GemmRing.empty L (ctaOf L g) (rawSlot old.block)
  have hWait' : X.get (GemmRing.softmax L (ctaOf L g) lane, w) =
      some ⟨wt, .wait m (old.block / 2 % 2) true true scope⟩ := by
    rw [← hLane, show m =
      ⟨.shared, ctaOf L g, L.sharedBase + Wg0.svDoneOff (old.block % 2)⟩ from rfl, hOldBlock]
    exact hWait
  obtain ⟨c, ct, sp, rank, final, hc, hTarget, hCta, hFinal, hSite, hBlock, hObs⟩ :=
    OutputReuseAudit.actual_final_pv_observed hpre hX hs hmma hOld' hOldSite rfl hWait'
  rw [← hLane] at hWait' hObs
  have hFinalBlock : final.i = d.block := hBlock.trans (hOldBlock.trans
    (show q.block = d.block from (congrArg Wg0.D.block hFields).symm))
  refine cut_of_observation hX hProb hCta hWait' (hWlt.trans hLd) hc hTarget hObs ?_
  intro i p k hi hp hpSite hpLe
  have hIssuer := Frame.lt_of_get hX hc
  have hSlot : final.i % 2 = (rawSlot old.block).val := by rw [hBlock]; rfl
  obtain ⟨hMbar, _, _⟩ := GemmRing.actual_notification hpre hX hs hc rfl hTarget
  rw [← hCta] at hMbar
  exact StageAfterPv.issue_before_final_commit hpre hX (hs issuer hIssuer) hp
    (.inr ⟨k, hpSite⟩) (hFinalBlock.symm ▸ hpLe) hc hFinal hSite hSlot hMbar

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvOutputCut
