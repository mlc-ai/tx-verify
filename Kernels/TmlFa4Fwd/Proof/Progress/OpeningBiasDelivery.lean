-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstQueryReadyPhase
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReady
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasNotificationFaults
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningBiasReady
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondBiasBoxes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier Prologue
open Thread.Loader (biasReadyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
include hp hMax hFrame

/-- The first Bias expectation is issued and both halves of the selected tile notify
their physical stage-zero object. -/
theorem selectedOpeningBiasDeliveredOfMaximal (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    (∃ credit, X.Arrive credit (biasReadyObject l (g/l.block) 0) 32768 1 true .cta) ∧
      let coords := Epilogue.assignedCoordinates p batch (g/l.block)
      ∀ half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
        X.TensorIssue issue p.biasMapAddress
          (biasInputSpec p (1152+64*half.val) (p.qOffset batch+256*coords.1) coords.2
            ⟨.shared,g/l.block,l.sharedBase+(166912+16384*half.val)⟩
            (biasReadyObject l (g/l.block) 0) false) ∧
          (X.tensor issue).any (fun o => o.effects.notified) = true := by
  obtain ⟨_, _, _, _, _, hCredit, hBoxes⟩ :=
    selectedOpeningBiasPacketOfMaximal hp hMax hFrame hg hw hb hLo hHi
  refine ⟨hCredit, fun half => ?_⟩
  obtain ⟨issue, hOwner, hIssue⟩ := hBoxes half
  refine ⟨issue, hOwner, hIssue, ?_⟩
  cases hNotify : (X.tensor issue).any (fun o => o.effects.notified) with
  | true => rfl
  | false =>
    exact (hMax.not_grows
      (Protocol.LoaderReady.pendingTensorInput hp hMax.1 hFrame hIssue hNotify)).elim

omit hp hMax hFrame in
private theorem biasPhaseOfDelivered {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {credit : EvId}
    (hCredit : X.Arrive credit (biasReadyObject l cta stage) 32768 1 true .cta)
    (hBoxes : ∀ half : Fin 2, ∃ issue box, X.TensorIssue issue p.biasMapAddress box ∧
      box.sharedBase.addr = 166912+32768*stage.val+16384*half.val+l.sharedBase ∧
      box.mbar = biasReadyObject l cta stage ∧
      (X.tensor issue).any (fun o => o.effects.notified) = true) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  let loc := biasReadyObject l cta stage
  have hNote (half : Fin 2) : ∃ issue box, X.TensorIssue issue p.biasMapAddress box ∧
      box.sharedBase.addr = 166912+32768*stage.val+16384*half.val+l.sharedBase ∧
      ∃ r ∈ X.objects loc, r.id = .async issue (.notify .load) ∧
        r.action = .completeTx 16384 := by
    obtain ⟨issue, box, hIssue, hDst, hMbar, hDone⟩ := hBoxes half
    have hBytes := actualTensorInputTxBytes hp hMax.1 hIssue
    obtain ⟨site, hEvent⟩ := hIssue
    cases hObservation : X.tensor issue with
    | none => simp [hObservation] at hDone
    | some o =>
      have hNotified : o.effects.notified = true := by simpa [hObservation] using hDone
      have hAction : objectAction X X.async loc (.async issue (.notify .load)) =
          some (.completeTx 16384) := by
        simp [objectAction, hEvent, hObservation, hMbar, hNotified, hBytes, bind, Option.bind, loc]
      obtain ⟨r, hr, hId⟩ := (hMax.1.tma.2.2.1 loc).2.2 _ _ hAction
      have ha := ((hMax.1.tma.2.2.1 loc).2.1 r hr).1
      rw [hId,hAction] at ha
      exact ⟨issue, box, ⟨site,hEvent⟩, hDst, r, hr, hId, (Option.some.inj ha).symm⟩
  obtain ⟨left, lBox, hLeft, hLDst, r, hr, hId, ha⟩ := hNote 0
  obtain ⟨right, rBox, hRight, hRDst, t, ht, hId', ha'⟩ := hNote 1
  have hNe : r ≠ t := by
    intro hEq
    have hSame := hId.symm.trans ((congrArg Record.id hEq).trans hId')
    have hI := (Ref.async.inj hSame).1
    subst right
    obtain ⟨_, he⟩ := hLeft
    obtain ⟨_, hf⟩ := hRight
    have hEq := Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hf)))
    have hAddr := congrArg (fun s : TensorCopy.Spec => s.sharedBase.addr) hEq.2
    rw [hLDst,hRDst] at hAddr
    change 166912+32768*stage.val+16384*0+l.sharedBase =
      166912+32768*stage.val+16384*1+l.sharedBase at hAddr
    omega
  obtain ⟨_, he⟩ := hCredit
  have hAction : objectAction X X.async loc (.thread credit) = some (.arrive 1 32768) := by
    simp [objectAction, he, loc]
  obtain ⟨expected, hExpected, hIdExpected⟩ := (hMax.1.tma.2.2.1 loc).2.2 _ _ hAction
  have hA := ((hMax.1.tma.2.2.1 loc).2.1 expected hExpected).1
  rw [hIdExpected, hAction] at hA
  exact Protocol.Bias.biasReadyAdvancedOfCredits hp hMax.1 stage hExpected
    (Option.some.inj hA).symm hr ht hNe ha ha'

/-- Every active CTA completes its first Bias-ready phase. The physical phase may advance
further as softmax consumes later tiles. -/
theorem selectedOpeningBiasPhaseOfMaximal (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    let log := X.objects (biasReadyObject l (g/l.block) 0)
    ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  obtain ⟨⟨credit,hCredit⟩,hBoxes⟩ :=
    selectedOpeningBiasDeliveredOfMaximal hp hMax hFrame hg hw hb hLo hHi
  apply biasPhaseOfDelivered hp hMax 0 hCredit
  intro half
  obtain ⟨issue,_,hIssue,hDone⟩ := hBoxes half
  exact ⟨issue,_,hIssue,by change l.sharedBase + (166912+16384*half.val) = _; omega,rfl,hDone⟩

/-- The first Bias tile remains ready for each pending lane of its stage-zero group. -/
theorem openingBiasPhaseForPendingLane (hg : g < l.threads) (hw : warpIndex l g < 4)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hMissing : PTX.Flow.okPolls (biasReadyObject l (g/l.block) 0) (X.tr g) = 0) :
    let log := X.objects (biasReadyObject l (g/l.block) 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  let loader := g/l.block*l.block+448
  have hLane : 448 < l.block := by rw [hp.block]; decide
  have hl : loader < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
  obtain ⟨hLoaderCta, hLoaderLane⟩ := NamedBar.lane_cta (c := g/l.block)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  have hLoaderWarp : warpIndex l loader = 14 := by
    unfold warpIndex loader
    rw [hLoaderLane]
  obtain ⟨s,hs,hLower⟩ := selectedOpeningBiasPhaseOfMaximal hp hMax hFrame hl hLoaderWarp hb
    (hLoaderCta.symm ▸ hLo) (hLoaderCta.symm ▸ hHi)
  rw [show loader/l.block = g/l.block from hLoaderCta] at hs
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hMember := (Thread.biasParticipantIff 0 (warpIndex l g)).mpr ⟨by omega, by omega⟩
  have hUpper := Protocol.Bias.openingBiasPhaseLeOneForPendingLane hp hMax.1
    (hFrame.metadataProtected hp).1 0 hWork hMember hMissing hs
  exact ⟨s,hs,Nat.le_antisymm hUpper hLower⟩

/-- The stage-one Bias packet of every selected request completes its first ready phase. -/
theorem selectedOpeningSecondBiasPhaseOfMaximal (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let log := X.objects (biasReadyObject l (g/l.block) 1)
    ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  obtain ⟨_,_,_,hSh,hQ1⟩ :=
    selectedOpeningSecondQueryReachedOfMaximal hp hMax hFrame hg hw hb hLo hHi
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨hQ1Entry,_,_⟩ :=
    Loader.openingSecondQueryExpectedFromCursorOfMaximal hp hMax hg hQ1
      (fun lane hLane hBlocked => by
        have hSame := (Step.sameWarp_lane hBlock hg hLane).1
        have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
        rw [hSame.1.2.2]
        exact Protocol.Loader.openingSecondQueryEmptyPhaseForBlockedLane
          hp hMax hSame.1.2.1 hWarp hBlocked)
  have writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc :=
    fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame
  obtain ⟨hBias1,_⟩ :=
    Loader.selectedSecondBiasEntryOfMaximal hp hMax writes hg hw hb hLo hHi hSh hQ1Entry
  obtain ⟨hBias1Entry,credit,hCredit⟩ :=
    Loader.openingSecondBiasExpectedOfMaximal hp hMax hg hBias1
      (fun lane hLane hBlocked => by
        have hSame := (Step.sameWarp_lane hBlock hg hLane).1
        have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
        rw [hSame.1.2.2]
        exact Protocol.Bias.openingSecondBiasEmptyPhase hp hMax
          hSame.1.2.1 hWarp hBlocked)
  apply biasPhaseOfDelivered hp hMax 1 hCredit
  intro half
  obtain ⟨issue,_,hIssue⟩ :=
    Loader.openingSecondBiasBoxesOfMaximal hp hMax writes hg hw hb hLo hHi hSh hBias1Entry half
  refine ⟨issue,_,hIssue,?_,rfl,?_⟩
  · change l.sharedBase+(199680+16384*half.val) = 166912+32768*1+16384*half.val+l.sharedBase
    omega
  · cases hNotify : (X.tensor issue).any (fun o => o.effects.notified) with
    | true => rfl
    | false =>
      exact (hMax.not_grows
        (Protocol.LoaderReady.pendingTensorInput hp hMax.1 hFrame hIssue hNotify)).elim

/-- The second Bias tile remains ready for each pending lane of its stage-one softmax group. -/
theorem openingSecondBiasPhaseForPendingLane (hg : g < l.threads) (hw : warpIndex l g / 4 = 1)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hMissing : PTX.Flow.okPolls (biasReadyObject l (g/l.block) 1) (X.tr g) = 0) :
    let log := X.objects (biasReadyObject l (g/l.block) 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  let loader := g/l.block*l.block+448
  have hLane : 448 < l.block := by rw [hp.block]; decide
  have hl : loader < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
  obtain ⟨hLoaderCta, hLoaderLane⟩ := NamedBar.lane_cta (c := g/l.block)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  have hLoaderWarp : warpIndex l loader = 14 := by
    unfold warpIndex loader
    rw [hLoaderLane]
  obtain ⟨s,hs,hLower⟩ := selectedOpeningSecondBiasPhaseOfMaximal hp hMax hFrame
    hl hLoaderWarp hb (hLoaderCta.symm ▸ hLo) (hLoaderCta.symm ▸ hHi)
  rw [show loader/l.block = g/l.block from hLoaderCta] at hs
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hMember := (Thread.biasParticipantIff 1 (warpIndex l g)).mpr ⟨by omega, hw⟩
  have hUpper := Protocol.Bias.openingBiasPhaseLeOneForPendingLane hp hMax.1
    (hFrame.metadataProtected hp).1 1 hWork hMember hMissing hs
  exact ⟨s,hs,Nat.le_antisymm hUpper hLower⟩

end PTX.Kernels.TmlFa4Fwd.Progress
