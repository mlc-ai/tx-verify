-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedNumeric
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainRescale
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedRescale

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue

noncomputable section

private def plainShiftPreserved (r : Nat) : Bool :=
  !plainStatsWritten.contains r && !([5519,8691].contains r)

private def biasedShiftPreserved (r : Nat) : Bool :=
  !biasedStatsWritten.contains r && !([4572,8444,8445].contains r)

private theorem plainShiftReadsPreserved :
    (shiftItems 2).all (fun it => plainShiftPreserved it.a) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem biasedShiftReadsPreserved :
    (shiftItems 1).all (fun it => biasedShiftPreserved it.a) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem plainExpPreserved :
    unbiasedExpFrame.all plainShiftPreserved = true := by decide +kernel

private theorem biasedExpPreserved :
    (biasedExpFrame.filter (· != 637)).all biasedShiftPreserved = true := by decide +kernel

/-- Once the plain alpha is ready, the actual coefficient store and statistics arrival
preserve the physical scores and establish the paired scale and offset. -/
theorem plainProbabilityFrameAfterAlpha {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} (hw : warp.val = warpIndex l g)
    {t : TState} {ending : Option TState} (old candidate : Option ℝ) (scores : Nat → Option ℝ)
    (ht : At t 6886 [(5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
      (2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
      (1492,alphaWord (abiFloat p.scaleLog2Bits) old candidate)])
    (hRef : t.regs 5514 = some (finiteRefValue (chosenReference
      (abiFloat p.scaleLog2Bits) old candidate)))
    (hNegative : t.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)))
    (hPaired : readERealPair l g t (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))))
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (scores (32*q.val+2*k.val)))
          (scoreValue (scores (32*q.val+2*k.val+1)))))
    (hFrame : ∀ r ∈ unbiasedExpFrame, ∃ v, t.regs r = some v)
    (hAddress : ∀ q : Fin 4, t.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)))
    (hSignal : t.regs 5187 = some (b32 (l.sharedBase+8*(stageOf warp).val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+2 < (X.tr g).length) :
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale*(chosenReference scale old candidate).getD 0
    ∃ u, Nonempty
      (RepeatedProbabilityShiftFrame p l .unbiased g (stageOf warp) u scores reference) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+2)) ending := by
  let scale := abiFloat p.scaleLog2Bits
  let chosen := chosenReference scale old candidate
  obtain ⟨a,hA,_,_,hAfter,hKeepA⟩ :=
    plainRescalePublicationInPrefix hp warp hw ht hRun (hAvail.imp_right (by intro h; omega))
  obtain ⟨u,hU,hTail,hOffset,hKeepU⟩ :=
    plainShiftOffsetTraceInPrefix chosen scale hA
      ((hKeepA _ (by decide)).trans hRef) ((hKeepA _ (by decide)).trans hNegative)
      hAfter (recordedProbabilitySuffixNonempty hAfter hAvail)
  have keep (r : Nat) (hr : plainShiftPreserved r = true) : u.regs r = t.regs r := by
    simp only [plainShiftPreserved,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not] at hr
    exact (hKeepU _ hr.2).trans (hKeepA _ hr.1)
  let words (r : Nat) := (u.regs r).getD (.pred false)
  let inputs (it : FmaItem) := (scores (it.x-5520),scores (it.y-5520))
  have pairAt (it : FmaItem) (hi : it ∈ shiftItems 2) : it.pk = none ∧
      u.regs it.a = some (.pair (scoreValue (inputs it).1) (scoreValue (inputs it).2)) := by
    obtain ⟨hNo,hPair⟩ := plainLogitsForShift scores hPacked it hi
    exact ⟨hNo,(keep _ (List.all_eq_true.mp plainShiftReadsPreserved _ hi)).trans hPair⟩
  have wordAt (r : Nat) {v : Value} (hv : u.regs r = some v) : words r = v := by simp [words,hv]
  have hScale :
      readERealPair l g u (.reg 8692) = some (.ok ((scale : EReal),(scale : EReal))) := by
    unfold readERealPair
    rw [show readValue l g u 64 (.reg 8692) = readValue l g t 64 (.reg 8692) by
      simp only [readValue,readReg,keep 8692 (by decide)]]
    exact hPaired
  refine ⟨u,⟨⟨words,inputs,false,hU,?_,?_,fun _ _ => ⟨rfl,rfl⟩,hScale,hOffset,?_,
    nofun,nofun,nofun,?_,?_⟩⟩,hTail⟩
  · intro it hi r hr
    have h := pairAt it hi
    have hR : r = it.a := by simpa only [FmaItem.reads,h.1,List.mem_singleton] using hr
    subst r
    exact h.2.trans (congrArg some (wordAt _ h.2).symm)
  · intro it hi
    have h := pairAt it hi
    simp [FmaItem.packOk,FmaItem.src,h.1,words,h.2,splitValue]
  · intro r hr
    obtain ⟨v,hv⟩ := hFrame r hr
    have h := (keep r (List.all_eq_true.mp plainExpPreserved r hr)).trans hv
    rwa [wordAt _ h]
  · intro _ q
    exact wordAt _ ((keep _ (by fin_cases q <;> decide)).trans (hAddress q))
  · intro _
    exact wordAt _ ((keep _ (by decide)).trans hSignal)

/-- The corresponding biased continuation retains its mixed-path predicate and
selects the probability tile of the actual warp stage. -/
theorem biasedProbabilityFrameAfterAlpha {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} (hw : warp.val = warpIndex l g)
    {t : TState} {ending : Option TState} (old candidate : Option ℝ) (scores : Nat → Option ℝ)
    (ht : At t 5675 [(1062,b32 warp.val),(2535,b32 l.sharedBase),
      (5127,b32 (3+warp.val)),(1362,alphaWord (abiFloat p.scaleLog2Bits) old candidate)])
    (hRef : t.regs 4565 = some (finiteRefValue (chosenReference
      (abiFloat p.scaleLog2Bits) old candidate)))
    (hNegative : t.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)))
    (hScale : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (mixed : Bool) (hMixed : t.regs 634 = some (.pred mixed))
    (hLogits : ∀ i ∈ biasBodyItems true,
      t.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1)))))
    (hFrame : ∀ r ∈ biasedExpFrame, r ≠ 637 → ∃ v, t.regs r = some v)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+2 < (X.tr g).length) :
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale*(chosenReference scale old candidate).getD 0
    ∃ u, Nonempty (RepeatedProbabilityShiftFrame p l .biased g (stageOf warp) u scores reference) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+2)) ending := by
  let scale := abiFloat p.scaleLog2Bits
  let chosen := chosenReference scale old candidate
  obtain ⟨a,hA,_,_,hAfter,hStage,hKeepA⟩ :=
    biasedRescalePublicationInPrefix hp warp hw ht hRun (hAvail.imp_right (by intro h; omega))
  obtain ⟨u,hU,hTail,hPairScale,hOffset,hKeepU⟩ :=
    biasedShiftScaleTraceInPrefix hp chosen hA
      ((hKeepA _ (by decide)).trans hRef) ((hKeepA _ (by decide)).trans hNegative)
      ((hKeepA _ (by decide)).trans hScale) hAfter (recordedProbabilitySuffixNonempty hAfter hAvail)
  have keep (r : Nat) (hr : biasedShiftPreserved r = true) : u.regs r = t.regs r := by
    simp only [biasedShiftPreserved,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not] at hr
    exact (hKeepU _ hr.2).trans (hKeepA _ hr.1)
  let words (r : Nat) := (u.regs r).getD (.pred false)
  let inputs (it : FmaItem) := (scores (it.x-1363),scores (it.y-1363))
  have pairAt (it : FmaItem) (hi : it ∈ shiftItems 1) : it.pk = none ∧
      u.regs it.a = some (.pair (scoreValue (inputs it).1) (scoreValue (inputs it).2)) := by
    obtain ⟨hNo,hPair⟩ := biasedLogitsForShift scores hLogits it hi
    exact ⟨hNo,(keep _ (List.all_eq_true.mp biasedShiftReadsPreserved _ hi)).trans hPair⟩
  have wordAt (r : Nat) {v : Value} (hv : u.regs r = some v) : words r = v := by simp [words,hv]
  have hStage' := (hKeepU 637 (by decide)).trans hStage
  refine ⟨u,⟨⟨words,inputs,mixed,hU,?_,?_,fun _ _ => ⟨rfl,rfl⟩,hPairScale,hOffset,?_,
    fun _ => (keep _ (by decide)).trans hMixed,fun _ => wordAt _ hStage',
      fun _ => wordAt _ ((keep _ (by decide)).trans ht.2.2.2.2.2.1),nofun,nofun⟩⟩,hTail⟩
  · intro it hi r hr
    have h := pairAt it hi
    have hR : r = it.a := by simpa only [FmaItem.reads,h.1,List.mem_singleton] using hr
    subst r
    exact h.2.trans (congrArg some (wordAt _ h.2).symm)
  · intro it hi
    have h := pairAt it hi
    simp [FmaItem.packOk,FmaItem.src,h.1,words,h.2,splitValue]
  · intro r hr
    by_cases hStageReg : r = 637
    · subst r
      rwa [wordAt _ hStage']
    have hLive : r ∈ (biasedExpFrame.filter (· != 637)) :=
      List.mem_filter.mpr ⟨hr,by simpa using hStageReg⟩
    obtain ⟨v,hv⟩ := hFrame r hr hStageReg
    have h := (keep _ (List.all_eq_true.mp biasedExpPreserved r hLive)).trans hv
    rwa [wordAt _ h]


end
end PTX.Kernels.TmlFa4Fwd.Softmax
