-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningStatisticsReplay
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWait
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstAffineInput
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstNumeric
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningPackedProbabilities

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

theorem exponentOfOpeningWeight (scale reference : ℝ)
    (scores : Nat → Option ℝ) (i : Nat) :
    ex2E true (scoreValue (affineScore scale (-reference) (scores i))) =
      .ok (.float .f32 (openingPackedWeight scale reference scores i)) := by
  unfold openingPackedWeight
  cases h : affineScore scale (-reference) (scores i) with
  | none => exact hardwareExponentNegInf
  | some x =>
    have hx : valFloat .f32 (.float .f32 x) = .ok x := by simp [valFloat,pure,Except.pure]
    exact ex2E_fin hx

def openingDenominatorRegisters (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062,b32 (Prologue.warpIndex l g)),(2535,b32 l.sharedBase),
    (5127,b32 (3+Prologue.warpIndex l g)),(7132,b32 p.scaleLog2Bits),
    (1230,fl (-abiFloat p.scaleLog2Bits))]

/-- The actual delayed load wait and the operands of the first P store. -/
structure OpeningProbabilityWaitCursor (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  statistics : OpeningStatisticsCursor p l X g stage
  state : TState
  values : Nat → ℝ
  waited : OpeningProbabilityWait X (g,statistics.index+1)
  ordinal : X.TcK (g,statistics.index+1) 4
  site : state.pc = probabilityPc .first 0
  sub : state.sub = 1
  acc : state.acc = []
  fault : state.fault = none
  shared : state.regs 3217 = some (b32 (l.sharedBase+8*stage.val))
  addresses : ∀ q : Fin 4, state.regs (probabilityReg .first q) =
    some (b32 (probabilityAddress l g stage q))
  packed : ∀ q : Fin 4, ∀ i < 8, state.regs (firstPackedReg q+i) =
    some (probabilityDoubleWord (fun k => values (32*q.val+k)) i)
  unpacked : ∀ i < 8,
    state.regs (firstUnpackBase 0+2*i) = some (probabilityWord values (2*(7-i))) ∧
    state.regs (firstUnpackBase 0+2*i+1) = some (probabilityWord values (2*(7-i)+1))
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (statistics.index+2)) (some state)
  continuation :
    Run kernel Assumptions.all l g state ((X.tr g).drop (statistics.index+2)) statistics.ending

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) {g : Nat}
    (hg : g < l.threads) {stage : Fin 2} (c : OpeningStatisticsCursor p l X g stage)
    (hRelease : c.index+1 = (X.tr g).length → ∃ Y, Maximal l kernel Assumptions.all m Y ∧
      Y.tr = X.tr ∧ Step.Released l Y g)
include hp hg c hRelease

/-- An active lane with its recorded statistics and a releasable rendezvous issues
its actual first delayed Tensor Memory wait. -/
theorem OpeningStatisticsCursor.probabilityWaitWithWeightsAndRegistersOfMaximal :
    ∃ cursor : OpeningProbabilityWaitCursor p l X g stage, cursor.statistics = c ∧
      cursor.values = openingPackedWeight (abiFloat p.scaleLog2Bits)
        (abiFloat p.scaleLog2Bits*(scoreMax c.scores (List.range 128)).getD 0) c.scores ∧
      (∀ i < 128, cursor.state.regs (1231+i) = some (fl (cursor.values i))) ∧
      (∀ r ∈ firstTransitionRegs, cursor.state.regs r = c.state.regs r) ∧
      (∀ r ∈ [1062,2535,5127,7132], cursor.state.regs r = c.state.regs r) ∧
      cursor.state.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)) := by
  let j := c.index
  let t := c.state
  let scores := c.scores
  let scale := abiFloat p.scaleLog2Bits
  let reference := scale*(scoreMax scores (List.range 128)).getD 0
  let values := openingPackedWeight scale reference scores
  obtain ⟨v,hV,hScale,hOffset,hRead,hSource,hPreFrame,hPre,hNeg⟩ :=
    firstShiftAfterStatsWithNegScaleLocal (g := g) hp scores (c.ready.mono trivial)
      c.masked c.ready.2.2.2.2.1 c.ready.2.2.2.2.2.1
  obtain ⟨w,hW,hPacked,hWeights,hPackFrame,hPack⟩ :=
    firstShiftedPacksLocal (g := g) hp reference scores values (exponentOfOpeningWeight _ _ _)
      (firstShiftValues v) (firstShiftLogits scores) hV hRead hSource
      (fun _ _ => ⟨rfl,rfl⟩) hScale hOffset
  obtain ⟨ready,hReady,hUnpack,hWords,hUnpackFrame⟩ :=
    probabilityUnpackLocal (g := g) 0 values hW (by simpa using hPacked 0)
  have hBound : j+1 ≤ (X.tr g).length := by
    obtain ⟨_,he,_⟩ := c.published
    exact len_of_get he
  obtain ⟨he,hPrefix,hTail⟩ := openingProbabilityWaitOfMaximal hp hg (Nat.zero_lt_succ j) hBound
    hReady c.recorded ((hPre.trans hPack).trans hUnpack) c.continuation hRelease
  let after := {ready with sub := 1}
  have hKeep (r : Nat) (hr : r ∈ [3217,3223,3224,3225,3226]) : after.regs r = t.regs r := by
    have hFlags : List.all [3217,3223,3224,3225,3226] (fun r =>
        !((shiftItems 0).flatMap FmaItem.writes).contains r) = true := by decide +kernel
    have hLow : r < 3879 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      omega
    have hPre : r ∉ [1230,3686,8024,8025,8026] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      omega
    have hAside : r < 3815 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      omega
    have hWritten := hPackFrame r (by simpa using List.all_eq_true.mp hFlags r hr)
      (.inr (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        omega)) (.inl hAside) (.inl (by omega))
    exact (hUnpackFrame r (.inl hLow)).trans (hWritten.trans (hPreFrame r hPre))
  have hTk : X.TcK (g,j+1) 4 := ⟨⟨_,he,rfl⟩,c.tensorCount⟩
  refine ⟨⟨c,after,values,he,hTk,hReady.1,rfl,hReady.2.2.1,hReady.2.2.2.1,
    (hKeep 3217 (by simp)).trans c.shared,?_,?_,hWords,hPrefix,hTail⟩,rfl,rfl,?_,?_,?_⟩
  · intro q
    have hr : probabilityReg .first q ∈ [3217,3223,3224,3225,3226] := by
      fin_cases q <;> decide
    exact (hKeep _ hr).trans (c.addresses q)
  · intro q i hi
    have hRange : firstUnpackBase 0+16 ≤ firstPackedReg q+i := by
      rw [show firstUnpackBase 0 = 3879 from rfl]
      unfold firstPackedReg
      omega
    exact (hUnpackFrame _ (.inr hRange)).trans (hPacked q i hi)
  · intro i hi
    exact (hUnpackFrame _ (.inl (by change 1231+i < 3879; omega))).trans (hWeights i hi)

  · intro r hr
    have hRegisters : firstTransitionRegs.all (fun reg =>
      !((shiftItems 0).flatMap FmaItem.writes).contains reg) = true := by decide +kernel
    have hFlags := List.all_eq_true.mp hRegisters r hr
    simp only [firstTransitionRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    have hPre : r ∉ [1230,3686,8024,8025,8026] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      omega
    have hUnpack : r < firstUnpackBase 0 ∨ firstUnpackBase 0+16 ≤ r := by
      change r < 3879 ∨ 3879+16 ≤ r
      omega
    exact (hUnpackFrame r hUnpack).trans ((hPackFrame r (by simpa using hFlags)
      (by omega) (by omega) (.inl (by omega))).trans (hPreFrame r hPre))
  · have hCarry (r : Nat) (hr : r ∈ [1062,2535,5127,7132,1230]) :
        after.regs r = v.regs r := by
      have hFlags : [1062,2535,5127,7132,1230].all (fun reg =>
          !((shiftItems 0).flatMap FmaItem.writes).contains reg) = true := by decide +kernel
      have hWrite := List.all_eq_true.mp hFlags r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      exact (hUnpackFrame r (by change r < 3879 ∨ 3879+16 ≤ r; omega)).trans
        (hPackFrame r (by simpa using hWrite) (by omega) (by omega) (.inl (by omega)))
    refine ⟨?_,(hCarry 1230 (by decide)).trans hNeg⟩
    intro r hr
    apply (hCarry r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      tauto)).trans
    apply hPreFrame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    omega

theorem OpeningStatisticsCursor.probabilityWaitWithWeightsOfMaximal :
    ∃ cursor : OpeningProbabilityWaitCursor p l X g stage, cursor.statistics = c ∧
      cursor.values = openingPackedWeight (abiFloat p.scaleLog2Bits)
        (abiFloat p.scaleLog2Bits*(scoreMax c.scores (List.range 128)).getD 0) c.scores ∧
      (∀ i < 128, cursor.state.regs (1231+i) = some (fl (cursor.values i))) ∧
      ∀ r ∈ firstTransitionRegs, cursor.state.regs r = c.state.regs r := by
  obtain ⟨cursor,hStats,hValues,hWords,hCarry,_,_⟩ :=
    c.probabilityWaitWithWeightsAndRegistersOfMaximal hp hg hRelease
  exact ⟨cursor,hStats,hValues,hWords,hCarry⟩

theorem OpeningStatisticsCursor.probabilityWaitOfMaximal :
    Nonempty (OpeningProbabilityWaitCursor p l X g stage) := by
  obtain ⟨cursor,_,_,_,_⟩ := c.probabilityWaitWithWeightsOfMaximal hp hg hRelease
  exact ⟨cursor⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
