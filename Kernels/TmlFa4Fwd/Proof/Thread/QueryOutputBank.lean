-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCoverage
import Kernels.TmlFa4Fwd.Proof.MmaFirstQueryOperand
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondQueryAcquire
import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
open PTX.Kernels.TmlFa4Fwd.Correction (outputElementAccess outputChunkLoc)
open PTX.Kernels.TmlFa4Fwd.Mma

/-- An observed output commit has actual earlier issues for both of its initial Q banks,
each preceded by the corresponding parity-zero query acquire. -/
theorem firstOutputCommitQueryBank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (he : FirstOutputCommit X commit spec)
    (stage : Fin 2) : QueryBankBeforeOutput l X commit stage := by
  obtain ⟨g, index⟩ := commit
  obtain ⟨base, hBank⟩ := initialQueryOperandsBeforeOutputCommit hp hX he stage
  obtain ⟨d, op, accum, mask, hIndex, hFirst, _⟩ := hBank 0
  have hAcquire : ∃ wait e, X.get wait = some e ∧
      e.kind = .wait (Output.queryObject l (wait.1 / l.block) stage) 0 true true .cta ∧
      TraceBefore X wait (g, base) := by
    fin_cases stage
    · obtain ⟨i, hi, bar, parity, hWait, _⟩ := firstQueryWaitBeforeGate hp hX hFirst
        (show 2145 ≤ 2197 by decide) (show 2197 ≤ 2642 by decide)
      obtain ⟨rfl, rfl⟩ := firstQueryPollOperands hp hX hWait
      exact ⟨(g, i), _, hWait, rfl, rfl, hi, len_of_get hFirst⟩
    · obtain ⟨wait, e, hGet, hKind, hEarlier⟩ := Thread.Mma.secondQueryBeforeFirstFragment hp hX
        hFirst (show 2259 ≤ 2259 by decide) (show 2259 ≤ 2266 by decide)
      refine ⟨wait, e, hGet, ?_, hEarlier⟩
      rw [show wait.1 = g from hEarlier.1]
      exact hKind
  obtain ⟨wait, e, hGet, hKind, hTrace⟩ := hAcquire
  refine ⟨wait, e, hGet, hKind, ?_⟩
  intro step
  obtain ⟨d, op, accum, mask, hBefore, hIssue, hOperand⟩ := hBank step
  have hOrder : TraceBefore X wait (g, base + step.val) :=
    ⟨hTrace.1, Nat.lt_of_lt_of_le hTrace.2.1 (Nat.le_add_right _ _), len_of_get hIssue⟩
  exact ⟨(g, base + step.val), d, op, accum, mask, ⟨_, hIssue⟩, rfl, hBefore, hOrder, hOperand⟩

private theorem locateWriteIntent {X : Execution} {input : EvId} {a : Acc} {loc : Loc}
    {x y byte : Nat} (h : X.Intent (.async input (.write (.load x y byte))) a true)
    (hCover : a.Covers loc) : ∃ s addr, X.TensorIssue input addr s ∧
      TensorCopy.writeLoc s x y byte = some loc := by
  obtain ⟨_, s, addr, hIssue, hLoc, hSize⟩ := h
  have hSpace := hCover.1
  have hOwner := hCover.2.1
  have hLo := hCover.2.2.1
  have hHi := hCover.2.2.2
  have hAddress : loc.addr = a.loc.addr := by omega
  have hEq : loc = a.loc := by
    cases loc
    cases hA : a.loc
    simp only [hA, Loc.mk.injEq] at hSpace hOwner hAddress ⊢
    exact ⟨hSpace, hOwner, hAddress⟩
  exact ⟨s, addr, hIssue, hEq.symm ▸ hLoc⟩

private theorem destinationAboveBase {s : TensorCopy.Spec} {x y byte : Nat} {loc : Loc}
    (h : TensorCopy.writeLoc s x y byte = some loc) : s.sharedBase.addr ≤ loc.addr := by
  obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp h
  rw [← hLoc]
  exact Nat.le_add_right _ _

/-- Every pending tensor input writes shared bytes at or above the output stage base. -/
theorem tensorInputWriteAboveScratch {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input : EvId} {x y byte : Nat} {a : Acc} {loc : Loc}
    (h : X.Intent (.async input (.write (.load x y byte))) a true) (hCover : a.Covers loc) :
    loc.space = .shared ∧ l.sharedBase + 3072 ≤ loc.addr := by
  obtain ⟨spec, addr, ⟨site, he⟩, hByte⟩ := locateWriteIntent h hCover
  obtain ⟨i, rfl⟩ := actualInputIssuePc hX he
  obtain ⟨_, _, _, hBase, _, _⟩ := actualInputBoxAt hp hX i he
  have hOffset := (by decide : ∀ j : Fin 14, 3072 ≤ (inputSite j).sharedOffset) i
  have hLo := destinationAboveBase hByte
  rw [hBase] at hLo
  change l.sharedBase + (inputSite i).sharedOffset ≤ loc.addr at hLo
  obtain ⟨slot, _, hAt⟩ := Option.map_eq_some_iff.mp hByte
  have hSpace : (spec.sharedLoc slot).space = spec.sharedBase.space := rfl
  rw [hAt] at hSpace
  rw [hBase] at hSpace
  exact ⟨hSpace, by omega⟩

private theorem correctionBelowBias {l : Launch} {writer x row : Nat} {stage : Fin 2}
    {subbox : Fin 4} {loc : Loc} (hx : x < 32) (hy : row < 128)
    (hCover : (outputElementAccess l writer stage subbox x row).Covers loc) :
    loc.addr < l.sharedBase + 166912 := by
  have hXor : x / 4 ^^^ (row % 8) < 2 ^ 3 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hStage := stage.isLt
  have hSub := subbox.isLt
  have h := hCover.2.2.2
  change loc.addr < (outputElementAccess l writer stage subbox x row).loc.addr + 4 at h
  simp only [outputElementAccess, outputChunkLoc, sharedSlot, Loc.at] at h
  omega

/-- An actual or pending tensor write intent overlapping correction staging must be from one
of the four Q subboxes. Every Bias destination is above the correction staging allocation. -/
theorem queryOfOverlappingTensorIntent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input : EvId} {writer x row qx qy qbyte : Nat} {stage : Fin 2} {subbox : Fin 4}
    {a : Acc} {loc : Loc} (hIntent : X.Intent (.async input (.write (.load qx qy qbyte))) a true)
    (hInput : a.Covers loc) (hx : x < 32) (hy : row < 128)
    (hOutput : (outputElementAccess l writer stage subbox x row).Covers loc) :
    ∃ stage plane s, Thread.Loader.QuerySubbox p l X input stage plane s ∧
      TensorCopy.writeLoc s qx qy qbyte = some loc := by
  obtain ⟨g, index⟩ := input
  obtain ⟨s, addr, ⟨pos, he⟩, hAddr⟩ := locateWriteIntent hIntent hInput
  obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
  obtain ⟨_, _, _, hBase, _, _⟩ := actualInputBoxAt hp hX site he
  have hLo := destinationAboveBase hAddr
  rw [hBase] at hLo
  change l.sharedBase + (inputSite site).sharedOffset ≤ loc.addr at hLo
  have hHi := correctionBelowBias hx hy hOutput
  have hGeometry : (∃ qStage : Fin 2,
      inputBarrierBase site + (inputSite site).barrierOffset = 8 * qStage.val) ∨
      166912 ≤ (inputSite site).sharedOffset := by
    fin_cases site <;> first | exact .inl ⟨0, rfl⟩ | exact .inl ⟨1, rfl⟩ | exact .inr (by decide)
  obtain ⟨qStage, hOffset⟩ := hGeometry.resolve_right (by omega)
  have hBar := loaderTensorOffset hp hX site he
  rw [hOffset] at hBar
  obtain ⟨_, plane, hBox⟩ := Thread.Loader.querySubboxOfBarrier hp hX qStage ⟨_, he⟩ hBar
  exact ⟨qStage, plane, s, hBox, hAddr⟩

end PTX.Kernels.TmlFa4Fwd.Thread
