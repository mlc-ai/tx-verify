-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopies
public import Kernels.TmlFa4Fwd.Proof.ResultGeometry
public import Lemmas.Protocol.CpAsyncPhase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX AsyncCopy

noncomputable section

private theorem packetCovers {X : Execution} {copy : EvId} {s : Spec} {loc : Loc}
    (hCopy : X.Copy copy s) (hWhole : s.writes = .whole) (hByte : s.dst.Covers loc) :
    AsyncCovers X copy (.write .copy) loc :=
  ⟨s.dst, true, ⟨rfl, s, hCopy, hWhole, rfl⟩, hByte⟩

private theorem operandCovers {X : Execution} {mma : EvId} {d index : Nat} {isB accum : Bool}
    {s : TcMma.OperandSpec} {mask : List Nat} {loc : Loc}
    (hMma : X.MmaIssue mma d s accum mask)
    (hByte : s.byteLoc (if isB then .b else .a) index = some loc) :
    AsyncCovers X mma (.mmaRead isB index) loc :=
  ⟨{ loc := loc, size := 1 }, false, ⟨rfl, rfl, .inl ⟨d, s, accum, mask, hMma, hByte⟩⟩,
    ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩

variable {l : Launch} {X : Execution}

/-- A successful KV wait orders the actual packet byte before the MMA that consumes it. -/
theorem packetBeforeOperand {copy mma wait : EvId} {s : Spec} {op : TcMma.OperandSpec}
    {d index : Nat} {isB accum : Bool} {mask : List Nat} {loc : Loc} (hCta : SameCta l copy.1 mma.1)
    (hCopy : X.Copy copy s) (hWhole : s.writes = .whole) (hCover : s.dst.Covers loc)
    (hMma : X.MmaIssue mma d op accum mask)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc)
    (hFinish : AsyncFinished l X copy (.write .copy) wait) (hIssue : baseCausality l X wait mma) :
    modelCausality l X loc (.async copy (.write .copy)) (.async mma (.mmaRead isB index)) :=
  ⟨.inl hCta, .direct ⟨packetCovers hCopy hWhole hCover, operandCovers hMma hLoc,
    .inl ⟨wait, hFinish, hIssue⟩⟩⟩

/-- The observed MMA completion orders its shared read before an ordinary copy reuses that byte. -/
theorem operandBeforePacketReuse {copy mma wait : EvId} {s : Spec} {op : TcMma.OperandSpec}
    {d index : Nat} {isB accum : Bool} {mask : List Nat} {loc : Loc} (hCta : SameCta l mma.1 copy.1)
    (hMma : X.MmaIssue mma d op accum mask)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc) (hCopy : X.Copy copy s)
    (hWhole : s.writes = .whole) (hCover : s.dst.Covers loc) {scope : MbarScope}
    (hObserved : AsyncObserved X mma .mmaDone wait true scope)
    (hScope : ScopesMeet l .cluster mma.1 scope wait.1) (hIssue : baseCausality l X wait copy) :
    modelCausality l X loc (.async mma (.mmaRead isB index)) (.async copy (.write .copy)) :=
  ⟨.inl hCta, .direct ⟨operandCovers hMma hLoc, packetCovers hCopy hWhole hCover,
    .inl ⟨wait, .inr ⟨scope, hObserved, hScope⟩, hIssue⟩⟩⟩

/-- An observed TMA tile can supply an operand byte independently of the LSU packet path. -/
theorem tensorBeforeOperand {tensor mma wait : EvId} {s : TensorCopy.Spec} {address x y k : Nat}
    {op : TcMma.OperandSpec} {d index : Nat} {isB accum : Bool} {mask : List Nat} {loc : Loc}
    (hCta : SameCta l tensor.1 mma.1) (hTensor : X.TensorIssue tensor address s)
    (hWrite : TensorCopy.writeLoc s x y k = some loc) (hMma : X.MmaIssue mma d op accum mask)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc)
    (hFinish : AsyncFinished l X tensor (.write (.load x y k)) wait)
    (hIssue : baseCausality l X wait mma) :
    modelCausality l X loc (.async tensor (.write (.load x y k)))
      (.async mma (.mmaRead isB index)) :=
  ⟨.inl hCta, .direct
    ⟨⟨{ loc := loc, size := 1 }, true, ⟨rfl, s, address, hTensor, hWrite, rfl⟩,
      ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩, operandCovers hMma hLoc,
      .inl ⟨wait, hFinish, hIssue⟩⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
