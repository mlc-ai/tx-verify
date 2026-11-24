-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheWord

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.TcMma Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Mma (qkByteIndex)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

/-- The recorded B element is the BF16 word of the matched ready generation once the
actual covering writes are ordered around those reads. This applies to either cache plane. -/
theorem Completed.actualCacheOperandElement {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {wait mma : EvId} {use phase d : Nat} {accum : Bool} {mask : List Nat} {op : OperandSpec}
    (h : Completed l X wait (kvUseStage use) phase)
    (block : Fin 4) (step : Fin 8) (plane : CachePlane) {row k : Nat}
    (hr : row < 128) (hk : k < 16)
    (hMma : X.MmaIssue mma d op accum mask) (hEarlier : TraceBefore X wait mma)
    (hBytes : ∀ b : Fin 2, op.byteLoc .b (qkByteIndex row k b.val) =
      (cacheOperand l mma.1 block step use plane).byteLoc .b (qkByteIndex row k b.val))
    {ops : MmaOperands} (hOps : X.async.mmaOperands mma = some ops)
    (hOther : ∀ issue (group : PublishedCopyGroup l X issue) j spec word,
      X.AsyncArrive issue (readyObject l wait.1 (kvUseStage use)) true →
      generation l X issue (kvUseStage use) = phase → (j,spec) ∈ group.copies →
      word < 8 → ∀ b : Fin 2,
      let loc := spec.dst.loc.at (2 * word + b.val)
      op.byteLoc .b (qkByteIndex row k b.val) = some loc →
      ∀ other a data, X.MemWrites other a data → a.Covers loc →
        other = .async (issue.1,j) (.write .copy) ∨
        modelCausality l X loc other (.async (issue.1,j) (.write .copy)) ∨
        modelCausality l X loc (.async mma (.mmaRead true (qkByteIndex row k b.val))) other) :
    ∃ value, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok value := by
  obtain ⟨issue,group,j,spec,bytes,word,hPub,hPhase,hMember,hWord,hRecorded,hUse⟩ :=
    h.actualCacheOperandWord hp hX block step plane hr hk hMma hEarlier hBytes
  have hCopy := ((group.member j spec).mp hMember).2.2
  exact cacheOperandElementOfOrderedWord hp hX hFrame hCopy hRecorded hWord hMma hOps
    (fun b => (hUse b).1) (fun b => (hUse b).2)
    (fun b => hOther issue group j spec word hPub hPhase hMember hWord b (hUse b).1)

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
