-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGlue
public import Kernels.FlashKdaFwd.Proof.Progress.Guard

@[expose] public section

/-! # The result facts without a safety hypothesis

The read-back theorems use that visibility at a byte has no cycle, which the library proves
for executions whose synchronization is *guarded* (`SyncGuarded`, `Lemmas/Order/GuardOrder.lean`:
successful polls head canonical spin loops, no memory order comes from a release/acquire pair
or a thread fence, and no record of an mbarrier history faults before a successful poll).
`Proof/Progress/Guard.lean: syncGuarded` gives this from consistency and "not unsafe". Here it
follows from the protocol contract instead (`Facts.syncGuarded`): the first two parts are scans
of the decoded program, and the third is `Facts.mbarFaultFree` with `Facts.mbarInitFirst`.

So the result facts need no safety hypothesis: `resultFacts_of_contracts` has the form of the
field `result` of `Top.Layers` (`Proof/Top/Layers.lean`), given the five contracts for the
execution. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {O : Owners}

/-- **Synchronization is guarded in every consistent execution that satisfies the protocol
contract.** -/
theorem Facts.syncGuarded (F : Facts P L X) (hP : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) : SyncGuarded L kernel X where
  spin _ _ _ _ _ _ he := Proof.Top.poll_canonical hX he
  noMemSync e f :=
    ⟨noSynchronizesWith_of (fun _ _ _ _ he => Proof.Progress.noReleasingStore hX he)
      (fun _ _ _ _ _ he => (Proof.Progress.noAtomicEvent hX he).elim) e f,
      not_fenceSync_of_noFence (fun _ _ _ => Proof.Progress.noThreadFence hX) e f⟩
  noFault m _ _ r _ hr _ _ _ := by
    have hmem := List.mem_of_getElem? hr
    by_cases hinit : ∃ n, r.action = .init n
    · obtain ⟨c, hfirst⟩ := F.mbarInitFirst hP hX m (List.ne_nil_of_mem hmem)
      obtain ⟨r0, -, -, hf0, huniq⟩ := hfirst r hmem
      rw [huniq r hmem hinit]
      exact hf0
    · exact F.mbarFaultFree hP hX m r hmem fun n hn => hinit ⟨n, hn⟩

/-- **The result facts of one consistent execution, from the five contracts**: the protocol
contract `Facts`, the classification of the buffer region `UnionFacts`, the source bytes of the
stores `StoreCover` (reference layer, for some owner functions `O`), the events that write
global memory `StoresIssued` (reference layer) and the content of the compute threads' writes
`OutContent` (value layer). -/
theorem resultFacts_of_contracts (hP : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (F : Facts P L X)
    (U : UnionFacts L X (ctaTiles P) O) (C : StoreCover L X O) (S : StoresIssued P L X)
    (V : OutContent P L X O) : Proof.Top.ResultFacts P L mem0 X :=
  resultFacts hP hX S F U C V (F.syncGuarded hP hX)

end PTX.Kernels.FlashKdaFwd.Protocol
