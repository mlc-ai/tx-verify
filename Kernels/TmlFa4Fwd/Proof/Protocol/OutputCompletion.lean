-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.SingleUnitUpdate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy PTX.MBarrier Thread

/-- Each MMA output-completion object has one possible notification and fault-free polls. -/
theorem outputCompletionHistoryClean {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (outputCompletionObject l cta stage)) : r.fault = none := by
  let loc := outputCompletionObject l cta stage
  let log := X.objects loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hShape {q : Record Ref} (hq : q ∈ log) (h : CounterUpdate q.action) :=
    outputCompletionUpdate hp hX stage hq h
  have hUpdate (ha : CounterUpdate r.action) : r.fault = none := by
    have hInit := outputCompletionInitialized hp hX stage hr
    have hChecked := X.objects_checked hX loc
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_, _, hState, _⟩ := PairTmaRing.state_of_init hX hInit hNo hi
      (by intro n; rw [hShape hr ha]; simp)
    exact hChecked.singleZeroTxUpdateClean hNo hShape
      (fun hq hs hqa hsa => outputCompletionUpdateUnique hp hX stage hq hs hqa hsa)
      hi hState (fun _ _ hs => PairTmaRing.expected_of_init hX hInit hNo hs) ha
  cases ha : r.action with
  | init count => exact actualInitOrPollClean hp hX hr (.inl ⟨count, ha⟩)
  | pollParity parity ok => exact actualInitOrPollClean hp hX hr (.inr ⟨parity, ok, ha⟩)
  | inval => exact (hNo r hr ha).elim
  | arrive | completeTx | increment => exact hUpdate (by rw [ha]; trivial)

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
