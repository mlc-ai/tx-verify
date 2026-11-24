-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.SingleUnitUpdate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Scores

/-- A score-ready notification accepts its credit when the actual history has none before it. -/
theorem scoreReadyInitialPhaseClean {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hi : (X.objects (scoreReadyObject l cta stage))[i]? = some r)
    (hUnits : unitsBefore (X.objects (scoreReadyObject l cta stage)) i = 0) :
    r.fault = none := by
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  have hMem := List.mem_of_getElem? hi
  have hNo := objects_noInval hX.tma.2.2.1 (fun j _ => noMbarInval hX (i := j)) loc
  have hUpdate (hu : CounterUpdate r.action) : r.fault = none := by
    have hShape {q : Record Ref} (hq : q ∈ log) (ha : CounterUpdate q.action) :
        q.action = .arrive 1 0 := by
      obtain ⟨_, _, _, _, _, _, _, hAction⟩ := scoreReadyUpdate hp hX stage hq ha
      exact hAction
    have hInit := scoreReadyInitialized hp hX stage hMem
    obtain ⟨_, _, hState, _⟩ := PairTmaRing.state_of_init hX hInit hNo hi
      (by intro n; rw [hShape hMem hu]; simp)
    apply (X.objects_checked hX loc).zeroTxUpdateCleanOfUnits hNo hShape hi hState _ hu
    intro before hs
    rw [PairTmaRing.expected_of_init hX hInit hNo hs, hUnits]
    decide
  cases ha : r.action with
  | init count => exact actualInitOrPollClean hp hX hMem (.inl ⟨count, ha⟩)
  | pollParity parity ok => exact actualInitOrPollClean hp hX hMem (.inr ⟨parity, ok, ha⟩)
  | inval => exact (hNo r hMem ha).elim
  | arrive | completeTx | increment => exact hUpdate (by rw [ha]; trivial)

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
