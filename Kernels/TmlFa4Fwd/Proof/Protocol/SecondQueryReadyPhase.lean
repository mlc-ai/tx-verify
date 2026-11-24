-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryFaults
import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryReadyOperands

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Query
open PTX PTX.MBarrier PTX.AsyncCopy Thread.Output

/-- A recorded successful Q1 acquire keeps the second query object at its completed phase. -/
theorem secondQueryReadyOfPriorSuccess {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {r : Record Ref} (hr : r ∈ X.objects (queryObject l cta 1))
    (hSuccess : r.reply.waited = some true) :
    let log := X.objects (queryObject l cta 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  let loc := queryObject l cta 1
  let log := X.objects loc
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hr
  have hChecked := X.objects_checked hX loc
  obtain ⟨initial,q,hInitial,hAction,hParity,_⟩ := hChecked.okPoll hj hSuccess
  have hZero : q = 0 := by
    cases record_source hX.tma.2.2.1 hr with
    | wait _ he ha =>
      have hSame := (Action.pollParity.inj (hAction.symm.trans ha)).1
      exact hSame.trans (secondQueryReadyPollParity hp hX he rfl)
    | init _ _ ha | inval _ _ ha | arrive _ _ ha | increment _ _ ha
    | tensor _ _ _ ha | commit _ _ _ ha | arriveOn _ _ _ _ ha | bulk _ _ _ _ ha
    | clc _ _ _ _ ha => rw [hAction] at ha; cases ha
  have hPositive : 0 < initial.phase := by
    subst q
    omega
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨s,hs,hMono⟩ := hChecked.phase_mono hNo (List.getElem?_eq_some_iff.mp hj).1.le
    (Nat.le_refl _) hInitial
  have hUpper := (queryHistoryRange hp hX 1 hr (Nat.le_refl _) hs).1
  exact ⟨s,hs,by omega⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Query
