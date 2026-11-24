-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCompletion
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarRingBlocker
import Lemmas.Protocol.MbarUnitTx

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.MBarrier PTX.AsyncCopy Thread

/-- Once its unique terminal notification has arrived, an output stage stays at phase one. -/
theorem terminalOutputPhaseOfNotification {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (outputCompletionObject l cta stage)) (hArrival : r.action = .arrive 1 0) :
    let log := X.objects (outputCompletionObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  classical
  let loc := outputCompletionObject l cta stage
  let log := X.objects loc
  have hInit := outputCompletionInitialized hp hX stage hr
  have hCheck := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨initial,hi,hCount,hClean,_⟩ := hInit r hr
  have hLength : 0 < log.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨st,hs,hExpected⟩ := ObjectInit.checked_expected_after_init
    hCheck hNo hi hCount hClean hLength (Nat.le_refl _)
  have hShape {q : Record Ref} (hq : q ∈ log) (hUpdate : CounterUpdate q.action) :
      q.action = .arrive 1 0 := outputCompletionUpdate hp hX stage hq hUpdate
  have hUnit : UnitTx log 0 := by
    refine ⟨?_,?_,fun _ _ h => PairTmaRing.expected_of_init hX hInit hNo h⟩
    · intro q hq _ _ _ hAct
      exact Action.arrive.inj (hAct.symm.trans (hShape hq (by rw [hAct]; trivial)))
    · intro q hq _ _ hAct
      have h := hShape hq (by rw [hAct]; trivial)
      rw [hAct] at h
      cases h
  have hTx : st.tx = 0 := by simpa using hUnit.tx hCheck hNo (Nat.le_refl _) hs
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro q hq hAct
    have h := hShape hq (by rw [hAct]; trivial)
    rw [hAct] at h
    cases h
  have hUpper : unitsBefore log log.length ≤ 1 := by
    simpa using hCheck.unitsBefore_le_card {r.id}
      (fun _ q c tx hq hFault hAct => (hUnit.arrive q (List.mem_of_getElem? hq) hFault c tx hAct).1)
      (fun _ _ q _ _ hq _ hAct => Finset.mem_singleton.mpr
        (outputCompletionUpdateUnique hp hX stage (List.mem_of_getElem? hq) hr
          (by rw [hAct]; trivial) (by rw [hArrival]; trivial)))
  have hFault := outputCompletionHistoryClean hp hX stage hr
  have hUnits : arrivalUnits log = 1 := by
    have hLow : 1 ≤ arrivalUnits log := by
      rw [arrivalUnits_eq_length (fun q hq c tx hf ha => (hUnit.arrive q hq hf c tx ha).1)]
      exact List.length_pos_of_mem (List.mem_filter.mpr
        ⟨hr,countedArrive_iff.mpr ⟨hFault,1,0,hArrival⟩⟩)
    rw [unitsBefore,List.take_length] at hUpper
    omega
  have hPhase := MbarRing.Blocker.units_eq_phase hCheck hNo hs hTx hExpected hIncr
  exact ⟨st,hs,hPhase.symm.trans hUnits⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
