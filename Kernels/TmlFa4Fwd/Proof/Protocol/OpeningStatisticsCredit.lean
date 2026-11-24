-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsCreditFaults
import Lemmas.Protocol.UnitReachBlocker
import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing.Unit PTX.Flow Correction

/-- When every correction lane has issued its first usable credit, the statistics
slot has advanced beyond the opening phase. -/
theorem openingSlotAdvancedOfCredits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDeps : CreditAcquireDependencies l X) {cta : Nat} (stage : Fin 2)
    (hCredit : ∀ lane : Fin 128, ∃ j, X.Arrive (statsCreditLane l cta lane,j)
      (statsCreditLoc l cta stage) 0 1 true .cta) :
    let log := X.objects (statsCreditLoc l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  let addr := statsCreditLoc l cta stage
  let log := X.objects addr
  let O := statsCreditObject hp hX cta stage
  have hEvents (lane : Fin 128) : ∃ j e, X.get (statsCreditLane l cta lane,j) = some e ∧
      e.kind = .arrive addr 0 1 true .cta := by
    obtain ⟨j,_,he⟩ := hCredit lane
    exact ⟨j,_,he,rfl⟩
  obtain ⟨j,e,he,hKind⟩ := hEvents 0
  have hAct : objectAction X X.async addr (.thread (statsCreditLane l cta 0,j)) =
      some (.arrive 1 0) := by
    obtain ⟨_,kind⟩ := e
    change kind = _ at hKind
    subst kind
    simp [objectAction,he]
  obtain ⟨k,record,hRecord,_,_⟩ := MbarOneShot.Hist.record_of_action hX hAct
  have hNonempty : log ≠ [] := by
    intro h
    change log[k]? = some record at hRecord
    rw [h] at hRecord
    simp at hRecord
  obtain ⟨s,hs⟩ := final_of_init hX O.init O.noInval hNonempty
  obtain ⟨lane,hShort⟩ := O.blocked hX hs
  obtain ⟨i,credit,hGet,hArrive⟩ := hEvents lane
  have hMem : credit ∈ X.tr (statsCreditLane l cta lane) := List.mem_of_getElem? hGet
  have hPos : 0 < arrivals addr (X.tr (statsCreditLane l cta lane)) := by
    unfold arrivals
    exact List.countP_pos_iff.mpr ⟨credit,hMem,by simp [arrivesOn,sourceArrive,hArrive]⟩
  have hAtLeast := arrivals_le_unitRec (m := addr) hX
    (fun _ hr => creditHistoryClean hp hX hDeps (cta := cta) stage hr)
    (statsCreditLane l cta lane)
  exact ⟨s,hs,(hPos.trans_le hAtLeast).trans_le hShort⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
