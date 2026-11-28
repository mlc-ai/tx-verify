-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.EmptyTime
public import Lemmas.Protocol.NotifyBlocker
public import Lemmas.Protocol.UnitReachBlocker
public import Lemmas.Protocol.SingleTmaRing.Faults
import Kernels.InklingRelDecode.Proof.Protocol.KV.Reuse
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched PTX.MbarRing
open PTX.MBarrier hiding okPolls

theorem wait_published {Q L m X g c r s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (wait : Waiting L m X r c s g) :
    X.objects (r.obj L c s) ≠ [] := by
  obtain ⟨rfl,q,sc,hn⟩ := wait
  have site : Export.afterInit r.site := by cases r <;> decide
  let j : Fin 12 := ⟨2*s.val+(if r=.empty then 1 else 0),by split <;> omega⟩
  have h := Mbar.next_published hp hX hn site j
  have eq : MbarRow.loc L g (MbarRow.initOffset j)=r.obj L (g/L.block) s := by
    cases r <;> fin_cases s <;> rfl
  rwa [eq] at h

theorem slot_fits {Q L X c s} : ((decl Q L X c).slot s).Fits := by
  change 0 < 8 ∧ 0 < 8192 ∧ 2 * (8 * 8192) ≤ MBarrier.limit
  decide

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
