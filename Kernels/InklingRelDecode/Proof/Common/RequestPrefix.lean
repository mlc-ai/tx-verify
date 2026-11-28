-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Requests
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.WorkerCall
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Proof
noncomputable section

/-- The number of register requests before a state. -/
def requests {Q L g} : (thread Q L g).D → Nat
  | (.inr ⟨.inl (.dispatch _ _),s⟩,_) => workerRequests s
  | (.inr ⟨.inl (.prologue _),s⟩,_) => dataRequests s
  | _ => 0

/-- The states on which the count is exact: the dispatch loop never takes the retry path, and
no thread waits at the stub of an unselected role. -/
def requestClean {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),s⟩,_) => workerClean s
  | (.inr ⟨.inr _,_⟩,_) => False
  | _ => True

private theorem site_clear (s : Startup.Site) (h : ∀ r, s ≠ .enter r) :
    s.pc ∉ Lib.requestPcs := by
  cases s <;> first | decide | exact absurd rfl (h _)

private theorem startup_clear {L g} {s : Startup.D} {ev sn}
    (hn : Startup.succ L g s ev = some (some sn)) : s.site.pc ∉ Lib.requestPcs := by
  apply site_clear
  intro r h
  simp [Startup.succ, h] at hn

theorem enter_requests {Q L g} (s : Startup.D) (n : Cls → Nat) :
    requests (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) = 0 := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> first | rfl | (rename_i r; cases r <;> rfl)

theorem request_step {Q L g} {s sn : (thread Q L g).D} {ev} (ok : requestClean s)
    (hn : (thread Q L g).next s ev = some (some sn)) :
    requests sn = requests s + if (thread Q L g).pc s ∈ Lib.requestPcs then 1 else 0 := by
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨step,_⟩ := Code.counted_next_some hn
  rcases s with s | ⟨r,s⟩
  · obtain ⟨_,go,rfl⟩ := Code.glue_inl_some step
    rw [enter_requests]
    change 0 = 0 + if s.site.pc ∈ Lib.requestPcs then 1 else 0
    simp [startup_clear go]
  · obtain ⟨_,sub,rfl⟩ := Code.glue_inr_some step
    rcases r with r | r
    · cases r with
      | dispatch w x => exact worker_requests_next ok sub
      | prologue w => exact data_requests_next sub
    · cases sub

end
end PTX.Kernels.InklingRelDecode.Proof
