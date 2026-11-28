-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.RequestCount
public import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
public import Kernels.InklingRelDecode.Proof.Lib.RegLedger
import Kernels.InklingRelDecode.Proof.Prologue.RegLedger
import Kernels.InklingRelDecode.Proof.Softmax.RegLedger
import Kernels.InklingRelDecode.Proof.Epilogue.RegLedger
import Kernels.InklingRelDecode.Proof.Dispatch.RegLedger
import Kernels.InklingRelDecode.Proof.Loader.RegLedger
import Kernels.InklingRelDecode.Proof.Mma.RegLedger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow
noncomputable section

private theorem startup_ledger (s : Startup.Site) : Lib.ledgerOk s.pc 0 0 = true := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

/-- **The ledger of register requests and barrier-1 events holds at every clean state.** -/
theorem state_ledger {Q L g} (s : (thread Q L g).D) (ok : requestClean s) :
    Lib.ledgerOk ((thread Q L g).pc s) (publication s) (requests s) = true := by
  obtain ⟨s,n⟩ := s
  rcases s with s | ⟨r,s⟩
  · exact startup_ledger s.site
  · rcases r with r | r
    · cases r with
      | prologue w =>
        rcases s with s | ⟨ent,s | ⟨_,s⟩⟩
        · exact Prologue.reg_ledger s.site
        · exact Softmax.reg_ledger s.site
        · exact Epilogue.reg_ledger s.site
      | dispatch w x =>
        rcases s with s | ⟨r,s⟩
        · obtain ⟨g1,g2,early,late⟩ := ok
          exact Dispatch.reg_ledger s.site s.round (fun h => early h) (fun h => late h) ⟨g1,g2⟩
        · cases r with
          | loader k =>
            have z : k = 0 := ok
            subst z
            have h := Loader.reg_ledger s.site
            simp only [publication,requests,workerPublication,workerRequests,Nat.mul_zero,
              Nat.zero_add]
            exact h
          | mma k =>
            have z : k = 0 := ok
            subst z
            have h := Mma.reg_ledger s.site
            simp only [publication,requests,workerPublication,workerRequests,Nat.mul_zero,
              Nat.zero_add]
            exact h
    · change Lib.ledgerOk r.pc 0 0 = true
      cases r <;> decide

/-- The role a state belongs to, by the position of its thread. -/
def DataRole {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.prologue _),_⟩,_) => True
  | _ => False

def WorkerRole {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),_⟩,_) => True
  | _ => False

private theorem site_pc_clear (s : Startup.Site) (h : ∀ r, s ≠ .enter r) :
    s.pc ∉ Lib.requestPcs := by
  cases s <;> first | decide | exact absurd rfl (h _)

private theorem site_clear (d : Startup.D) (h : Startup.enterOf d = none) :
    d.site.pc ∉ Lib.requestPcs := by
  apply site_pc_clear
  intro r hr
  simp [Startup.enterOf, hr] at h

/-- **A state at a request belongs to the default partition or to the workers, with the
position of that role.** -/
theorem state_group {Q L g} (s : (thread Q L g).D) (ok : requestClean s)
    (act : ∀ st n, s = (.inl st,n) → Startup.enterOf st = none)
    (h : (thread Q L g).pc s ∈ Lib.requestPcs) :
    (DataRole s ∧ Lib.dataReq ((thread Q L g).pc s) = true) ∨
      (WorkerRole s ∧ Lib.workerReq ((thread Q L g).pc s) = true) := by
  obtain ⟨s,n⟩ := s
  rcases s with s | ⟨r,s⟩
  · exact (site_clear s (act s n rfl) h).elim
  · rcases r with r | r
    · cases r with
      | prologue w =>
        refine .inl ⟨trivial,?_⟩
        rcases s with s | ⟨ent,s | ⟨_,s⟩⟩
        · exact Prologue.request_group s.site h
        · exact Softmax.request_group s.site h
        · exact Epilogue.request_group s.site h
      | dispatch w x =>
        refine .inr ⟨trivial,?_⟩
        rcases s with s | ⟨r,s⟩
        · exact Dispatch.request_group s.site h
        · cases r with
          | loader k => exact Loader.request_group s.site h
          | mma k => exact Mma.request_group s.site h
    · exact ok.elim

end
end PTX.Kernels.InklingRelDecode.Proof
