-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Publication
public import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Lemmas.Kernel.Safety.StateInvU
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame
noncomputable section

def publication {Q L g} : (thread Q L g).D → Nat
  | (.inr ⟨.inl (.dispatch _ _),s⟩,_) => workerPublication s
  | (.inr ⟨.inl (.prologue _),s⟩,_) => dataPublication s
  | _ => 0

private theorem startup_clear (s : Startup.Site) : s.pc ∉ Lib.barOneSites := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem enter_phase {Q L g} (s : Startup.D) (n : Cls → Nat) :
    publication (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) = 0 := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> first | rfl | (rename_i r; cases r <;> rfl)

private theorem phase_next {Q L g} {s sn : (thread Q L g).D} {ev}
    (hn : (thread Q L g).next s ev = some (some sn)) :
    publication sn = publication s + if (thread Q L g).pc s ∈ Lib.barOneSites then 1 else 0 := by
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨step,_⟩ := Code.counted_next_some hn
  rcases s with s | ⟨r,s⟩
  · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some step
    rw [enter_phase]
    change 0 = 0 + if s.site.pc ∈ Lib.barOneSites then 1 else 0
    simp [startup_clear]
  · obtain ⟨_,sub,rfl⟩ := Code.glue_inr_some step
    rcases r with r | r
    · cases r with
      | dispatch w x => exact worker_publication_next sub
      | prologue w => exact data_publication_next sub
    · cases sub

private def phaseTable (Q L) : RoleTable (thread Q L) where
  J _ _ := True
  Ev g s e := Execution.isBarId 1 e = decide ((thread Q L g).pc s ∈ Lib.barOneSites)

/-- The phase is the exact count on the trace before this state. This induction
uses only tracking of the control machine, including at worker dispatch. -/
theorem publication_prefix {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (nu : NoUbBefore X g k) (hs : stateAt (thread Q L) X g k = some (some s)) :
    ((X.tr g).take k).countP (Execution.isBarId 1) = publication s := by
  apply RoleTable.countInvU (T := phaseTable Q L) (fun g hg => thread_sound hp hg) hX
    (S := fun g => g < L.threads) _ _ hg (Execution.isBarId 1)
    (P := fun d n => n = publication d) _ _ k _ nu hs
  · exact ⟨fun _ _ _ _ _ _ _ _ _ _ hc fire _ => Lib.barOne_fires hp.block hc fire⟩
  · exact fun g hg k => ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  · exact (enter_phase ..).symm
  · intro d e dn n _ _ hit prev step _
    rw [phase_next step,←prev]
    change Execution.isBarId 1 e = decide _ at hit
    simp [hit]

end
end PTX.Kernels.InklingRelDecode.Proof
