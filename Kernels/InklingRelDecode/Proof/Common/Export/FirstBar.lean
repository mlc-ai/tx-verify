-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.TableU
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

private theorem startup_clear (s : Startup.Site) : s.pc ∉ Lib.barOneSites := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem prologue_hit (s : Prologue.Site) (hit : s.pc ∈ Lib.barOneSites) : s.pc=573 := by
  revert hit
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem soft_late (s : Softmax.Site) : 1 ≤ Softmax.publicationPhase s := by
  cases s <;> simp [Softmax.publicationPhase]

private theorem epilogue_late (s : Epilogue.Site) : 1 ≤ Epilogue.publicationPhase s := by
  unfold Epilogue.publicationPhase
  split <;> omega

/-- A default-partition lane's barrier-one rendezvous before any other is the prologue's
releasing barrier. -/
theorem first_barrier_pc {Q L m X g k pc cnt mode} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.bar 1 cnt mode⟩)
    (zero : ((X.tr g).take k).countP (Execution.isBarId 1)=0) (lane : g%L.block<128) : pc=573 := by
  have hg := Frame.lt_of_get hX he
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have at_pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  have phase := publication_prefix hp hX hg (Frame.noUbBefore_of_get hX he) hs
  rw [zero] at phase
  obtain ⟨t,ins,o,_,code,fire⟩ : ∃ t ins o, _ ∧ kernel.code[pc]?=some ins ∧
      Fires pc (eventTmpl Assumptions.all L g t ins.op) ⟨pc,.bar 1 cnt mode⟩ o := by
    obtain ⟨_,bad⟩|⟨t,ins,o,ht,code,fire⟩ := get_source hX he
    · cases bad
    exact ⟨t,ins,o,ht,code,fire⟩
  have hit : pc ∈ Lib.barOneSites := of_decide_eq_true (Lib.barOne_fires hp.block code fire).symm
  have pcs : (thread Q L g).pc s=pc := at_pc.symm
  rw [←pcs] at hit
  rw [←pcs]
  obtain ⟨s,n⟩ := s
  rcases s with s | ⟨r,s⟩
  · exact (startup_clear _ hit).elim
  · rcases r with r | r
    · cases r with
      | dispatch w x =>
        obtain ⟨wide,_⟩ := worker_warp hp hX hk hs
        omega
      | prologue w =>
        rcases s with s | ⟨ent,s | ⟨_,s⟩⟩
        · have := prologue_hit s.site hit
          exact this
        · have := soft_late s.site
          change 0 = Softmax.publicationPhase s.site at phase
          omega
        · have := epilogue_late s.site
          change 0 = Epilogue.publicationPhase s.site at phase
          omega
    · have clear : Startup.Entry.pc r ∉ Lib.barOneSites := by cases r <;> decide
      exact absurd hit clear

end PTX.Kernels.InklingRelDecode.Proof.Export
