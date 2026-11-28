-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.BarOne
public import Kernels.InklingRelDecode.Spec
import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
import Kernels.InklingRelDecode.Proof.Common.LaunchLane

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Frame

/-- Publication generations observed in data warps. The terminal arrival
at 2849 publishes the exit role word, and no fifth arrival is possible. -/
theorem data_sync {Q L m X g k pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.bar 1 none .sync⟩)
    (low : g%L.block<128) :
    (pc,((X.tr g).take k).countP (Execution.isBarId 1)) ∈ [(573,0),(575,1),(2846,2),(2849,3)] := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_,one|bad|bad⟩ := Lib.recorded_bar hX hp.block he
  all_goals try cases bad.1
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have p := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change pc=_ at p
  rw [publication_prefix hp hX hg (Frame.noUbBefore_of_get hX he) hs]
  have hit := one.2.2
  rw [p] at hit ⊢
  obtain ⟨s,n⟩ := s
  rcases s with s|⟨r,d⟩
  · change s.site.pc ∈ Lib.barOneSites at hit
    have miss (s : Startup.Site) : s.pc ∉ Lib.barOneSites := by
      cases s <;> first | decide | (rename_i r; cases r <;> decide)
    exact (miss _ hit).elim
  · rcases r with r|r
    · cases r with
      | dispatch w x =>
        have upper := (worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs).1
        change 128≤g%L.block at upper
        omega
      | prologue w =>
        rcases d with d|⟨_,d|⟨_,d⟩⟩
        · change d.site.pc ∈ Lib.barOneSites at hit
          change (d.site.pc,Prologue.publicationPhase d.site) ∈ _
          generalize d.site=s at hit ⊢
          revert hit
          cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
        · change d.site.pc ∈ Lib.barOneSites at hit
          change (d.site.pc,Softmax.publicationPhase d.site) ∈ _
          generalize d.site=s at hit ⊢
          revert hit
          cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
        · change d.site.pc ∈ Lib.barOneSites at hit
          change (d.site.pc,Epilogue.publicationPhase d.site) ∈ _
          generalize d.site=s at hit ⊢
          revert hit
          cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    · change r.pc ∈ Lib.barOneSites at hit
      cases r <;> contradiction

theorem first_data_sync {Q L m X g k pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.bar 1 none .sync⟩)
    (low : g%L.block<128) (ord : ((X.tr g).take k).countP (Execution.isBarId 1)=0) : pc=573 := by
  simpa [ord] using data_sync hp hX he low

end PTX.Kernels.InklingRelDecode.Proof.Export
