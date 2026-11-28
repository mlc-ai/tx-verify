-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.Where

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

private theorem halfRange : BarRow.halfZeroSites.all (fun p =>
    (27<p && p<574) || (574<p && p<2331)) = true := by decide

/-- A half-CTA rendezvous follows at most two barrier-1 events of its thread. -/
theorem half_publication {Q L m X g k pc md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k) = some ⟨pc,.bar 0 (some 128) md⟩) :
    ((X.tr g).take k).countP (Execution.isBarId 1) ≤ 2 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, r⟩ := Lib.recorded_bar hX hp.block he
  have site : pc ∈ BarRow.halfZeroSites := by
    rcases r with ⟨h, -⟩ | ⟨-, e, -⟩ | ⟨-, -, s⟩
    · exact absurd h (by decide)
    · cases e
    · exact s
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have p := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change pc = _ at p
  rw [publication_prefix hp hX hg (Frame.noUbBefore_of_get hX he) hs]
  have range := List.all_eq_true.mp halfRange pc site
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
  rcases range with pro|soft
  · obtain ⟨_,_,_,rfl⟩ := (p ▸ state_role s).prologue pro.1 pro.2
    change Prologue.publicationPhase _ ≤ 2
    unfold Prologue.publicationPhase
    split <;> omega
  · obtain ⟨_,_,_,_,rfl⟩ := (p ▸ state_role s).softmax soft.1 soft.2
    change Softmax.publicationPhase _ ≤ 2
    unfold Softmax.publicationPhase
    split <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Export
