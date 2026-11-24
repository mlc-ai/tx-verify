-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainPollAgreement
import Kernels.TmlFa4Fwd.Proof.Progress.FirstCacheAcquire
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Lemmas.Flow.PollSynced
import Lemmas.Execution.ExecutionGrowth

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof Prologue Epilogue

noncomputable section

private theorem drainLoaderWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) (hSite : e.pc ∈ [1866,1877,1888]) :
    14 ≤ warpIndex l g := by
  have hRange := (by decide :
    ∀ pc ∈ [1866,1877,1888], 173 < pc ∧ 1866 ≤ pc ∧ pc < 1901 ∧
      pc ∉ registerHintSites) e.pc hSite
  have hRole := roleBodyPcOfEvent hp hX he hRange.1 hRange.2.2.2
  unfold roleBodyPc at hRole
  rcases hRole with hExit | hRole
  · omega
  · split_ifs at hRole <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y) {g h i j site : Nat}
    (hWarp : SameWarp l g h) {a b : Loc} {parity parity' : Nat} {ok ok' acq acq' : Bool}
    {scope scope' : MbarScope} (he : X.get (g,i) = some ⟨site,.wait a parity ok acq scope⟩)
    (hf : X.get (h,j) = some ⟨site,.wait b parity' ok' acq' scope'⟩)
include hp hX hFrame hComplete hWarp he hf

/-- Two same-warp loader lanes at one final cache drain wait use the same object.
The selected CTA has the same exact number of K/V ring uses in every lane. -/
theorem drainPollObjectsAgree (hSite : site ∈ [1866,1877,1888]) : a = b := by
  obtain ⟨Y,hY,hPrefix,hLargest⟩ := bounded_largest_extension (terminates hp) hX
  have hMax : Maximal l kernel Assumptions.all m Y :=
    ⟨hY,fun Z hZ hExt => hLargest Z hZ (Execution.le_trans hPrefix hExt)⟩
  have hDone := hComplete Y hMax
  have hYFrame := hFrame Y hY
  have hCuQ := hp.cuQ_protected (X := Y) (fun _ _ _ _ => loaderOutputWrites hYFrame)
  have hg := hWarp.1.1
  have hw := drainLoaderWarp hp hX he hSite
  have hSlot := (by decide :
    ∀ pc ∈ [1866,1877,1888], ∃ slot : Fin 3, pc = drainCacheSite slot) site hSite
  obtain ⟨slot,rfl⟩ := hSlot
  have hSelf : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hgLane := Step.warpLane_of_sameWarp hSelf
  have hhLane := Step.warpLane_of_sameWarp hWarp
  have hgIndex : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hhIndex : laneOf l h < 32 := Nat.mod_lt _ (by decide)
  have heY := Execution.le_get hPrefix he
  have hfY := Execution.le_get hPrefix hf
  rw [← hgLane] at heY
  rw [← hhLane] at hfY
  by_cases hActive : g / l.block < tilePrefix p p.batch * p.heads
  · obtain ⟨batch,⟨hb,hLo,hHi⟩,_⟩ := tileBatch_existsUnique p hActive
    have hPublication := Progress.selectedCacheKeyPacketDeliveredOfMaximal hp hMax hYFrame
      hg hw hb hLo hHi
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    have laneExit (lane : Nat) (hl : lane < 32) : Thread.Exited Y (warpLane l g lane) := by
      have hLive := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
      obtain ⟨site,he⟩ := (hDone.1 (warpLane l g lane) hLive).resolve_left (noCanceled hY)
      obtain ⟨index,hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_getLast? he)
      exact ⟨index,⟨site,.exit⟩,hi,rfl⟩
    obtain ⟨ip,hi,_,_⟩ := hPublication (laneOf l g) hgIndex
    obtain ⟨jp,hj,_,_⟩ := hPublication (laneOf l h) hhIndex
    have ha := selectedDrainPollObject hp hY hYFrame hg hw hgIndex hb hLo hHi hi
      (laneExit _ hgIndex) slot heY
    have hb := selectedDrainPollObject hp hY hYFrame hg hw hhIndex hb hLo hHi hj
      (laneExit _ hhIndex) slot hfY
    rw [hgLane] at ha
    rw [hhLane] at hb
    exact ha.trans (by simpa only [emptyObject,hWarp.1.2.2] using hb.symm)
  · have ha := idleDrainPollObject hp hMax hDone hg hw hCuQ (Nat.le_of_not_lt hActive)
      hgIndex slot heY
    have hb := idleDrainPollObject hp hMax hDone hg hw hCuQ (Nat.le_of_not_lt hActive)
      hhIndex slot hfY
    rw [hgLane] at ha
    rw [hhLane] at hb
    exact ha.trans (by simpa only [emptyObject,hWarp.1.2.2] using hb.symm)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
