-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSurfaceProgress
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFinalTensorRanks
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Epilogue Prologue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hOutputs : OutputFootprint p X)
include hp hMax hOutputs

/-- After the rescale loop all warp peers load, wait and stage the same chunk.
The recorded store callbacks preserve every lane's next surface cursor. -/
theorem surfaceWarpStepAfterRescale (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {lead : Nat} (hRole : 8 ≤ warpIndex l lead ∧ warpIndex l lead < 12) (stage : Fin 2)
    (chunk : Fin 16) (reciprocal : Nat → ℝ) {F : Nat → List (Nat × Value)}
    (hFrame : ∀ g, SameWarp l lead g → FinalizeSurfaceRegisters l g stage (reciprocal g) (F g))
    (c : ∀ g, SameWarp l lead g → OpeningTripCursor l X g
      (finalizeSurfacePc stage chunk.val) (finalizeSurfaceFrame l g stage chunk.val (F g))) :
    ∀ g (hw : SameWarp l lead g),
      ∃ d : OpeningTripCursor l X g (finalizeSurfacePc stage (chunk.val+1))
          (finalizeSurfaceFrame l g stage (chunk.val+1) (F g)),
        d.pos = (c g hw).pos+10 ∧ d.ending = (c g hw).ending := by
  classical
  have hCuQ := (hOutputs.metadataProtected hp).1
  have hGuard := Progress.syncGuarded hp hMax.1 hCuQ
  have hLayout := Mma.actualMmaLayoutInjective hMax.1
  let rank := Thread.correctionFinalTensorBase X lead+(32*stage.val+2*chunk.val)
  have hLoad (g : Nat) (hw : SameWarp l lead g) :=
    surfaceLoadOfMaximal hp hMax hGuard hLayout hw.1.2.1 stage chunk (reciprocal g)
      (hFrame g hw) (c g hw)
  let ld (g : Nat) (hw : SameWarp l lead g) := Classical.choose (hLoad g hw)
  have hRoleOf (g : Nat) (hw : SameWarp l lead g) :
      8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    have hEq : warpIndex l lead = warpIndex l g := hw.2
    exact hEq ▸ hRole
  have hPeerWarp (g : Nat) (hw : SameWarp l lead g) {peer : Nat}
      (hPeer : peer ∈ warpLanes l g) : SameWarp l lead peer := by
    obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hPeer
    have hl := (List.mem_range.mp hLane).trans_le (min_le_left _ _)
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    exact Step.sameWarp_trans hw (Step.sameWarp_lane hBlock hw.1.2.1 hl).1
  have hLoadRank (g : Nat) (hw : SameWarp l lead g) : X.TcK (g,(ld g hw).cursor.pos) rank := by
    have self : SameWarp l lead lead := ⟨⟨hw.1.1,hw.1.1,rfl⟩,rfl⟩
    have same := Thread.finalLoadBasesAgree hp hMax.1 hOutputs hw hRole.1 hRole.2 stage chunk
      (ld lead self).load (ld g hw).load
    dsimp only [rank]
    rw [same]
    exact Thread.finalLoadRankOfRescales hp hMax.1 hOutputs (hRoleOf g hw).1
      (hRoleOf g hw).2 stage chunk (ld g hw).load
  have hLoadPeers (g : Nat) (hw : SameWarp l lead g) :
      ∀ peer ∈ warpLanes l g, ∃ k, X.TcK (peer,k) rank := by
    intro peer hPeer
    exact ⟨_,hLoadRank peer (hPeerWarp g hw hPeer)⟩
  let prod (g : Nat) (hw : SameWarp l lead g) := Classical.choice
    ((ld g hw).productsOfMaximal hp hMax hCuQ hValues hw.1.2.1 (hFrame g hw)
      (Step.releasedOfTcOrdinal (ld g hw).load rfl (hLoadRank g hw).2 (hLoadPeers g hw)))
  have hWaitRank (g : Nat) (hw : SameWarp l lead g) :
      X.TcK (g,(ld g hw).cursor.pos+1) (rank+1) := by
    exact ⟨⟨_,(prod g hw).wait,rfl⟩,(countP_take_succ (p := isTcColl) (ld g hw).load rfl).trans
      (congrArg (·+1) (hLoadRank g hw).2)⟩
  have hWaitPeers (g : Nat) (hw : SameWarp l lead g) :
      ∀ peer ∈ warpLanes l g, ∃ k, X.TcK (peer,k) (rank+1) := by
    intro peer hPeer
    exact ⟨_,hWaitRank peer (hPeerWarp g hw hPeer)⟩
  intro g hw
  have hRelease : (ld g hw).cursor.pos+2 = (X.tr g).length → Step.Released l X g := by
    simpa only [Nat.add_assoc] using Step.releasedOfTcOrdinal (prod g hw).wait rfl
      (hWaitRank g hw).2 (hWaitPeers g hw)
  obtain ⟨d,hPos,hEnd⟩ := (ld g hw).writesOfMaximal hp hMax hw.1.2.1 (hRoleOf g hw).2
    (prod g hw) hRelease
  have hSaved := Classical.choose_spec (hLoad g hw)
  exact ⟨d,hPos.trans (congrArg (·+10) hSaved.1),hEnd.trans hSaved.2⟩

/-- Iterate the live chunk transitions through the final accumulator tile. -/
theorem surfaceWarpThroughAfterRescale (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {lead : Nat} (hRole : 8 ≤ warpIndex l lead ∧ warpIndex l lead < 12) (stage : Fin 2)
    (reciprocal : Nat → ℝ) {F : Nat → List (Nat × Value)}
    (hFrame : ∀ g, SameWarp l lead g → FinalizeSurfaceRegisters l g stage (reciprocal g) (F g))
    (start : Nat)
    (c : ∀ g, SameWarp l lead g → OpeningTripCursor l X g
      (finalizeSurfacePc stage start) (finalizeSurfaceFrame l g stage start (F g))) (n : Nat)
    (hn : start+n ≤ 16) :
    ∀ g (hw : SameWarp l lead g),
      ∃ d : OpeningTripCursor l X g (finalizeSurfacePc stage (start+n))
          (finalizeSurfaceFrame l g stage (start+n) (F g)),
        d.pos = (c g hw).pos+10*n ∧ d.ending = (c g hw).ending := by
  induction n with
  | zero =>
    intro g hw
    exact ⟨c g hw,by simp,rfl⟩
  | succ n ih =>
    have h := ih (by omega)
    let chunk : Fin 16 := ⟨start+n,by omega⟩
    let prev (g : Nat) (hw : SameWarp l lead g) := Classical.choose (h g hw)
    intro g hw
    obtain ⟨d,hPos,hEnd⟩ := surfaceWarpStepAfterRescale hp hMax hOutputs hValues hRole
      stage chunk reciprocal hFrame prev g hw
    have hPrev := Classical.choose_spec (h g hw)
    refine ⟨d,?_,hEnd.trans hPrev.2⟩
    have hPrevPos : (prev g hw).pos = (c g hw).pos+10*n := hPrev.1
    omega

end PTX.Kernels.TmlFa4Fwd.Correction
