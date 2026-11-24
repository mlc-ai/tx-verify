-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyObservedGate
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringIndexSeed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g lane j batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1) {e : Event}
include hp hX hg hw hl writes hCTA hb hLo hHi hMany

set_option maxRecDepth 100000 in
/-- After the nine warm visits, the actual steady lane retains its launch frame
and starts with iteration nine. -/
theorem steadyFirstArmOfDemand (he : X.get (warpLane l g lane, j) = some e) (hFloor : 917 ≤ e.pc)
    (hDemand' : 1386 ≤ e.pc ∨ (Execution.isShfl e = true ∧
      primingSearchShuffleCount batch + 640 <
        ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl)) (hSafe : ∀ f, e.kind ≠ .ub f)
    :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    ∃ pos ≤ j, ∃ s ending,
      At s 1386 ([(7181, b32 9), (1116, b32 (trips - 2))] ++
        warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
      ((X.tr thread).take pos).countP Execution.isShfl = primingSearchShuffleCount batch + 640 := by
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let F := (1116, b32 (trips - 2)) :: warmStartFrame p l batch
    (co.2 / 6) trips (warpIndex l g) tid
  let G := [(7174, b32 8), (1091, b32 (trips - 1))] ++ F
  change 11 ≤ trips at hMany
  have hMin : min (trips - 1) 9 = 9 := by omega
  have hWarm : 8 < min (trips - 1) 9 := by omega
  have hDemand : WarmRoundDemand p l X g lane batch 8 j e :=
    ⟨.inl hWarm, hDemand'.imp (by omega) (fun h => by have := h.2; omega)⟩
  obtain ⟨_, _, hTileBound, index, hOrder, s, ending, hs, hr, hsRank⟩ :=
    warmRoundEntryOfEvent hp hX hg hw hl writes hCTA hb hLo hHi he hFloor hSafe hDemand
  have hFit : trips - 1 < 2 ^ 31 := by
    change 128 * (trips - 2) + 127 < 2 ^ 31 at hTileBound
    omega
  have hs' : At s 917 G := hs.mono
    ⟨hs.2.2.2.2.1, holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2.2⟩
  have hAudit (n : Nat) : ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n (G.map Prod.fst) ins.op) = true := by kernel_rfl
  obtain ⟨seed, hSeedBefore, u, stop, hU, huRun, huRank⟩ :=
    warmObservedAdvance hFit hWarm hAudit (by kernel_rfl) hs' hr he hOrder
      hSafe (hDemand'.imp (by omega) (fun h => by rw [hsRank]; exact h.2))
  have huAt : At u 1353 ((1091, b32 (trips - 1)) :: F) := by
    have hTrue := hU.mono hU.2.2.2.2.2
    rw [hMin] at hTrue
    exact hTrue
  obtain ⟨pos, hBefore, w, stop', hwAt, hwRun, hwRank⟩ :=
    steadyGateFromSeedDemand hFit (by kernel_rfl) (fun _ => by kernel_rfl)
      (by kernel_rfl) (by kernel_rfl) huAt huRun he hSeedBefore
      (hDemand'.imp (by omega) And.left) hSafe
  have hAdvance : min (trips - 1) 9 < trips - 1 := by omega
  refine ⟨pos, hBefore, w, stop', ?_, hwRun, ?_⟩
  · rw [ite_eq_left hAdvance] at hwAt
    refine hwAt.mono ?_
    rw [← hMin]
    exact ⟨hwAt.2.2.2.2.1, hwAt.2.2.2.2.2.2⟩
  · rw [hwRank, huRank, hsRank]


set_option maxRecDepth 100000 in
/-- After the nine warm visits, the actual steady lane retains its launch frame
and starts with iteration nine. -/
theorem steadyFirstArmOfEvent (he : X.get (warpLane l g lane, j) = some e) (hPc : 1386 ≤ e.pc)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    ∃ pos ≤ j, ∃ s ending,
      At s 1386 ([(7181, b32 9), (1116, b32 (trips - 2))] ++
        warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
      ((X.tr thread).take pos).countP Execution.isShfl = primingSearchShuffleCount batch + 640 := by
  exact steadyFirstArmOfDemand hp hX hg hw hl writes hCTA hb hLo hHi hMany he
    (by omega) (.inl hPc) hSafe

end
end PTX.Kernels.TmlFa4Fwd.Loader
