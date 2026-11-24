-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinates
public import Kernels.TmlFa4Fwd.Proof.SchedulerFrame
public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionReads
public import Lemmas.Register.RegisterFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The startup registers needed again at writeback or at the drain scan. -/
def schedulerFrameRegs : List Nat :=
  [2535, 1178, 2390, 6497, 7290, 7502, 7506, 1072, 1062, 1201, 268, 7138]

private theorem coordinateFrameCode :
    ((kernel.code.drop 2899).take 50).all
      (fun ins => schedulerFrameRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem coordinateStraightCode :
    ((kernel.code.drop 2899).take 49).all (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The actual coordinate steps preserve every startup register needed after tile selection. -/
theorem coordinateRunFrame {l : Launch} {g n : Nat} {t u : TState}
    (hRun : run kernel [] l g n t = some u) (hLo : 2899 ≤ t.pc)
    (hHi : t.pc + n ≤ 2949) {r : Nat} (hr : r ∈ schedulerFrameRegs) : u.regs r = t.regs r :=
  schedulerLocalFrame coordinateFrameCode coordinateStraightCode hRun hLo hHi hr

/-- Replay the coordinate calculation under a model that agrees through the tile guard. -/
theorem coordinateRunTransport {A : List Assumption} {l : Launch} {g : Nat} {t u : TState}
    (hModel : ∀ {s : TState}, 2899 ≤ s.pc → s.pc < 2949 →
      out kernel A l g s = out kernel [] l g s)
    (hRun : run kernel [] l g 50 t = some u) (hPc : t.pc = 2899) :
    run kernel A l g 50 t = some u :=
  schedulerLocalTransport (lo := 2899) (len := 50) coordinateStraightCode hModel hRun
    (by rw [hPc]) (by rw [hPc])

/-- The selected tile coordinates and the startup operands coexist in the resulting state. -/
theorem computeSelectedTileFramed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch item start previous : Nat} {F : List (Nat × Value)}
    (hBatch : batch < p.batch) (hPrefix : start + previous = tilePrefix p batch * p.heads)
    (hLo : tilePrefix p batch * p.heads ≤ item)
    (hHi : item < tilePrefix p (batch + 1) * p.heads)
    (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) :
    let pos := assignedCoordinates p batch item
    Seg kernel [] l g 50 2899
      ([(1207, b32 start), (7225, b32 previous), (1072, b32 item),
        (2355, b32 (requestTiles p batch)), (7138, b32 p.heads), (7155, b32 800),
        (7146, b32 p.batch), (7228, b32 batch)] ++ F) 2949
      ([(7228, b32 batch), (7227, b32 pos.2), (7226, b32 (2 ^ 30 + 256 * pos.1))] ++ F) := by
  dsimp only
  intro t hAt
  obtain ⟨hArgs, hFrame⟩ := (holds_append ..).mp hAt.2.2.2.2
  obtain ⟨u, hu, huAt⟩ :=
    computeSelectedTile hp g hBatch hPrefix hLo hHi t (hAt.mono hArgs)
  have hKeep := holdsSchedulerFrame hFrame
    (fun _ hr => coordinateRunFrame hu (by rw [hAt.1]) (by rw [hAt.1]) hr) hF
  exact ⟨u, hu, huAt.mono ((holds_append ..).mpr ⟨huAt.2.2.2.2, hKeep⟩)⟩

/-- The actual selected request path computes the scheduler coordinates, reads its two cuQ
endpoints and reaches the exact ready-poll PC with the writeback and rescan operands. -/
theorem selectedCoordinatesToReady {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {t : TState} {batch item start previous lane : Nat} {F : List (Nat × Value)}
    (hBatch : batch < p.batch) (hPrefix : start + previous = tilePrefix p batch * p.heads)
    (hLo : tilePrefix p batch * p.heads ≤ item) (hHi : item < tilePrefix p (batch + 1) * p.heads)
    (hLane : lane < 32) (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs)
    (hLaneFact : (1201, b32 lane) ∈ F) (hCuQFact : (7502, b64 p.cuQBase) ∈ F)
    (ht : At t 2899
      ([(1207, b32 start), (7225, b32 previous), (1072, b32 item),
        (2355, b32 (requestTiles p batch)), (7138, b32 p.heads), (7155, b32 800),
        (7146, b32 p.batch), (7228, b32 batch)] ++ F)) :
    let pos := assignedCoordinates p batch item
    ∃ u v w z, run kernel [] l g 54 t = some u ∧
      EStep kernel [] l g u
        ⟨2953, .rd { loc := globalLoc (p.cuQBase + 4 * batch), size := 4 }
          ((b32 (p.qOffset batch)).toBytes.map some)⟩ (some v) ∧
      EStep kernel [] l g v
        ⟨2954, .rd { loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4 }
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ (some w) ∧
      w.pc = 2955 ∧ run kernel [] l g 3 w = some z ∧
      At z 2958 ([(7229, b32 0), (2395, b32 (2 ^ 30 - p.qLength batch + 256 * pos.1)),
        (2393, b32 (p.qOffset (batch + 1))), (307, .pred (decide (p.batch < lane))),
        (7147, b32 p.batch), (7228, b32 batch), (7227, b32 pos.2),
        (7226, b32 (2 ^ 30 + 256 * pos.1))] ++ F) := by
  dsimp only
  obtain ⟨s, hs, hS⟩ := computeSelectedTileFramed hp g hBatch hPrefix hLo hHi hF t ht
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hDisjoint : schedulerFrameRegs.all (fun r => !selectScratch.contains r) = true := rfl
  have hClean : ∀ pair ∈
      [(7228, b32 batch), (7227, b32 (assignedCoordinates p batch item).2),
        (7226, b32 (2 ^ 30 + 256 * (assignedCoordinates p batch item).1))] ++ F,
      pair.1 ∉ selectScratch := by
    intro pair hm
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | hm <;> first
      | exact of_decide_eq_true rfl
      | simpa using List.all_eq_true.mp hDisjoint _ (hF pair hm)
  obtain ⟨u, v, w, z, hu, hv, hw, hPc, hz, hZ⟩ :=
    selectedTileToReady hp g hBatch hTile hLane hS hClean
      (List.mem_append.mpr (.inr hLaneFact)) (by simp)
      (List.mem_append.mpr (.inr hCuQFact)) (by simp)
  exact ⟨u, v, w, z, run_comp hs hu, hv, hw, hPc, hz, hZ⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
