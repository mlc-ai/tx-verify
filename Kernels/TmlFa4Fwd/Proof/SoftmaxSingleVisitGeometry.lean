-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstGeometryReads
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

/-- The computed addresses and predicates still needed after the three request length reads. -/
def singleVisitGeometryCarry (l : Launch) (g : Nat) (warp : Fin 8) : List (Nat × Value) :=
  let stage := stageOf warp
  [(2771, b32 (waitLoc l g stage 2).addr), (2789, b32 (scoreAddress l g stage 2)),
    (5127, b32 (3 + warp.val))] ++
    (List.finRange 16).map
      (fun i => ((biasReadSite false i).base, b32 (biasVectorBase l g stage false i))) ++
    biasFenceFacts l g warp false

theorem singleVisitGeometryCarryRegs (l : Launch) (g : Nat) (warp : Fin 8) :
    ∀ x ∈ singleVisitGeometryCarry l g warp, x.1 ∈ firstGeometryCarryRegs := by
  have hRegs :
      ((singleVisitGeometryCarry l g warp).map Prod.fst).all
        (fun r => firstGeometryCarryRegs.contains r) = true := rfl
  intro x hx
  have h := List.all_eq_true.mp hRegs x.1 (List.mem_map_of_mem hx)
  simpa only [List.contains_eq_mem, decide_eq_true_eq] using h

/-- The real request length loads and correction acknowledgement produce the complete
single-visit round frame, while the earlier address arithmetic supplies its stable inputs. -/
theorem singleVisitGeometryReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (warp : Fin 8) {g j batch tile : Nat} (hb : batch < p.batch)
    (hTile : 256 * tile < p.qLength batch) (hTrip : Mma.trips p batch tile = 1)
    {t : TState}
    (ht : At t 3367 (firstGeometryAddressInput p l g batch tile (stageOf warp) ++
      singleVisitGeometryCarry l g warp))
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ fails u, FirstGeometryReads p X g j batch ∧
      At u 3425 (singleVisitRoundFacts p l g warp batch tile
        (1 - stageGeometryBlocks p batch tile (stageOf warp) + 10)
        (p.kLength batch - p.qLength batch + 256 * tile)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 3 + fails + 1)) none := by
  let stage := stageOf warp
  have hCuQ off (ho : off ≤ 1) k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + off))).at k) :=
    hp.inputByte_unwritten writes (region := ⟨p.cuQBase, 4 * (p.batch + 1)⟩)
      (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  have hUsedK k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k) :=
    hp.inputByte_unwritten writes (region := ⟨p.usedKBase, 4 * p.batch⟩)
      (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  obtain ⟨fails, u, hReads, _, hu, hRun⟩ := firstGeometryReadyTraceFramed hp hX stage hb hTile
    (singleVisitGeometryCarryRegs l g warp) ht hCuQ hUsedK hr
  refine ⟨fails, u, hReads, hu.mono ?_, hRun⟩
  have hCarry := (holds_append ..).mp hu.2.2.2.2 |>.2
  have hParts := (holds_append ..).mp hCarry
  have hBases := (holds_append ..).mp hParts.1 |>.2
  have hPast : p.kLength batch - p.qLength batch + 256 * tile + 256 =
      p.kLength batch - p.qLength batch + 256 * (tile + 1) := by omega
  simp only [singleVisitRoundFacts, firstLoopGeometry, holds_append, holds_cons, holds_nil]
  repeat' first | exact hBases | exact hParts.2 | apply And.intro
  all_goals first
    | trivial
    | exact holds_mem hu.2.2.2.2 (by
        simp [firstGeometryAckFacts, firstGeometryFacts, singleVisitGeometryCarry, stage,
          hTrip, hPast])

end PTX.Kernels.TmlFa4Fwd.Softmax
