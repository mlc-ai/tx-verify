-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderActiveReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- Positions and contents of the requests' three loader metadata reads. -/
def activeMetadataEvents (p : Params) (batch : Nat) : List Event :=
  [⟨381, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
      ((b32 (p.qOffset batch)).toBytes.map some)⟩,
   ⟨382, .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
      ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩,
   ⟨385, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
      ((b32 (p.kLength batch)).toBytes.map some)⟩]

def activeMetadataFacts (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  [(1086, b32 (p.kLength batch)), (1799, b32 (p.qOffset batch)),
   (1800, b32 (p.qOffset (batch + 1)))] ++ loaderActiveLaneFacts p l g batch lane

/-- The actual metadata reads advance each lane by three events and preserve its ordinals. -/
theorem loaderActiveWarpReads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    {g batch shuffles votes : Nat} (hb : batch < p.batch)
    (cur : SchedulerWarpAt l X g 381 (loaderActiveLaneFacts p l g batch) shuffles votes) :
    ∃ next : SchedulerWarpAt l X g 386 (activeMetadataFacts p l g batch) shuffles votes,
      (∀ lane, next.pos lane = cur.pos lane + 3) ∧
      ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) =
        activeMetadataEvents p batch ++ (X.tr (warpLane l g lane)).drop (next.pos lane) := by
  let thread := warpLane l g
  have hLanes : ∀ lane < 32, ∃ u,
      (X.tr (thread lane)).drop (cur.pos lane) =
        activeMetadataEvents p batch ++ (X.tr (thread lane)).drop (cur.pos lane + 3) ∧
      Run kernel Assumptions.all l (thread lane) u
        ((X.tr (thread lane)).drop (cur.pos lane + 3)) none ∧
      At u 386 (activeMetadataFacts p l g batch lane) := by
    intro lane hl
    obtain ⟨u, h₀, h₁, h₂, hu, hr⟩ := loaderActiveReadWords hp hX writes hb
      (cur.checkpoint lane hl)
      ((cur.continuation lane hl).after_local (cur.localSteps lane hl))
    refine ⟨u, ?_, hr, hu⟩
    have hx := List.getElem?_eq_some_iff.mp h₀
    have hy := List.getElem?_eq_some_iff.mp h₁
    have hz := List.getElem?_eq_some_iff.mp h₂
    rw [List.drop_eq_getElem_cons hx.1, hx.2, List.drop_eq_getElem_cons hy.1, hy.2,
      List.drop_eq_getElem_cons hz.1, hz.2]
    rfl
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! u hTrace hRun hAt using hLanes
  have hCounts := cur.ordinals.advance (fun _ => activeMetadataEvents p batch)
    (fun lane hl => ⟨_, hTrace lane hl⟩) (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨fun lane => cur.pos lane + 3, u, u, hCounts, hRun, fun _ _ => .refl, hAt⟩,
    fun _ => rfl, hTrace⟩

/-- Every active loader warp reaches the same selected request in all its lanes. It
performs the actual three metadata reads and retains their decoded values at PC 386. -/
theorem loaderActiveProgram {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (hActive : g / l.block < tilePrefix p p.batch * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) :
    ∃ batch shuffles, batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ cur : SchedulerWarpAt l X g 386 (activeMetadataFacts p l g batch) shuffles 1,
        ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane - 3) =
          activeMetadataEvents p batch ++ (X.tr (warpLane l g lane)).drop (cur.pos lane) := by
  rcases loaderSchedule hp hX hComplete hg hWarp writes with
    ⟨hBad, _⟩ | ⟨first, batch, shuffles, hf, hGroup, hb, hLo, hHi, ⟨selected⟩⟩
  · omega
  obtain ⟨prep⟩ := loaderSelectedPrefix hp hX hg hf hGroup hb selected
  obtain ⟨coords⟩ := loaderSelectedCoordinates hp hX hg hf hGroup hb hLo hHi prep
  obtain ⟨ready⟩ := loaderActiveWarpEntry hp hb hLo hHi coords
  obtain ⟨cur, hPos, hRead⟩ := loaderActiveWarpReads hp hX writes hb ready
  refine ⟨batch, _, hb, hLo, hHi, cur, ?_⟩
  intro lane hl
  rw [show cur.pos lane - 3 = ready.pos lane by rw [hPos]; omega]
  exact hRead lane hl

end
end PTX.Kernels.TmlFa4Fwd.Loader
