-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKMetadata

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- The first two metadata iterations carry the pointer-preparation registers unchanged. -/
def primingKInitialScratchFacts (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    List (Nat × Value) :=
  primingScratchFacts p l batch (primingLaneRow tile (32 * warp + lane)) 0 ++
    primingKPackFrame p l batch head tile warp lane

/-- The priming packet ABI is unchanged across either scratch iteration. -/
theorem primingKFrameScratch (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    PrimingScratchExtra (primingKPackFrame p l batch head tile warp lane) := by
  constructor
  · constructor
    · set_option maxRecDepth 100000 in kernel_rfl
    · simp [primingKPackFrame, primingKMaskInputs]
    · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

/-- The copy preparation frame survives the initial K acquire. -/
theorem primingKFrameWait (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    PrimingKWaitExtra (primingKPackFrame p l batch head tile warp lane) := by
  constructor
  · set_option maxRecDepth 100000 in kernel_rfl
  · simp [primingKPackFrame, primingKMaskInputs]

private theorem primingKPrepNoCollectives (p : Params) (l : Launch) (g batch base n : Nat) :
    let es := primingScratchEvents p l g batch base 0 ++
      primingScratchEvents p l g batch base 1 ++
      List.replicate n (primingKWaitEvent l g false) ++ [primingKWaitEvent l g true]
    es.countP Execution.isShfl = 0 ∧ es.countP isFullWarpVote = 0 := by
  dsimp only
  simp only [primingScratchEvents, List.countP_append, List.countP_replicate]
  change _ + _ + (if false then n else 0) + 0 = 0 ∧
    _ + _ + (if false then n else 0) + 0 = 0
  by_cases h0 : base < p.kLength batch <;>
    by_cases h1 : base + 64 < p.kLength batch <;>
      simp [h0, h1, Execution.isShfl, isWarpVote, voteClass]

/-- The scratch initialization and successful acquire precede preparation of the row pointers. -/
def primingKPrepEvents (p : Params) (l : Launch) (g batch base n : Nat) : List Event :=
  primingScratchEvents p l g batch base 0 ++ primingScratchEvents p l g batch base 1 ++
    List.replicate n (primingKWaitEvent l g false) ++ [primingKWaitEvent l g true]

theorem primingKPrepEvents_noShuffle (p : Params) (l : Launch) (g batch base n : Nat) :
    (primingKPrepEvents p l g batch base n).countP Execution.isShfl = 0 :=
  (primingKPrepNoCollectives p l g batch base n).1

theorem primingKPrepEvents_before (p : Params) (l : Launch) (g batch base n : Nat)
    {e : Event} (he : e ∈ primingKPrepEvents p l g batch base n) :
    e.pc ≤ 517 := by
  simp only [primingKPrepEvents, List.mem_append, List.mem_replicate, List.mem_singleton] at he
  rcases he with ((h | h) | ⟨_, rfl⟩) | rfl
  · exact (primingScratchEvents_before e h).trans (by decide)
  · exact (primingScratchEvents_before e h).trans (by decide)
  · exact (Nat.le_refl 517)
  · exact (Nat.le_refl 517)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The emitting lane acquires K and has exact actual stack slots before loading its pointer. -/
theorem primingPreparedLaneWithFrameInPrefix {g i batch tile warp lane : Nat} (hb : batch < p.batch)
    (hTile : 128 * tile + 127 < 2 ^ 31)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {F : List (Nat × Value)}
    (hScratch : PrimingScratchExtra F) (hWait : PrimingKWaitExtra F) {t : TState}
    {ending : Option TState}
    (ht : At t 488 (primingScratchFacts p l batch (primingLaneRow tile (32 * warp + lane)) 0 ++ F))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending) {bound : Nat}
    (hBound : 517 ≤ bound) (hDemand : PrefixDemand X g i bound ending) :
    ∃ n u, let base := primingLaneRow tile (32 * warp + lane)
      let pre := primingKPrepEvents p l g batch base n
      let stop := i + pre.length
      (X.tr g).drop i = pre ++ (X.tr g).drop stop ∧
      At u 520 F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop stop) ending ∧
      PrefixDemand X g stop bound ending ∧
      ∀ slot : Fin 2, PrimingMetadataAt p l X g stop batch (base + 64 * slot.val) slot := by
  let tid := 32 * warp + lane
  let base := primingLaneRow tile tid
  have hRows : base + 64 < 2 ^ 31 := by
    have ht := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    have hc := Nat.mod_lt tid (by decide : 0 < 8)
    simp [base, primingLaneRow, kvCopyColumn]
    omega
  obtain ⟨n, u, rest, hTrace, hU, hRest⟩ :=
    primingScratchAndWaitObservedFrameInPrefix hp hX hb hRows writes
      hScratch hWait ht hr (hDemand.weaken hBound)
  let pre := primingKPrepEvents p l g batch base n
  let stop := i + pre.length
  have hPre : (X.tr g).drop i = pre ++ rest := by
    simpa only [pre, primingKPrepEvents, List.append_assoc, List.cons_append, List.nil_append]
      using hTrace
  have hTail : (X.tr g).drop stop = rest := by
    rw [← List.drop_drop, hPre, List.drop_left]
  have hLength : stop = i + (primingScratchEvents p l g batch base 0).length +
      (primingScratchEvents p l g batch base 1).length + n + 1 := by
    simp [stop, pre, primingKPrepEvents, Nat.add_assoc]
  have hFront : (X.tr g).drop i = pre ++ (X.tr g).drop stop := hTail.symm ▸ hPre
  refine ⟨n, u, hFront, hU.mono ((holds_append ..).mp hU.2.2.2.2).2,
    hTail.symm ▸ hRest, hDemand.advanceList hFront ?_, ?_⟩
  · exact fun _ he => (primingKPrepEvents_before p l g batch base n he).trans hBound
  · change ∀ slot : Fin 2, PrimingMetadataAt p l X g stop batch (base + 64 * slot.val) slot
    rw [hLength]
    exact primingMetadataFromObservedTrace hX hTrace

/-- The K replay uses the frame for both packed pointer rows. -/
theorem primingKPreparedLaneFromScratch {g i batch head tile warp lane : Nat} (hb : batch < p.batch)
    (hTile : 128 * tile + 127 < 2 ^ 31)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {t : TState} {ending : Option TState}
    (ht : At t 488 (primingKInitialScratchFacts p l batch head tile warp lane))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending) {bound : Nat}
    (hBound : 517 ≤ bound) (hDemand : PrefixDemand X g i bound ending) :
    ∃ n u, let base := primingLaneRow tile (32 * warp + lane)
      let pre := primingKPrepEvents p l g batch base n
      let stop := i + pre.length
      (X.tr g).drop i = pre ++ (X.tr g).drop stop ∧
      At u 520 (primingKPackFrame p l batch head tile warp lane) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop stop) ending ∧
      PrefixDemand X g stop bound ending ∧
      ∀ slot : Fin 2, PrimingMetadataAt p l X g stop batch (base + 64 * slot.val) slot :=
  primingPreparedLaneWithFrameInPrefix hp hX hb hTile writes
    (primingKFrameScratch p l batch head tile warp lane)
    (primingKFrameWait p l batch head tile warp lane) ht hr hBound hDemand

end
end PTX.Kernels.TmlFa4Fwd.Loader
