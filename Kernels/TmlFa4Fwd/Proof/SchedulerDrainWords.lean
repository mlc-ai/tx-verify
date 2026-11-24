-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Kernel.ReadValue
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.WarpScan
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Lemmas.Flow.Local
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanGuard

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The word provided to the first drain shuffle. Lanes above the sentinel skip the read. -/
def drainCuQ (p : Params) (lane : Nat) : Nat :=
  if lane ≤ p.batch then p.qOffset lane else 0

variable {p : Params} {l : Launch}

/-- The down shuffle's source carries the right endpoint of each active request.
The reserved lane never computes a tile count. -/
theorem drainWordTiles {m : Mem0} (hp : Pre p l m) (first lane : Nat) :
    let source := (shflSource .down lane 1 31).1
    let begin := drainCuQ p (first + lane)
    let finish := drainCuQ p (first + source)
    let active := decide (first + lane < p.batch ∧ lane < 31)
    begin < 2 ^ 32 ∧ finish < 2 ^ 32 ∧ (active = true → begin ≤ finish) ∧
      finish - begin < 2 ^ 30 ∧
      (if active then (finish - begin + 255) / 256 else 0) = groupLaneTiles p first lane := by
  have mono : ∀ a b, a ≤ b → b ≤ p.batch → p.qOffset a ≤ p.qOffset b := by
    intro a b hab hb
    induction b with
    | zero => simp [Nat.eq_zero_of_le_zero hab]
    | succ b ih =>
      by_cases h : a = b + 1
      · rw [h]
      · exact (ih (by omega) (by omega)).trans (hp.lengths b (by omega)).1
  have hWord (i : Nat) : drainCuQ p i < 2 ^ 30 := by
    unfold drainCuQ
    split
    · rename_i h
      have hLe := mono i p.batch h (Nat.le_refl _)
      have hTot := hp.shape.2.2.2.2.2
      change p.qOffset p.batch + 256 * p.batch < 2 ^ 30 at hTot
      omega
    · decide
  dsimp only
  have hb := hWord (first + lane)
  have he := hWord (first + (shflSource .down lane 1 31).1)
  refine ⟨by omega, by omega, ?_, by omega, ?_⟩
  · intro ha
    have hActive := of_decide_eq_true ha
    obtain ⟨hBatch, hLane⟩ := hActive
    rw [shflSource_down_one, ite_eq_left (show lane + 1 < 32 by omega)]
    simpa [drainCuQ, hBatch, show first + lane ≤ p.batch by omega, ← Nat.add_assoc]
      using (hp.lengths _ hBatch).1
  · by_cases h : lane < 31 ∧ first + lane < p.batch
    · obtain ⟨hLane, hBatch⟩ := h
      rw [shflSource_down_one, ite_eq_left (show lane + 1 < 32 by omega)]
      simp [hLane, hBatch, groupLaneTiles, drainCuQ, requestTiles, Params.qLength,
        show first + lane ≤ p.batch by omega, ← Nat.add_assoc]
    · have h' : ¬ (first + lane < p.batch ∧ lane < 31) := fun h' => h ⟨h'.2, h'.1⟩
      simp [h, h', groupLaneTiles]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
