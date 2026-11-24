-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressQueryPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaHistory

public section

/-! # A pending query TMA wait can advance the actual tiles already issued -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- At a pending query TMA wait, each tile is either notified or has a counted extension. -/
theorem query_wait_tile_or_extension (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) {g : Nat} {d : Wg1Mma.D} (hp : Frame.Pending L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = .qWait) (tile : Fin 8) :
    (∃ j < (X.tr g).length,
      X.TensorIssue (g, j) (P.param1Base + Wg1Mma.qMapOff) (MmaDataTrace.queryTmaSpec P L g tile) ∧
        (X.tensor (g, j)).any (fun o => o.effects.notified) = true) ∨
      (∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L) := by
  obtain ⟨j, hj, hi⟩ :=
    QueryTmaHistory.load_before_pending_wait tile hpre hX (hs g hp.1).machine hub hp hσ hd
  cases hNote : (X.tensor (g, j)).any (fun o => o.effects.notified)
  · exact .inr (query_tensor_extension hpre tile hs hX ht hi hNote)
  · exact .inl ⟨j, hj, hi, hNote⟩

/-- A maximal execution at a pending query TMA poll has already notified all eight query tiles. -/
theorem query_wait_tiles_notified (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) {g : Nat} {d : Wg1Mma.D} (hp : Frame.Pending L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = .qWait) (tile : Fin 8) :
    ∃ j < (X.tr g).length,
      X.TensorIssue (g, j) (P.param1Base + Wg1Mma.qMapOff) (MmaDataTrace.queryTmaSpec P L g tile) ∧
        (X.tensor (g, j)).any (fun o => o.effects.notified) = true :=
  (query_wait_tile_or_extension hpre hmax.1 hs ht hub hp hσ hd tile).resolve_right hmax.not_grows

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
