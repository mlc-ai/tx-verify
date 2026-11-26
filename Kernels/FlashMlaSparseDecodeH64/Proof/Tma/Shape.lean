-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Cnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ShapeA
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ShapeB

@[expose] public section

/-! # The TMA warp's shape table

`shape`: the event a state of the TMA warp fires is its site's (`Ev.lean`), from the site
obligations (`ShapeA.lean`, `ShapeB.lean`), and the same for the counted machine
(`shape_counted`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The event kind a state of the TMA warp fires is its site's. -/
theorem shapeK (hp : Pre P L m) : (code P L g).Shape (EvK L g) := by
  refine Code.Shape.of_at fun d => ?_
  cases hs : d.site with
  | elect => exact shapeAt_elect d hs
  | loadTopk => exact shapeAt_lens d (.inl hs)
  | loadExtra => exact shapeAt_lens d (.inr hs)
  | qWait => exact shapeAt_qWait d hs
  | storeWait => exact shapeAt_storeWait d hs
  | coordWait => exact shapeAt_coordWait d hs
  | rawWait => exact shapeAt_rawWait d hs
  | coord0 k => exact shapeAt_coord d ⟨k, .inl hs⟩
  | coord1 k => exact shapeAt_coord d ⟨k, .inr (.inl hs)⟩
  | coord2 k => exact shapeAt_coord d ⟨k, .inr (.inr (.inl hs))⟩
  | coord3 k => exact shapeAt_coord d ⟨k, .inr (.inr (.inr hs))⟩
  | gather k => exact shapeAt_gather hp d ⟨k, hs⟩
  | rawArrive => exact shapeAt_rawArrive hp d hs
  | coordFree => exact shapeAt_coordFree hp d hs
  | outBar => exact shapeAt_outBar hp d hs
  | exit => exact shapeAt_exit d hs
  | leave s => exact shapeAt_leave d hs

/-- **The event a state of the TMA warp fires is the event of its site, at its pc.** -/
theorem shape (hp : Pre P L m) : (code P L g).Shape (Ev L g) :=
  fun hat hi hc hf => ⟨fires_pc hf, shapeK hp hat hi hc hf⟩

/-- The counted machine's shape table. -/
theorem shape_counted (hp : Pre P L m) : (TC P L g).Shape (fun d e => Ev L g d.1 e) :=
  Code.Shape.counted (shape hp)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
