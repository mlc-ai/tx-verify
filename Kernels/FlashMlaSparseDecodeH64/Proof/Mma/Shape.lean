-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Cnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.ShapeQ
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.ShapeLoop

@[expose] public section

/-! # The MMA warp's events by state

Every event a state of the MMA warp fires has the shape of its site (`Ev.lean`): the site files'
obligations, one per site family (`shape`), and the same for the counted machine
(`shape_counted`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The event kind a state of the MMA warp fires is its site's. -/
theorem shapeK (hp : Pre P L m) : (code P L g).Shape (EvK L g) := by
  refine Code.Shape.of_at fun d => ?_
  cases hs : d.site with
  | elect => exact shapeAt_elect d hs
  | loadTopk => exact shapeAt_loadTopk d hs
  | loadExtra => exact shapeAt_loadExtra d hs
  | trap => exact shapeAt_trap d hs
  | qLoad k => exact shapeAt_qLoad hp d ⟨k, hs⟩
  | qArrive => exact shapeAt_qArrive hp d hs
  | qWait => exact shapeAt_qWait d hs
  | qFence => exact shapeAt_fence d (.inl hs)
  | qCopy k => exact shapeAt_qCopy d ⟨k, hs⟩
  | qCopyCommit => exact shapeAt_qCopyCommit d hs
  | qCopyWait => exact shapeAt_qCopyWait d hs
  | qCopyFence => exact shapeAt_fence d (.inr (.inl hs))
  | kvWait => exact shapeAt_kvWait d hs
  | kvFence => exact shapeAt_fence d (.inr (.inr (.inl hs)))
  | qk k => exact shapeAt_qk d ⟨k, hs⟩
  | qkCommit => exact shapeAt_qkCommit d hs
  | soWait => exact shapeAt_soWait d hs
  | soFence => exact shapeAt_fence d (.inr (.inr (.inr hs)))
  | pv k => exact shapeAt_pv d ⟨k, hs⟩
  | pvCommit => exact shapeAt_pvCommit d hs
  | outBar => exact shapeAt_outBar hp d hs
  | exit => exact shapeAt_exit d hs
  | leave s => exact shapeAt_leave d hs

/-- **The event a state of the MMA warp fires is the event of its site, at its pc.** -/
theorem shape (hp : Pre P L m) : (code P L g).Shape (Ev L g) :=
  fun hat hi hc hf => ⟨fires_pc hf, shapeK hp hat hi hc hf⟩

/-- The counted machine's shape table. -/
theorem shape_counted (hp : Pre P L m) : (MC P L g).Shape (fun d e => Ev L g d.1 e) :=
  Code.Shape.counted (shape hp)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
