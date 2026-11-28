-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Cnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.ShapeLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.ShapeEpi

@[expose] public section

/-! # Warpgroup 0's events by state

Every event a state of warpgroup 0's control machine fires has the shape of its site (`Ev.lean`):
the site files' obligations, one per site family (`shape`), and the same for the counted machine
(`shape_counted`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The event kind a state of warpgroup 0 fires is its site's. -/
theorem shapeK (hp : Pre P L m) : (code P L g w).Shape (EvK P L g w) := by
  refine Code.Shape.of_at fun d => ?_
  cases hs : d.site with
  | smr => exact shapeAt_smr d hs
  | sink => exact shapeAt_nc d (.inl hs)
  | lenA => exact shapeAt_nc d (.inr (.inl hs))
  | lenB => exact shapeAt_nc d (.inr (.inr hs))
  | bwait => exact shapeAt_bwait d hs
  | arrL => exact shapeAt_arrL d hs
  | bar0 => exact shapeAt_bar9 hp d (.inl hs)
  | wv => exact shapeAt_wv d hs
  | wq => exact shapeAt_wq d hs
  | tcfa => exact shapeAt_tcFence d (.inl hs)
  | sld a k => exact shapeAt_sld d ⟨a, k, hs⟩
  | sldw => exact shapeAt_ldWait hp d (.inl hs)
  | tcfb => exact shapeAt_tcFence d (.inr (.inr (.inl hs)))
  | vm => exact shapeAt_rd d (.inl hs)
  | pst k => exact shapeAt_wr d (.inl ⟨k, hs⟩)
  | bar1 => exact shapeAt_bar1 hp d hs
  | pld k => exact shapeAt_rd d (.inr (.inl ⟨k, hs⟩))
  | mst => exact shapeAt_wr d (.inr (.inl hs))
  | bar2 => exact shapeAt_bar9 hp d (.inr hs)
  | arrV => exact shapeAt_arrV d hs
  | mld => exact shapeAt_rd d (.inr (.inr hs))
  | vote => exact shapeAt_vote d hs
  | ost k => exact shapeAt_wr d (.inr (.inr ⟨k, hs⟩))
  | rsf => exact shapeAt_tcFence d (.inr (.inl hs))
  | rld c => exact shapeAt_rld d ⟨c, hs⟩
  | rldw c => exact shapeAt_ldWait hp d (.inr ⟨c, hs⟩)
  | rst c => exact shapeAt_rst d ⟨c, hs⟩
  | rstw c => exact shapeAt_rstw d ⟨c, hs⟩
  | rsfb => exact shapeAt_tcFence d (.inr (.inr (.inr (.inl hs))))
  | fpx => exact shapeAt_tcFence d (.inr (.inr (.inr (.inr hs))))
  | arrS => exact shapeAt_arrS d hs
  | ebar0 => exact shapeAt_ebar9 hp d (.inl hs)
  | est => exact shapeAt_ewr d (.inl hs)
  | ebar1 => exact shapeAt_ebar9 hp d (.inr hs)
  | eld => exact shapeAt_eld d hs
  | lse => exact shapeAt_ewr d (.inr hs)
  | wsv => exact shapeAt_wsv d hs
  | efa => exact shapeAt_eFence d (.inl hs)
  | old c => exact shapeAt_old d ⟨c, hs⟩
  | oldw c => exact shapeAt_oldw hp d ⟨c, hs⟩
  | ost2 c k => exact shapeAt_ost2 hp c d ⟨k, hs⟩
  | ofpx c => exact shapeAt_eFence d (.inr ⟨c, hs⟩)
  | obar c => exact shapeAt_obar hp d ⟨c, hs⟩
  | oel c => exact shapeAt_oel d ⟨c, hs⟩
  | otma c => exact shapeAt_otma hp d ⟨c, hs⟩
  | commit => exact shapeAt_commit d hs
  | ebar => exact shapeAt_ebar hp d hs
  | dealloc => exact shapeAt_dealloc d hs
  | exit => exact shapeAt_exit d hs

/-- **The event a state of warpgroup 0 fires is the event of its site, at its pc.** -/
theorem shape (hp : Pre P L m) : (code P L g w).Shape (Ev P L g w) :=
  fun hat hi hc hf => ⟨fires_pc hf, shapeK hp hat hi hc hf⟩

/-- The counted machine's shape table. -/
theorem shape_counted (hp : Pre P L m) : (MC P L g w).Shape (fun d e => Ev P L g w d.1 e) :=
  Code.Shape.counted (shape hp)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
