-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.EvR
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Sim
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part122
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The addresses of the correction warps' launch-word reads

The correction warps' shape table states a scheduler read without its address (`rdOrUb`). The
launch-input source needs the address: `EvR` is a second shape table for the scan's reads, the
chosen request's two reads (the output warp's shapes of `toE d`, whose addresses `rdAddr` are the
same terms of the scan state) and the used-K read (`ukAddr`); it says nothing at other sites. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- The shape obligations of the reads that the theorem's `hs` admits. -/
local macro "rd_shape" : tactic => `(tactic|
  site_shape s skip_by (simp at hs)
    unfolding [EvR, Epilogue.Ev, Epilogue.rdAddr, ukAddr, toE, epi, Epilogue.vbits]
    reg_vals [valueOf, values, valuesStart, valuesRole, valuesScan, valuesSelect,
      valuesSelect2, valuesTile, Epilogue.partials, loopRegsR, Epilogue.lanePreds, lookupLit]
    addr_by (corr_addr))

theorem shapeR_word (_hp : Pre p L m) (d : D) (hk : d.k = 0) (k : Epilogue.Scan)
    (hs : d.site = .word k) : (code p L g).ShapeAt (EvR p L g) d := by
  obtain ⟨s, v, k'⟩ := d
  cases hk
  cases k <;> rd_shape

theorem shapeR_req (_hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk) : (code p L g).ShapeAt (EvR p L g) d := by
  obtain ⟨s, v, k'⟩ := d
  cases hk
  rd_shape

/-- **The reads' shapes with their addresses.** -/
theorem shapeR (hp : Pre p L m) : (code p L g).Shape (EvR p L g) := by
  refine Code.Shape.of_at fun d => ?_
  by_cases hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk
  · by_cases hk : d.k = 0
    · rcases hs with ⟨k, h⟩ | h
      · exact shapeR_word hp d hk k h
      · exact shapeR_req hp d hk h
    · intro _ hi
      exfalso
      rcases hi with hi | hi
      · exact hk hi
      · rcases hs with ⟨k, h⟩ | h | h | h <;> simp [Site.midOk, h] at hi
  · intro _ _ _ _
    obtain ⟨s, v, k⟩ := d
    cases s <;> simp_all [EvR]

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
