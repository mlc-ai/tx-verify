-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmSegA

@[expose] public section

/-! # The softmax region's loop test and the next block's bias pointers

From the loop test (pc 1049) to the first bias load of the loop (pc 1124): the test
`%rd11 == %rd498` is false while the counter is below `num_iters` (pcs 1049-1050), the next
iteration's mask is computed (pcs 1051-1056; not proved, see the development notes), then the key
offset
and the 64 pointers of the next block's bias (pcs 1057-1121) and the zero fill of the first
destination (pcs 1122-1123). The pieces from pc 1057 on compose to `seg_next`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

/-- `%p91 = (num_iters == i)` (pc 1049). -/
theorem seg_1049 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hi : d.i < 2 ^ 32) :
    Seg kernel asms L g 1 1049 (factsAt L g 1049 d) 1050 (factsAt L g 1050 d) := by
  have := hok.r26_lt
  intro t h
  sm_seg h [Nat.reduceMul]

/-- `@%p91 bra` (pc 1050) is not taken while the counter is below `num_iters`. -/
theorem seg_1050 (d : D) (hlt : d.i < d.e.r26) :
    Seg kernel asms L g 1 1050 (factsAt L g 1050 d) 1051 (factsAt L g 1051 d) := by
  have hv : valueOf L g d 91 = .pred false := by
    sm_vals
    have : d.e.r26 ≠ d.i := by omega
    simp [this]
  have hp : (91, Value.pred false) ∈ factsAt L g 1050 d :=
    hv ▸ Flow.mem_factsFrom (val := valueOf L g d) (show 91 ∈ Flow.live 1050 by decide +kernel)
  have hb := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) Flow.code_1050 hp
    (fun _ _ => localRule_bra) (segFree (by decide +kernel))
  exact hb.weaken_end fun R hR => Flow.holds_factsFrom_mono hR (by decide +kernel)

/-- `%r42 = %r40 + %r1451`, the key offset of the next block (pc 1057). -/
theorem seg_1057 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) :
    Seg kernel asms L g 1 1057 (factsAt L g 1057 d) 1058 (factsAt L g 1058 d) := by
  have := hok.splits
  intro t h
  sm_seg h [key, blkOf]

/-- The first bias pointer of the next block (pc 1058, `mad.wide.s32`). -/
theorem seg_1058 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 1058 (factsAt L g 1058 d) 1059 (factsAt L g 1059 d) := by
  have := p9_lt d.e (g % L.block)
  intro t h
  sm_seg h [Nat.reduceMul, ofInt_two, madwide_s32, ptrAt, sxw_two, sxw]

/-- Bias pointers 1 to 63 of the next block (pcs 1059 to 1121). -/
theorem seg_1059 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 20 1059 (factsAt L g 1059 d) 1079 (factsAt L g 1079 d) := by
  intro t h
  sm_seg h

theorem seg_1079 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 21 1079 (factsAt L g 1079 d) 1100 (factsAt L g 1100 d) := by
  intro t h
  sm_seg h

theorem seg_1100 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 22 1100 (factsAt L g 1100 d) 1122 (factsAt L g 1122 d) := by
  intro t h
  sm_seg h

/-- The zero fill of the first destination (pcs 1122 and 1123). -/
theorem seg_1122 (d : D) (hT : g % L.block < 128) (hcv : d.cv = 0) :
    Seg kernel asms L g 2 1122 (factsAt L g 1122 d) 1124 (factsAt L g 1124 d) := by
  intro t h
  sm_seg h [hcv, D.vd]

/-- **The next block's key offset and bias pointers**, and the zero fill of the first destination
(pcs 1057 to 1123). -/
theorem seg_next (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hcv : d.cv = 0) :
    Seg kernel asms L g 67 1057 (factsAt L g 1057 d) 1124 (factsAt L g 1124 d) := by
  have h1 := (seg_1057 d hT hok).comp (seg_1058 d hT)
  have h2 := h1.comp (seg_1059 d hT)
  have h3 := h2.comp (seg_1079 d hT)
  have h4 := h3.comp (seg_1100 d hT)
  have h5 := h4.comp (seg_1122 d hT hcv)
  exact Seg.of_len h5 rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
