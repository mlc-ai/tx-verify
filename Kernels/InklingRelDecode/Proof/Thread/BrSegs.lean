-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.BrStep

@[expose] public section

/-! # The bridge's segments: pcs 2560-2564, up to the epilogue's poll at pc 2565 -/

namespace PTX.Kernels.InklingRelDecode.Proof.Br
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Epi

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- **The test of `num_iters` and the release of the dependent grid** (pcs 2560-2561). -/
theorem seg_test (i : In) (hok : i.Ok) :
    Seg kernel asms L g 2 2560 (bfacts 2560 i) 2562 (bfacts 2562 i) := by
  intro t h
  br_segs h [In.skip, Nat.mod_eq_of_lt hok.n, M32]

/-! ### The row's log-sum-exp (pcs 2562-2563) -/

theorem live_ne_lg2 : ∀ r ∈ Flow.live 2563, r = 1759 ∨ (r ≠ 1759 ∧ r ∈ Flow.live 2562) := by
  decide +kernel

theorem code_lg2 : kernel.code[2562]? = some ⟨none, .float
    { lg2I with dsts := [some 1759], srcs := [.reg 1915] }⟩ := Flow.code_2562

/-- **`lg2.approx.ftz.f32`** (pc 2562): the logarithm of the row sum, under the condition that
it does not fault. -/
theorem seg_lg2 (i : In) :
    SegD kernel asms L g 1 2562 (bfacts 2562 i) 2563 (bfacts 2563 i) ((lg2E i.l).toBool = true) :=
  SegD.one (E := lg2E i.l) (d := 1759) code_lg2 rfl
    (fun t h => by
      have hl : 1915 ∈ Flow.live 2562 := by decide +kernel
      have h1 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueB i) hl)
      exact exec_lg2E h.1 (OpndIs.reg h1))
    (fun x hx _ => by
      show okVal (b32 0) (lg2E i.l) = x
      exact okVal_of_ok hx)
    live_ne_lg2

/-! ### The fused multiply-add (pc 2563) -/

theorem live_ne_fma : ∀ r ∈ Flow.live 2564, r = 524 ∨ (r ≠ 524 ∧ r ∈ Flow.live 2563) := by
  decide +kernel

theorem code_fma : kernel.code[2563]? = some ⟨none, .float
    { fmaI .rn false with dsts := [some 524], srcs := [.reg 498, .reg 1914, .reg 1759] }⟩ :=
  Flow.code_2563

/-- **`fma.rn.f32 %r63, %r37, %r1453, %r1298`** (pc 2563): the log-sum-exp, under the condition
that it does not fault. -/
theorem seg_fma (i : In) :
    SegD kernel asms L g 1 2563 (bfacts 2563 i) 2564 (bfacts 2564 i)
      ((floatE lseI [i.sc, i.mx, i.lg2v]).toBool = true) :=
  SegD.one (E := floatE lseI [i.sc, i.mx, i.lg2v]) (d := 524) code_fma rfl
    (fun t h => by
      have h1 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueB i)
        (show 498 ∈ Flow.live 2563 by decide +kernel))
      have h2 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueB i)
        (show 1914 ∈ Flow.live 2563 by decide +kernel))
      have h3 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueB i)
        (show 1759 ∈ Flow.live 2563 by decide +kernel))
      exact exec_floatE_fma_at (idealAtBr (Or.inl rfl) (by have := h.1; omega))
        (declineAtBr (Or.inl rfl) (by have := h.1; omega)) (OpndIs.reg h1) (OpndIs.reg h2)
        (OpndIs.reg h3))
    (fun x hx _ => by
      show okVal (b32 0) (floatE lseI [i.sc, i.mx, i.lg2v]) = x
      exact okVal_of_ok hx)
    live_ne_fma

/-! ### The parity word of the poll (pc 2564) -/

/-- **`mov.b32 %r1299, 0`** (pc 2564): the parity word of the poll of `o_final`. -/
theorem seg_zero (i : In) :
    Seg kernel asms L g 1 2564 (bfacts 2564 i) 2565 (bfacts 2565 i) := by
  intro t h
  br_seg h

end
end PTX.Kernels.InklingRelDecode.Proof.Br
