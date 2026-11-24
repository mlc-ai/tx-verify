-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderActiveProgram
public import Kernels.TmlFa4Fwd.Audit.ShiftLoop
public import Kernels.TmlFa4Fwd.Flow.Code.Part006

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem shiftSeg {l : Launch} {g a n b : Nat} {F G : List (Nat × Value)}
    (hLo : 174 ≤ a) (hHi : a + n ≤ 1906)
    (hStraight : ((kernel.code.drop a).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (segment : Seg kernel [] l g n a F b G) :
    Seg kernel Assumptions.all l g n a F b G := by
  intro t ht
  obtain ⟨u, hr, hu⟩ := segment t ht
  exact ⟨u, (loaderLinear (regs := []) hLo hHi ht.1 (by simp) hStraight hr).1, hu⟩

def loaderShiftCarry (row base : Nat) : List (Nat × Value) :=
  [(1801, b32 (256 * row)), (1087, b32 (base + 256 * row)),
   (7296, b64 16), (1798, b32 16)]

private theorem shiftInit {l : Launch} {g row base : Nat} (hEnd : base + 256 * row < 2 ^ 32) :
    Seg kernel [] l g 3 386
      [(7168, b32 row), (1799, b32 base), (103, .pred false),
       (7296, b64 16), (1798, b32 16)]
      389 ((103, .pred false) :: loaderShiftCarry row base) := by
  have h32 : row < 2 ^ 32 := by omega
  have hRow : 256 * row < 2 ^ 32 := by omega
  have hBase : base < 2 ^ 32 := by omega
  have hShift : (truncBits 32 (BitVec.ofInt 64 8)).toNat = 8 := rfl
  have he : BitVec.ofNat 64 row <<< 8 = BitVec.ofNat 64 (256 * row) := by
    rw [nf_shl]
    congr 1
    omega
  intro t ht
  simp only [loaderShiftCarry]
  seg_fp ht using
    simp only [b32, truncBits_ofNat h32 (by decide), truncBits_ofNat hBase (by decide), hShift,
      show ¬8 ≥ 32 by decide, ↓reduceIte, he, truncBits_ofNat hRow (by decide),
      ← BitVec.ofNat_add, truncBits_ofNat hEnd (by decide)]

private theorem shiftGuardOne (l : Launch) (g row base : Nat) :
    Seg kernel [] l g 2 390 ((103, .pred false) :: loaderShiftCarry row base) 392
      ((104, .pred false) :: loaderShiftCarry row base) := by
  intro t ht
  simp only [loaderShiftCarry] at ht ⊢
  seg_fp ht using decide

private theorem shiftGuardTwo (l : Launch) (g row base : Nat) :
    Seg kernel [] l g 2 393 ((104, .pred false) :: loaderShiftCarry row base) 395
      ((105, .pred false) :: loaderShiftCarry row base) := by
  intro t ht
  simp only [loaderShiftCarry] at ht ⊢
  seg_fp ht using decide

private theorem shiftSeeds (l : Launch) (g row base : Nat) :
    Seg kernel [] l g 2 396 ((105, .pred false) :: loaderShiftCarry row base) 398
      ((7171, b32 2) :: (1059, .bits 16 1) :: loaderShiftCarry row base) := by
  intro t ht
  simp only [loaderShiftCarry] at ht ⊢
  seg_fp ht using decide

private theorem shiftRound (l : Launch) (g row base : Nat) (i : Fin 3) :
    Seg kernel Assumptions.all l g 4 398
      ((7171, b32 (2 ^ (i.val + 1))) :: (1059, .bits 16 (BitVec.ofNat 64 (i.val + 1))) ::
        loaderShiftCarry row base) (if i.val = 2 then 402 else 398)
      ((7171, b32 (2 ^ (i.val + 2))) :: (1059, .bits 16 (BitVec.ofNat 64 (i.val + 2))) ::
        loaderShiftCarry row base) := by
  apply shiftSeg (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
  fin_cases i <;> intro t ht <;>
    simp only [loaderShiftCarry, show (0 : Nat) ≠ 2 by decide, ↓reduceIte] at ht ⊢ <;>
    seg_fp ht using decide

/-- At the launch's page-size word 16, the actual shift loop executes exactly three rounds
and computes 4. The selected Q block's global row offset is preserved. -/
theorem loaderQueryShiftLoop {l : Launch} {g row base : Nat}
    (hEnd : base + 256 * row < 2 ^ 32) :
    Seg kernel Assumptions.all l g 24 386
      [(7168, b32 row), (1799, b32 base), (103, .pred false),
       (7296, b64 16), (1798, b32 16)]
      402 ((7171, b32 16) :: (1059, .bits 16 4) :: loaderShiftCarry row base) := by
  have step₀ := shiftSeg (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
    (shiftInit (l := l) (g := g) hEnd)
  have branch₀ : Seg kernel [] l g 1 389 ((103, .pred false) :: loaderShiftCarry row base) 390
      ((103, .pred false) :: loaderShiftCarry row base) :=
    Seg.bra (K := kernel) (A := []) (L := l) (g := g) (pick := false)
      Flow.code_389 (by simp) (by simp)
  have step₁ := shiftSeg (by decide) (by decide) rfl branch₀
  have step₂ := shiftSeg (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
    (shiftGuardOne l g row base)
  have branch₁ : Seg kernel [] l g 1 392 ((104, .pred false) :: loaderShiftCarry row base) 393
      ((104, .pred false) :: loaderShiftCarry row base) :=
    Seg.bra (K := kernel) (A := []) (L := l) (g := g) (pick := false)
      Flow.code_392 (by simp) (by simp)
  have step₃ := shiftSeg (by decide) (by decide) rfl branch₁
  have step₄ := shiftSeg (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
    (shiftGuardTwo l g row base)
  have branch₂ : Seg kernel [] l g 1 395 ((105, .pred false) :: loaderShiftCarry row base) 396
      ((105, .pred false) :: loaderShiftCarry row base) :=
    Seg.bra (K := kernel) (A := []) (L := l) (g := g) (pick := false)
      Flow.code_395 (by simp) (by simp)
  have step₅ := shiftSeg (by decide) (by decide) rfl branch₂
  have step₆ := shiftSeg (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
    (shiftSeeds l g row base)
  exact step₀.comp (step₁.comp (step₂.comp (step₃.comp (step₄.comp (step₅.comp
    (step₆.comp ((shiftRound l g row base 0).comp ((shiftRound l g row base 1).comp
      (shiftRound l g row base 2)))))))))

private theorem powerEnvelope {l : Launch} {g row base : Nat} :
    Seg kernel [] l g 7 402 ((7171, b32 16) :: (1059, .bits 16 4) :: loaderShiftCarry row base)
      409 ((107, .pred false) :: (7298, b64 0) :: (1059, .bits 16 4) ::
        loaderShiftCarry row base) := by
  intro t ht
  simp only [loaderShiftCarry] at ht ⊢
  seg_fp ht using decide

private theorem zeroReciprocal {l : Launch} {g row base : Nat} :
    Seg kernel [] l g 4 410 ((107, .pred false) :: (7298, b64 0) :: (1059, .bits 16 4) ::
        loaderShiftCarry row base)
      415 ((9534, b64 0) :: (1059, .bits 16 4) :: loaderShiftCarry row base) := by
  intro t ht
  simp only [loaderShiftCarry] at ht ⊢
  seg_fp ht using decide

/-- The exact power-of-two page word has zero reciprocal correction, so the decoded
32-bit division path rejoins the address setup at 415. -/
theorem loaderShiftReciprocal {l : Launch} {g row base : Nat} :
    Seg kernel Assumptions.all l g 12 402
      ((7171, b32 16) :: (1059, .bits 16 4) :: loaderShiftCarry row base)
      415 ((9534, b64 0) :: (1059, .bits 16 4) :: loaderShiftCarry row base) := by
  have step₀ := shiftSeg (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) (powerEnvelope (l := l) (g := g)
      (row := row) (base := base))
  have branch : Seg kernel [] l g 1 409
      ((107, .pred false) :: (7298, b64 0) :: (1059, .bits 16 4) :: loaderShiftCarry row base)
      410 ((107, .pred false) :: (7298, b64 0) :: (1059, .bits 16 4) ::
        loaderShiftCarry row base) :=
    Seg.bra (K := kernel) (A := []) (L := l) (g := g) (pick := false)
      Flow.code_409 (by simp) (by simp)
  have step₁ := shiftSeg (by decide) (by decide) rfl branch
  have step₂ := shiftSeg (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) (zeroReciprocal (l := l) (g := g)
      (row := row) (base := base))
  exact step₀.comp (step₁.comp step₂)

end
end PTX.Kernels.TmlFa4Fwd.Loader
