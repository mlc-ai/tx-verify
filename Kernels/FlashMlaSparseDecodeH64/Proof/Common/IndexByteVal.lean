-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexRecvVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StoreVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexByte
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The validity byte a lane of the index warp stores

At the validity byte's site of a lane `g` with `%tid.x % 4 = 0` in block `b`, the word the byte is
the low byte of (`ixByteW`) has bit `i < 8` the validity of lane `g + i / 2`'s position `i % 2`
in block `b` (`ix_byteBits`): its own bits, the receives from lanes `g + 1` and `g + 2` and
`g + 3` (`ix_recv1`, `ix_recv2`) and the quad bits (`byte_bits`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The lanes of a quad: the butterflies of distance 1 and 2 from a lane `0 mod 4`. -/
theorem xor_quad {l : Nat} (hl : l < 32) (h4 : l % 4 = 0) :
    l ^^^ 1 = l + 1 ∧ l ^^^ 2 = l + 2 ∧ (l + 2) ^^^ 1 = l + 3 := by
  have : l = 0 ∨ l = 4 ∨ l = 8 ∨ l = 12 ∨ l = 16 ∨ l = 20 ∨ l = 24 ∨ l = 28 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The bits of the validity byte of block `b`.** -/
theorem ix_byteBits (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {d : Index.D} {n : Cls → Nat} (hub : NoUbBefore X g k)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n)))
    (hx : g < L.threads) (hw : warpOf L g = 7) (hs : d.site = .bA ∨ d.site = .bB)
    (hm4 : tidOf L g % 4 = 0) :
    ∃ b, n (.index .st) = 3 * b + 2 ∧ (d.site = .bA → MainOk P L g d b) ∧
      (d.site = .bB → ExtraOk P L g d b) ∧
      ∀ i < 8, (truncBits 8 (ixByteW L g d)).toNat.testBit i = vbit P L (g + i / 2) b (i % 2) := by
  obtain ⟨b, hn, hst, hsk, hM, hE⟩ := ix_blk hp hX hFw hub hσ hx hw
  have hsoff : soff d.site = 2 := by rcases hs with h | h <;> simp [h]
  have hcn : n .shfl = ((X.tr g).take k).countP Execution.isShfl := state_count hσ .shfl
  have hskip : sgB L g = 1 := by
    have := hsk hs
    simp only [sgB, this]
    decide
  have hst' : n (.index .st) = 3 * b + 2 := by
    have h2 : stDone L g d.site d.el = 2 := by rcases hs with h | h <;> simp [h, stDone]
    rw [hst, h2, hskip]
  obtain ⟨hr1, hr2⟩ := ix_rv hp hX hFw hub hσ
  have r1 : RecvAt X g (3 + 2 * b) d.c.rv1 := by
    have := hr1 (by omega)
    rwa [show ((X.tr g).take k).countP Execution.isShfl - soff d.site = 3 + 2 * b by omega] at this
  have r2 : RecvAt X g (3 + 2 * b + 1) d.c.rv2 := by
    have := hr2 hsoff
    rwa [show ((X.tr g).take k).countP Execution.isShfl - 1 = 3 + 2 * b + 1 by omega] at this
  obtain ⟨y1, hy1, hy1t, hy1w, hv1⟩ := ix_recv1 hp hX hFw hx hw r1
  obtain ⟨y2, z, hy2, hz, hy2t, hzt, hy2w, hzw, hv2⟩ := ix_recv2 hp hX hFw hx hw r2
  refine ⟨b, hst', fun h => ?_, fun h => ?_, ?_⟩
  · exact hM (Or.inr (Or.inr (Or.inr h)))
  · exact hE (Or.inr (Or.inr (Or.inr h)))
  · intro i hi
    have ht : ∀ y, tidOf L y = y % 384 := fun y => tidOf_eq hp y
    have hlane : ∀ y, PTX.laneOf L y = y % 384 % 32 := fun y => by simp only [PTX.laneOf, hp.block]
    have hl4 : g % 384 % 32 % 4 = 0 := by have := ht g; omega
    have hq := xor_quad (Nat.mod_lt (g % 384) (by norm_num : 0 < 32)) hl4
    rw [hlane, hq.1] at hy1
    rw [hlane, hq.2.1] at hy2
    have e1 : y1 = g + 1 := by omega
    have e2 : y2 = g + 2 := by omega
    subst e1 e2
    have hl2 : (g + 2) % 384 % 32 = g % 384 % 32 + 2 := by omega
    rw [hlane, hl2, hq.2.2] at hz
    have e3 : z = g + 3 := by omega
    subst e3
    have hw' : ixByteW L g d = or32 (or32 (rvw d.c.rv1)
        (ixQuadW L g (vbit P L g b 0) (vbit P L g b 1))) (rvw d.c.rv2) := by
      rcases hs with h | h
      · obtain ⟨o0, o1⟩ := okMain_vbit (hM (Or.inr (Or.inr (Or.inr h))))
        simp only [ixByteW, h, o0, o1]
      · obtain ⟨o0, o1⟩ := okExtra_vbit (hE (Or.inr (Or.inr (Or.inr h))))
        simp only [ixByteW, h, o0, o1]
    have q0 := ixQuadW_lane L g (j := 0) (by norm_num) (by omega)
    have q1 := ixQuadW_lane L (g + 1) (j := 1) (by norm_num) (by have := ht (g + 1); omega)
    have q2 := ixQuadW_lane L (g + 2) (j := 2) (by norm_num) (by have := ht (g + 2); omega)
    have q3 := ixQuadW_lane L (g + 3) (j := 3) (by norm_num) (by have := ht (g + 3); omega)
    have hbb := byte_bits (vbit P L g b 0) (vbit P L g b 1) (vbit P L (g + 1) b 0)
      (vbit P L (g + 1) b 1) (vbit P L (g + 2) b 0) (vbit P L (g + 2) b 1)
      (vbit P L (g + 3) b 0) (vbit P L (g + 3) b 1) i hi
    rw [hw', hv1, hv2, q0, q1, q2, q3]
    refine hbb.trans ?_
    interval_cases i <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
