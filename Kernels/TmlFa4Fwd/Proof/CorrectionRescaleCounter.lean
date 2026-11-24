-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleBranch
public import Lemmas.Flow.Footprint
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part131

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The rescale loop counts remaining KV blocks with a negative 32-bit word. -/
def remainingRescaleWord (blocks : Nat) : Value := b32 (2 ^ 32 - blocks)

private theorem signedBlocks {blocks : Nat} (h : blocks < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 blocks) = (blocks : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show blocks < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show blocks < 2 ^ 32 by omega), ite_eq_left h]

/-- The rescale body is skipped for zero or one KV block. -/
theorem rescaleEntryCount (l : Launch) (g : Nat) {blocks : Nat}
    (hBound : blocks < 2 ^ 31) :
    Seg kernel [] l g 1 7989 [(1636, b32 blocks)] 7990
      [(730, .pred (decide (blocks < 2))), (1636, b32 blocks)] := by
  intro t ht
  have h32 : blocks < 2 ^ 32 := by omega
  have hTwo : toSigned 32 (truncBits 32 (BitVec.ofInt 64 2)) = 2 := rfl
  seg_fp ht using
    simp only [truncBits_ofNat h32 (by decide), compare, Option.getD_some,
      signedBlocks hBound, hTwo, Value.pred.injEq, decide_eq_decide]
    all_goals omega

/-- After a pair of rescale stages the real loop updates its word and stops at minus one. -/
theorem rescaleNextCount (l : Launch) (g : Nat) {blocks : Nat}
    (hLo : 2 ≤ blocks) (hHi : blocks < 2 ^ 31) :
    Seg kernel [] l g 2 8444 [(7278, remainingRescaleWord blocks)] 8446
      [(735, .pred (decide (2 < blocks))), (7278, remainingRescaleWord (blocks - 1))] := by
  intro t ht
  have hWord : 2 ^ 32 - blocks < 2 ^ 32 := by omega
  have hNext : 2 ^ 32 - (blocks - 1) < 2 ^ 32 := by omega
  have hEq : 2 ^ 32 - blocks + 1 = 2 ^ 32 - (blocks - 1) := by omega
  have one : truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := rfl
  have allOnes : truncBits 32 (BitVec.ofInt 64 (-1)) = BitVec.ofNat 64 (2 ^ 32 - 1) := rfl
  seg_fp ht using
    simp only [remainingRescaleWord, b32, truncBits_ofNat hWord (by decide), one,
      ← BitVec.ofNat_add, hEq, truncBits_ofNat hNext (by decide), allOnes,
      compare, Option.getD_some, toNat_ofNat_lt (show 2 ^ 32 - (blocks - 1) < 2 ^ 64 by omega),
      toNat_ofNat_lt (show 2 ^ 32 - 1 < 2 ^ 64 by decide), Value.pred.injEq, decide_eq_decide]
    all_goals omega

end
end PTX.Kernels.TmlFa4Fwd.Correction
