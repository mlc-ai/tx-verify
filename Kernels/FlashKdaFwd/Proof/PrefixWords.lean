-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Batches
public import Lemmas.Flow.Arith32Word

/-! Word-accurate arithmetic of the prefix loop. Offsets are narrowed independently before
subtraction. An interval may cross a 32-bit boundary, provided its length plus fifteen fits
in a signed 32-bit integer. -/
@[expose] public section
namespace FlashKda.Prefix
open PTX.Flow.Arith32
noncomputable section

theorem low_difference (lo len : Nat) (h : len < 2^32) :
    sub32 (W (lo+len)) (W lo) = W len := by
  apply BitVec.eq_of_toNat_eq
  simp only [sub32, r32, PTX.truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_sub]
  omega

/-- The actual 32-bit sub/add/div/add sequence implements one rounded-up prefix increment.
The result includes the precondition demanded by TxVerify's signed division rule. -/
theorem word_increment (start len acc : Nat) (hlen : len + 15 < 2^31)
    (hacc : acc + Batches.tiles len < 2^32) :
    let diff := sub32 (W (start+len)) (W start)
    let numer := add32 (W 15) diff
    divOk numer (W 16) = true ∧
      add32 (sdiv numer (W 16)) (W acc) = W (acc + Batches.tiles len) := by
  dsimp only
  rw [low_difference start len (by omega), add32_W (by omega), Nat.add_comm 15 len]
  obtain ⟨hq, hok⟩ := sdiv_W hlen (show 16 < 2^31 by decide) (show 0 < 16 by decide)
  refine ⟨hok, ?_⟩
  rw [hq, add32_W (by unfold Batches.tiles at hacc; omega)]
  unfold Batches.tiles
  rw [Nat.add_comm]

end
end FlashKda.Prefix
