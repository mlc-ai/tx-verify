-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A loaded word keeps each finite BF16 payload. Two raw mask encodings assemble as bits. -/
def biasLoadWord (lo hi : Option ℝ) : Value :=
  match lo, hi with
  | none, none => b32 0xFF80FF80
  | _, _ => .pair (biasValue lo) (biasValue hi)

/-- Rebuilding a shared word from the original scalar bytes preserves their BF16 representation. -/
theorem rebuildBiasLoadWord (lo hi : Option ℝ) :
    rebuild 3 (((biasValue lo).toBytes ++ (biasValue hi).toBytes).map some) =
      .ok (biasLoadWord lo hi) := by
  have bytes (x : Option ℝ) : (biasValue x).toBytes = [(biasValue x, 0), (biasValue x, 1)] := by
    cases x <;> rfl
  rw [bytes lo, bytes hi]
  cases lo <;> cases hi <;>
    simp [biasLoadWord, biasValue, rebuild, rebuild.halves, Value.toBytes, Value.bytes,
      Value.byteAt, FloatFmt.bytes, intByte, List.range_succ, rebuildBits, littleEndianBits,
      byteBits, Value.bitPattern, bind, Option.bind, Except.bind, pure, Except.pure, b32]

theorem splitBiasLoadWord (lo hi : Option ℝ) :
    splitValue 32 (biasLoadWord lo hi) = (biasValue lo, biasValue hi) := by
  cases lo <;> cases hi <;> rfl

theorem biasLoadWordShape (lo hi : Option ℝ) : BiasWordShape (biasLoadWord lo hi) := by
  refine ⟨?_, ?_⟩
  · cases lo <;> cases hi <;> rfl
  · rw [splitBiasLoadWord]
    constructor <;> first | cases lo <;> rfl | cases hi <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Softmax
