-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProASound
public import Lemmas.Flow.SignedBits

@[expose] public section

/-! # What the prologue's exit facts mean

`exitFacts L g dt` (`ProASound`) are the registers live at pc 574 valued by the table of the data
`dt` the thread holds at `barrier.sync 1`. This file states what some of them are, and records
every premise the protocol layer must discharge for this region.

## Premises of the region (what `Pre` / the protocol layer must supply)

* `ArgsOk L g P` (`ProADefs`), for the thread's inherited registers `P`: the thread is in the
  default partition (`g % block < 128`); `0 < num_splits < 2 ^ 31` (`Pre.splitsPos`,
  `Pre.splitsRange`) and `ctaid.x < num_splits` (`Pre.gridShape`); the parameter words read by pc
  20 to 26 and 316 to 318 are the launch's (`Pre.paramQ`, `paramRel`, `paramSeq`, `paramCu`,
  `paramO`, `paramLse`, `paramScale`, `paramStrideQ`, `paramStrideRel`, `paramNTok`); `%r67 … %r71`,
  `%rd72`, `%r2` (`tm`), `%r1`, `%r3` are the inherited registers `Inh` names (the common code's
  facts at pc 20).
* The three loaded words are single 32-bit words (`word32`: `Pre.cuInput`, `Pre.seqInput` give
  `i32Byte`, whose rebuild is `b32`) and satisfy `WordsOk` (`ProANext`): `cu0 ≤ cu1 < 2 ^ 31`,
  `cu1 - cu0 ≤ seq_lens`, `seq_lens + 255 < 2 ^ 31` (`Pre.cuMono`, `qLenSeq`, `seqRange`), and the
  numerators of the two signed divisions, the registers `%r176 = num_splits - 1 - split +
  ⌈seq_lens / 128⌉` and `%r217 = num_splits - 1 - split + ⌊past / 128⌋`, are non-negative 32-bit
  signed words. `Pre` does not imply the last: it needs `num_splits + ⌈seq_lens / 128⌉ < 2 ^ 31`
  (`Pre.splitsRange` only gives `num_splits < 2 ^ 31`), so the protocol layer must add that bound
  to `Pre` (or the machine leaves the region on such a launch).
* Each block-table word (`word32`) is `i32Byte (page r s)` (`Pre.btInput`); each query load
  returns a two-byte value (`Pre.qInput` gives `Value.float .bf16 _`, whose bytes are 2); the
  machine records them in `Dat.q` without interpreting them.
* The shuffles return the warp index (`recv = b32 (tid / 32)`), as in the other roles.
* Not proved here: the protocol facts about the events (what the tensor copies, the mbarrier
  initializations, `expect_tx`, the Q stores and `(num_pre, num_iters)` write mean), and the closed
  forms of the registers computed through the signed divisions and the `max` (`%r22 … %r26`,
  `%r32`): `Dat`-level values of `exitFacts` are the table's terms `v_r22 …` (unfolded in
  `ProATable`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The registers live at pc 574. -/
theorem exitRegs : Flow.live Flow.setMaxReg_1 = [3, 177, 199, 462, 463, 464, 478, 481, 482,
    483, 484, 485, 486, 487, 490, 491, 525, 527, 532, 533, 610, 623, 624, 666, 792, 1912, 2019,
    2023, 2024] := by
  decide +kernel

/-- `%r1451 = ctaid.x << 7`. -/
theorem r1451_eq (L : Launch) (g : Nat) (dt : Dat) :
    truncBits 32 (v_r1451 L g dt) = BitVec.ofNat 64 (cta L g .x % 2 ^ 32 * 128 % 2 ^ 32) := by
  simp only [v_r1451, v_r17, wCta, wShl32, cta]
  generalize (L.ctaidOf (g / L.block)).get Dim.x = x
  norm_signed

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
