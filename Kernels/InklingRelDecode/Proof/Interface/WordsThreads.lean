-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ShapeWordsKeep

@[expose] public section

/-! # The thread-layer module the proof of `ProWordsMatch` reads

The successor of the prologue's three request-word loads and the invariance of the loaded words
(`ProA.next_ldCu0`, `next_ldCu1`, `next_ldSk`, `keeps_next`, `afterSk_next`). The protocol layer
(`Mbar/Words`) imports them through this module. -/
