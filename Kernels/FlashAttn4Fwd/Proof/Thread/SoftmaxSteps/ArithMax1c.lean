-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax1Facts

@[expose] public section

/-! # A loop tile's row maximum: the address of the statistics word

After the lazy rescale, the address of the thread's statistics word (`alpha_addr`), to the store
of `α`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem segMax1_addr {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (d : D) :
    Seg kernel asms L g 4 2935 (factsAt L g 2935 { d with site := .alphaSt }) 2939
      (factsAt L g 2939 { d with site := .alphaSt }) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have htid : tidOf L g < 512 := hpre.block ▸ Nat.mod_lt _ (by rw [hpre.block]; decide)
  intro t h
  ar_seg_with h [] using exact alpha_addr _ _ htid hbase

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
