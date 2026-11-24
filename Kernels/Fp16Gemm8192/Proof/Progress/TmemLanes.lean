-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.PassThread
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-! # The lanes of a Tensor Memory pair

The paired Tensor Memory operations of the kernel are made by warp 0 of the two CTAs of a cluster
(`ThreadFacts.warpOps`): the library's lanes of a pair (`Tmem.Pair.pairLane L 0`), whose `n`-th
operations are covered together (`Tmem.Pair.covered_all`), made as one collective instance
(`Tmem.Pair.tcCount_eq`), and completed by a ready step (`Tmem.Pair.pair_ready`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

/-- An execution without undefined behaviour has none in any thread. -/
theorem noUb_of {X : Execution} (hub : ¬ HasUb X) (h : Nat) :
    ∀ k pc f, X.get (h, k) ≠ some ⟨pc, .ub f⟩ :=
  fun _ _ _ he => hub ⟨_, _, _, he⟩

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
