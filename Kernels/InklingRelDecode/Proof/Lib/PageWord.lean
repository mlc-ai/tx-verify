-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.Regs

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof

/-- A word of the block table of request `z` that a block-table load reads: the page of one of
its slabs. -/
def PageWord (Q : Params) (z : Nat) (v : Value) : Prop :=
  ∃ s < 2 * Q.blocks z, v = b32 (Q.page z s)

/-- The block-table word the loop of counter `c` reads at CTA coordinate `x`: the page of slab
`2 (splits j + x) + δ` of request `z`, for the loop index `j` that `c` holds. -/
def PageAt (Q : Params) (z x δ : Nat) (c v : Value) : Prop :=
  ∃ j, c = b32 j ∧ j < 2 ^ 31 ∧ 2 * (Q.splits * j + x) + δ < 2 * Q.blocks z ∧
    v = b32 (Q.page z (2 * (Q.splits * j + x) + δ))

theorem PageAt.word {Q : Params} {z x δ : Nat} {c v : Value} (h : PageAt Q z x δ c v) :
    PageWord Q z v :=
  let ⟨_, _, _, hs, e⟩ := h
  ⟨_, hs, e⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
