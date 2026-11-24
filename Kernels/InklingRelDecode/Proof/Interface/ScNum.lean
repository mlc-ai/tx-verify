-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Kernels.InklingRelDecode.Proof.Interface.ShapeInput
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof2.Safety.PairRead

@[expose] public section

/-!
# `NumWordRead` from the second tree

`NumWordRead` (`ShapeWords.lean`): the loader's read of `num_iters` and the MMA warp's read of it
return the four bytes of the CTA's `num_iters`. A reader state of the first tree is a worker's
(`cls_inv`), and a worker's read of the second element of the pair returns it on the second
tree's role table (`Proof2.pair_read`: the prologue's `st9 1` of the CTA's thread 0 is before the
read through barrier 1, the softmax region's `store10` after it, at the loader's and the MMA
warp's first iteration).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem read_num_cases {bs : List (Option Byte)} {x : Nat} (hlen : bs.length = 4)
    (h : ∀ i < 4, bs[i]? = some (some (i32Byte x i))) : bs = (b32 x).toBytes.map some := by
  rw [toBytes_b32]
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, bs⟩⟩⟩⟩⟩ <;> simp at hlen
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

/-- **`NumWordRead`**, from the second tree's read of the pair (`Proof2.pair_read`). -/
theorem numWordRead_of_p2 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    NumWordRead Q L X := by
  intro g k pc a bs s hget hσ hr hloc hsz
  have hlk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  have hnotd : ¬ s.isD := by
    cases s with
    | d s => exact hr.elim
    | w s => exact fun h => h
  have hw : 128 ≤ g % L.block := by
    have := (cls_inv k s hlk.le hσ).not.mp hnotd
    omega
  have hloc' : a.loc = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4 * (1 : Fin 2).val⟩ := by
    rw [hloc]; simp
  exact Proof2.pair_read hpre hX hget hw 1 hloc' hsz

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
