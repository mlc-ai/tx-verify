-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RStores

@[expose] public section

/-! # The closing arrival of a finished block

A block `t` closed by a prefix (`t < w0Closed`) of lane `g` has its closing arrival at pc 1122
with the `soReady` arrivals of `t` blocks before it (`w0_block_arrive`), the premise of the
block-boundary facts (`wg0_arm`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The arrival that closes block `t`** (the lane `g`, a prefix `K` with more than `t` closed
blocks). -/
theorem w0_block_arrive (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g K t : Nat} (hw : warp L g < 4)
    (ht : t < w0Closed ((X.tr g).take K)) :
    ∃ ia l tx cnt rel sc, X.get (g, ia) = some ⟨1122, .arrive l tx cnt rel sc⟩ ∧
      w0Closed ((X.tr g).take ia) = t ∧
      ∀ b : Fin 2, arrivals (mbarLoc L (g / L.block) (.soReady b)) ((X.tr g).take ia) =
        ringUses 2 b.val t := by
  obtain ⟨ia, c, hc, hpc, hct⟩ := w0_close_idx ht
  have hlt : ia < K := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    simp only [List.length_take] at this
    omega
  have hget : X.get (g, ia) = some c := by
    rw [List.getElem?_take_of_lt hlt] at hc
    exact hc
  rw [List.take_take, Nat.min_eq_left hlt.le] at hct
  have harr := (arr_pc hp hX hFw hw hget (noUb_kind hnu hget)).1.mp hpc
  obtain ⟨pc, kd⟩ := c
  simp only at hpc
  subst hpc
  have key : ∃ l tx cnt rel sc, kd = .arrive l tx cnt rel sc := by
    cases kd <;> simp [arrivesOn, sourceArrive] at harr ⊢
  obtain ⟨l, tx, cnt, rel, sc, rfl⟩ := key
  obtain ⟨r, harr', -⟩ := wg0_arm hp hX hFw hnu hw hget
  have hrt : r = t := by
    have h1 := w0Closed_arrs hp hX hFw hw (k := ia) hnu
    unfold arrs2 at h1
    have h2 := harr' 0
    have h3 := harr' 1
    have e0 : loc L g (.soReady 0) = mbarLoc L (g / L.block) (.soReady 0) := rfl
    have e1 : loc L g (.soReady 1) = mbarLoc L (g / L.block) (.soReady 1) := rfl
    simp only [Fin.val_zero, Fin.val_one] at h2 h3
    unfold ringUses at h2 h3
    rw [e0, e1, h2, h3] at h1
    omega
  subst hrt
  exact ⟨ia, l, tx, cnt, rel, sc, hget, hct, harr'⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
