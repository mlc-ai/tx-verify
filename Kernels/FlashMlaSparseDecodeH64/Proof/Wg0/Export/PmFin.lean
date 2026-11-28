-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockTail
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.PcBound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase

@[expose] public section

/-! # The partner's maximum a closed block holds

The exchange load at pc 572 of a block is the last event at pc 572 of the block in progress up to
its closing event (the arrival at pc 1122): after it the next event is at pc 578 and the pcs do not
fall (`w0_pc_mono`), so no later event of the block is at pc 572. The block's word `pm`
(`w0Words`) is therefore the value that load read. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The word `pm` of a closed block is the value of its exchange load**: the load at index `j`
(pc 572), the event `c0` at `K0 > j` closing the block (no event at pc 1122 between). -/
theorem w0_pm_fin (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j K0 : Nat}
    (hv : W0Valid P.scale ((X.tr g).take K0)) {e c0 : Event} {a : Acc}
    {bs : List (Option Byte)} (he : X.get (g, j) = some e)
    (hpc : e.pc = 572) (hk : e.kind = .rd a bs) (hK : X.get (g, K0) = some c0)
    (hjK : j < K0)
    (hfirst : ∀ q, j < q → q < K0 → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122) :
    (w0Words (w0Fin ((X.tr g).take K0)).2).pm = (rebuild 3 bs).toOption.getD (.pred false) := by
  have hKl : K0 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hK).1
  obtain ⟨ex, hexpc, hfin, -⟩ := w0_tail hp hX hFw hw hv he (by omega) (by omega)
    (lo := 578) (by omega) (fun e' he' hu =>
      (w0_next_572 hp hX hFw hw he hpc he' hu (W0Valid.take_le hv (by omega))).ge) hjK hKl
    hfirst
  simp only [w0Words]
  rw [hfin, w0Last_ext _ _ _ _ (fun f hf => by have := hexpc f hf; simp; omega), w0Last_snoc]
  simp [hpc, w0RdVal, hk]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
