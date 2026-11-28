-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockTail
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.PcBound

@[expose] public section

/-! # The epilogue's row-sum word

The load at pc 1157 is followed by pcs of at least 1178 (`w0_next_1157`), so the word the block in
progress holds as the peer's row sum (`w0EpiPe`) is the value of that load at any later event of
the epilogue, and the finished blocks are those before the load (`w0_epiPe_fin`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The peer's row-sum word at a later event**: the load at index `kp` (pc 1157), no closing event
before the event at `k`: the block's word `w0EpiPe` is the load's value and the finished blocks are
those at the load. -/
theorem w0_epiPe_fin (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hv : W0Trace P X g)
    {kp k : Nat} {f : Event} {a : Acc} {bs : List (Option Byte)}
    (hf : X.get (g, kp) = some f) (hpc : f.pc = 1157) (hk : f.kind = .rd a bs) (hkp : kp < k)
    (hKl : k < (X.tr g).length)
    (hfirst : ∀ q, kp < q → q < k → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122) :
    w0EpiPe (w0Scan ((X.tr g).take k)).2 = (rebuild 3 bs).toOption.getD (.pred false) ∧
      (w0Fin ((X.tr g).take k)).1 = (w0Fin ((X.tr g).take kp)).1 := by
  obtain ⟨ex, hexpc, hfin, hl⟩ := w0_tail hp hX hFw hw (hv.take _) hf (by omega) (by omega)
    (lo := 1178) (by omega)
    (fun e' he' hu => by
      rcases w0_next_1157 hp hX hFw hw hf hpc he' hu hv with h | h <;> omega)
    hkp hKl hfirst
  refine ⟨?_, hl⟩
  rw [← w0Fin_snd, hfin]
  unfold w0EpiPe
  rw [w0Last_ext _ _ _ _ (fun f hf => by have := hexpc f hf; simp; omega), w0Last_snoc]
  simp [hpc, w0RdVal, hk]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
