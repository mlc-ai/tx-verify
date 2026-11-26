-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Flow.ScalarOut
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiValue

@[expose] public section

/-! # The words of the exchange stores, for the upper modules

`w0_mst_valueW` and `w0_est_value` of `EpiValue` with its role internals kept behind a private
import. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The word of the exchange store** (valid rows): see `w0_mst_valueW`. -/
theorem w0_mst_word (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 566)
    (hv : W0Valid P.scale ((X.tr g).take k)) {w : W0Words} (hwok : W0Ok P.scale w)
    (hhi : (w0Words (w0Fin ((X.tr g).take k)).2).hi = w.hi)
    (hmw : (w0Words (w0Fin ((X.tr g).take k)).2).mw = w.mw)
    (hpw : ∀ j, (w0Words (w0Fin ((X.tr g).take k)).2).pw j = w.pw j) :
    ∀ a bs, e.kind = .wr a bs → ∃ v : Value, bs = v.toBytes ∧ Scal v ∧ SK.ni.Has v := by
  intro a bs hk
  obtain ⟨v, h1, h2, -, h4⟩ := w0_mst_valueW hp hX hFw hw he hpc hv hwok hhi hmw hpw a bs hk
  exact ⟨v, h1, h2, h4⟩

/-- **The word of the row-sum store** (valid rows): see `w0_est_value`. -/
theorem w0_est_word (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 1155)
    (hv : W0Valid P.scale ((X.tr g).take k)) :
    ∀ a bs, e.kind = .wr a bs → ∃ v : Value, bs = v.toBytes ∧ Scal v ∧
      Rd v ((w0ESum (w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1)
        (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2 : ℝ) : EReal) :=
  w0_est_value hp hX hFw hw he hpc hv

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
