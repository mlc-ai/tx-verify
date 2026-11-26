-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Lemmas.Flow.ScalarOut
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.MstFin

@[expose] public section

/-! # The words a lane of warpgroup 0 exchanges

The store at pc 566 (the lane's scaled row maximum) or at pc 1155 (its carried row sum) writes a
clean scalar word that reads as `w0Loc` of the words of the lane's block that closes after the
store (`hcl`: every store at pc 566 has a closing event after it), resp. as `w0ESum`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

open Wg0 Wg0.Data in
/-- A store of the exchange (pc 566 or 1155) of a lane of warpgroup 0 writes a scalar word. -/
theorem peer_word (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {h : Nat} (hh : warp L h < 4) (hv : W0Trace P X h)
    (hcl : ∀ j f, X.get (h, j) = some f → f.pc = 566 →
      ∃ K c, j < K ∧ X.get (h, K) = some c ∧ c.pc = 1122)
    {j : Nat} {f : Event} {a' : Acc} {ws : List Byte} (hf : X.get (h, j) = some f)
    (hpc : f.pc = 566 ∨ f.pc = 1155) (hk : f.kind = .wr a' ws) :
    ∃ v : Value, ws = v.toBytes ∧ Scal v ∧ Clean v ∧
      ((f.pc = 566 ∧ ∃ K0 c0, j < K0 ∧ X.get (h, K0) = some c0 ∧ c0.pc = 1122 ∧
        (w0Fin ((X.tr h).take K0)).1 = (w0Fin ((X.tr h).take j)).1 ∧
        Rd v (w0Loc P.scale (w0Words (w0Fin ((X.tr h).take K0)).2))) ∨
      (f.pc = 1155 ∧ Rd v ((w0ESum (w0MxCarry P.scale (w0Fin ((X.tr h).take j)).1)
        (w0Carry P.scale (w0Fin ((X.tr h).take j)).1).2 : ℝ) : EReal))) := by
  rcases hpc with hpc | hpc
  · obtain ⟨K, c, hjK, hK, hc⟩ := hcl j f hf hpc
    obtain ⟨K0, hj0, -, ⟨c0, hc0, hc0pc⟩, hsame, hval⟩ :=
      w0_mst_value_fin hp hX hFw hh (hv.take (K + 1)) hf hpc hK (noUb_kind hnu hK) hc hjK
    obtain ⟨v, hv1, hv2, hv3⟩ := hval a' ws hk
    exact ⟨v, hv1, hv2, hv3.1, .inl ⟨hpc, K0, c0, hj0, hc0, hc0pc, hsame, hv3⟩⟩
  · obtain ⟨v, hv1, hv2, hv3⟩ := w0_est_value hp hX hFw hh hf hpc (hv.take j) a' ws hk
    exact ⟨v, hv1, hv2, hv3.1, .inr ⟨hpc, hv3⟩⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
