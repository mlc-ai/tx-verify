-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
public import Lemmas.Tcgen05.TmemWriters
public import Lemmas.Tcgen05.TcFence
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section

/-! # A write has a value

The kernel has no `tcgen05.cp` and no `tcgen05.shift`, so a write of a Tensor Memory cell is an
MMA result or a store. A store's value is the register it stores (`StoreValue`); the result of a
done MMA is derived (`CompletedValues`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.TcMma

variable {L : Launch} {m : Mem0} {X : Execution}

/-- **A store's value.** -/
theorem store_value (h : StoreCell L X st cell) : ∃ v, StoreValue L X st cell v := by
  obtain ⟨a, vals, sh, j, hs, hj, hc⟩ := h
  exact ⟨vals[j], a, vals, sh, j, hs, List.getElem?_eq_getElem hj, hc⟩

/-- **A write has a value**: the result of a done MMA, or the word of a store. -/
theorem wrote_of (hX : Consistent L kernel Assumptions.all m X)
    {src : EvId} {cell : Cell} (hCV : ∀ d s acc mask, X.MmaIssue src d s acc mask →
      X.MmaCell src cell → CompletedValues L Assumptions.all X src) (hw : TmemWrite L X src cell)
    (hdone : X.MmaCell src cell → X.async.mmaDone src = true) :
    ∃ value, Wrote L Assumptions.all X src cell value := by
  rcases tmemWrite_of_no_copy (Lib.no_cp hX) (no_shift hX) hw with hm | hs
  · obtain ⟨d, s, acc, mask, row, col, hi, hc⟩ := hm
    have hmc : X.MmaCell src cell := ⟨d, s, acc, mask, row, col, hi, hc⟩
    obtain ⟨v, hv⟩ := hCV d s acc mask hi hmc (hdone hmc) cell hmc
    exact ⟨v, .inl hv⟩
  · obtain ⟨v, hv⟩ := store_value hs
    exact ⟨v, .inr (.inl hv)⟩

/-- An event has one kind. -/
theorem get_tc_inj {e : EvId} {pc pc' : Nat} {k k' : TcKind}
    (h : X.get e = some ⟨pc, .tc k⟩) (h' : X.get e = some ⟨pc', .tc k'⟩) : k = k' := by
  rw [h] at h'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq] at h'
  exact h'.2

/-- **An MMA written before another MMA of another accumulator is done.** -/
theorem mma_done_of_wb (hX : Consistent L kernel Assumptions.all m X) {src r : EvId}
    {pcs pcr ds dr : Nat} {ss sr : OperandSpec} {as ar : Bool} {ms mr : List Nat}
    (hs : X.get src = some ⟨pcs, .tc (.mma ds ss as ms)⟩)
    (hr : X.get r = some ⟨pcr, .tc (.mma dr sr ar mr)⟩) (hne : ds ≠ dr)
    (h : WriteBefore L X src r) : X.async.mmaDone src = true := by
  rcases h with (hdn | hpl) | ⟨⟨a, v, sh, hst⟩, -⟩ | ⟨-, -, c, d, s, acc, mask, hcp, -⟩
  · exact hdn.done hX.tcCommit
  · obtain ⟨-, -, d1, s1, a1, m1, d2, s2, a2, m2, ⟨p1, h1⟩, ⟨p2, h2⟩, same⟩ := hpl
    have e1 := get_tc_inj hs h1
    have e2 := get_tc_inj hr h2
    simp only [TcKind.mma.injEq] at e1 e2
    exact absurd (e1.1.trans (same.1.trans e2.1.symm)) hne
  · obtain ⟨pc, hst⟩ := hst
    cases get_tc_inj hs hst
  · obtain ⟨pc, hcp⟩ := hcp
    cases get_tc_inj hs hcp

end PTX.Kernels.InklingRelDecode.Proof.Tmem
