-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.PcBound

@[expose] public section

/-! # The events of a block after one of its events

The events of the block in progress after the event at index `j` up to the index `K0`, no event
at pc 1122 between: all at pcs at least `lo` when the event after `j` is (`w0_tail`), so the block
at `K0` is the block at `j` with the event and these appended, and its finished blocks are those
at `j`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The tail of a block**: `ex` the events of the prefix of length `K0` after the event `e` at
index `j` (pc 201 or more, not at 1122), no event at pc 1122 up to `K0`, the event after `e` at
pc `lo` or more. -/
theorem w0_tail (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4)
    {j K0 lo : Nat} (hv : W0Valid P.scale ((X.tr g).take K0)) {e : Event}
    (he : X.get (g, j) = some e) (hge : 201 ≤ e.pc) (he1 : e.pc ≠ 1122) (hlo : 201 ≤ lo)
    (hnext : ∀ e', X.get (g, j + 1) = some e' → (∀ u, e'.kind ≠ .ub u) → lo ≤ e'.pc) (hjK : j < K0)
    (hK : K0 < (X.tr g).length)
    (hfirst : ∀ q, j < q → q < K0 → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122) :
    ∃ ex, (∀ f ∈ ex, lo ≤ f.pc ∧ f.pc ≠ 1122) ∧
      (w0Fin ((X.tr g).take K0)).2 = (w0Fin ((X.tr g).take j)).2 ++ [e] ++ ex ∧
      (w0Fin ((X.tr g).take K0)).1 = (w0Fin ((X.tr g).take j)).1 := by
  set ex := ((X.tr g).take K0).drop (j + 1) with hex
  have hexpc : ∀ f ∈ ex, lo ≤ f.pc ∧ f.pc ≠ 1122 := by
    intro f hf
    obtain ⟨q, hq, hqf⟩ := List.mem_iff_getElem.mp hf
    have hq0 := hq
    simp only [hex, List.length_drop, List.length_take] at hq
    have hlt : j + 1 + q < K0 := by omega
    have hget : X.get (g, j + 1 + q) = some f := by
      have h1 : (ex)[q]? = some f := by rw [List.getElem?_eq_getElem hq0, hqf]
      rw [hex, List.getElem?_drop, List.getElem?_take_of_lt hlt] at h1
      exact h1
    have hlt1 : j + 1 < (X.tr g).length := by omega
    obtain ⟨e', he'⟩ : ∃ e', X.get (g, j + 1) = some e' :=
      ⟨_, (List.getElem?_eq_getElem hlt1 : (X.tr g)[j + 1]? = _)⟩
    have hl := hnext e' he' (noUb_kind_of_lt hX he' (by omega) hK)
    have hm := w0_pc_mono hp hX hFw hw hv q (by omega) he' hget
      (noUb_kind_of_lt hX hget hlt hK) (by omega)
      (fun q' hq' ev hev => hfirst (j + 1 + q') (by omega) (by omega) ev hev)
    exact ⟨by omega, hfirst _ (by omega) hlt f hget⟩
  have htk : (X.tr g).take K0 = (X.tr g).take j ++ [e] ++ ex := by
    have h1 : ((X.tr g).take K0).take (j + 1) = (X.tr g).take (j + 1) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have h2 : (X.tr g).take (j + 1) = (X.tr g).take j ++ [e] := by
      have : (X.tr g)[j]? = some e := he
      rw [List.take_add_one, this]; rfl
    conv_lhs => rw [← List.take_append_drop (j + 1) ((X.tr g).take K0), h1, h2]
  have he2 : e.pc ≠ w0ArrLPc := by unfold w0ArrLPc; omega
  have he3 : e.pc ≠ w0ArrSPc := by unfold w0ArrSPc; exact he1
  have hext : ∀ f ∈ ex, f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc := fun f hf => by
    have := hexpc f hf
    unfold w0ArrSPc w0ArrLPc
    omega
  refine ⟨ex, hexpc, ?_, ?_⟩
  · rw [htk, w0Fin_ext _ _ hext, w0Fin_snoc_snd _ _ he3]
  · rw [htk, w0Fin_ext _ _ hext, w0Fin_snoc]
    simp [he3, he2]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
