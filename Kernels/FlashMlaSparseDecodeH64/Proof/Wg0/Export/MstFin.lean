-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Lemmas.Flow.ScalarOut
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt

@[expose] public section

/-! # The stored maximum of a block that closes

A store at pc 566 of a lane of warpgroup 0 that is followed by a closing event of its block (the
arrival at pc 1122) writes the lane's scaled maximum `w0Loc` of the words of the block that
closes, whatever the lane's later events are: the events between the store and the first closing
event are at pcs between 566 and 1121 (`w0_pc_mono`), and the closed block's words are valid
(`W0Valid`). The word is scalar. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The row maximum of a block that closes**: the store at pc 566 at index `j`, with a closing
event at index `K` after it, writes a scalar word that reads as `w0Loc` of the words of the block
in progress before the first closing event (index `K0`, `j < K0`). -/
theorem w0_mst_value_fin (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j K : Nat}
    (hv : W0Valid P.scale ((X.tr g).take (K + 1))) {e c : Event} (he : X.get (g, j) = some e)
    (hpc : e.pc = 566) (hK : X.get (g, K) = some c)
    (hcu : ∀ u, c.kind ≠ .ub u) (hc : c.pc = 1122) (hjK : j < K) :
    ∃ K0, j < K0 ∧ K0 ≤ K ∧ (∃ c0, X.get (g, K0) = some c0 ∧ c0.pc = 1122) ∧
      (w0Fin ((X.tr g).take K0)).1 = (w0Fin ((X.tr g).take j)).1 ∧
      ∀ a bs, e.kind = .wr a bs → ∃ v : Value, bs = v.toBytes ∧ Scal v ∧
        Rd v (w0Loc P.scale (w0Words (w0Fin ((X.tr g).take K0)).2)) := by
  have hex : ∃ n, ∃ ev, X.get (g, j + 1 + n) = some ev ∧ ev.pc = 1122 :=
    ⟨K - (j + 1), c, by rw [show j + 1 + (K - (j + 1)) = K by omega]; exact hK, hc⟩
  classical
  let n0 := Nat.find hex
  obtain ⟨c0, hc0, hc0pc⟩ := Nat.find_spec hex
  have hmin : ∀ q < n0, ∀ ev, X.get (g, j + 1 + q) = some ev → ev.pc ≠ 1122 :=
    fun q hq ev hev h => Nat.find_min hex hq ⟨ev, hev, h⟩
  have hn0 : n0 ≤ K - (j + 1) := Nat.find_min' hex ⟨c, by
    rw [show j + 1 + (K - (j + 1)) = K by omega]; exact hK, hc⟩
  set K0 := j + 1 + n0 with hK0
  have hno : ∀ q < K0 - j, ∀ ev, X.get (g, j + q) = some ev → ev.pc ≠ 1122 := by
    intro q hq ev hev
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [Nat.add_zero, he] at hev
      cases hev
      rw [hpc]; decide
    · have := hmin (q - 1) (by omega) ev (by rw [show j + 1 + (q - 1) = j + q by omega]; exact hev)
      exact this
  have hge : 103 ≤ e.pc := by omega
  have hKl : K < (X.tr g).length := (List.getElem?_eq_some_iff.mp hK).1
  have hub0 : ∀ u, c0.kind ≠ .ub u := by
    by_cases hKK : K0 = K
    · obtain rfl : c0 = c := by rw [hKK, hK] at hc0; exact (Option.some.inj hc0).symm
      exact hcu
    · exact noUb_kind_of_lt hX hc0 (by omega) hKl
  have hmid : ∀ f ∈ ((X.tr g).take K0).drop j, 566 ≤ f.pc ∧ f.pc < 1122 := by
    intro f hf
    obtain ⟨q, hq, hqf⟩ := List.mem_iff_getElem.mp hf
    have hq0 := hq
    simp only [List.length_drop, List.length_take] at hq
    have hqK : j + q < K0 := by omega
    have hget : X.get (g, j + q) = some f := by
      have h1 : (((X.tr g).take K0).drop j)[q]? = some f := by
        rw [List.getElem?_eq_getElem hq0, hqf]
      rw [List.getElem?_drop, List.getElem?_take] at h1
      have h2 : (X.tr g)[j + q]? = some f := by simpa [hqK, Nat.add_comm] using h1
      exact h2
    have h1 := w0_pc_mono hp hX hFw hw hv q (by omega) he hget
      (noUb_kind_of_lt hX hget (by omega) hKl) hge
      (fun q' hq' ev hev => hno q' (by omega) ev hev)
    have h2 := w0_pc_mono hp hX hFw hw hv (K0 - (j + q)) (by omega) hget
      (by rw [show j + q + (K0 - (j + q)) = K0 by omega]; exact hc0) hub0 (by omega)
      (fun q' hq' ev hev => hno (q + q') (by omega) ev (by
        rw [show j + (q + q') = j + q + q' by omega]; exact hev))
    have h3 : f.pc ≠ 1122 := hno q (by omega) f hget
    omega
  have hpre : (X.tr g).take (K0 + 1) = (X.tr g).take K0 ++ [c0] := by
    have : (X.tr g)[K0]? = some c0 := hc0
    rw [List.take_add_one, this]; rfl
  have hfin : w0Fin ((X.tr g).take K0 ++ [c0]) =
      ((w0Fin ((X.tr g).take K0)).1 ++ [(w0Fin ((X.tr g).take K0)).2], []) := by
    rw [w0Fin_snoc]; simp [hc0pc, w0ArrSPc]
  have hwok : W0Ok P.scale (w0Words (w0Fin ((X.tr g).take K0)).2) := by
    have hvK := W0Valid.take_le hv (m := K0 + 1) (by omega)
    rw [hpre] at hvK
    exact hvK.now.1 _ (by rw [hfin]; simp)
  have hsame : (w0Fin ((X.tr g).take K0)).1 = (w0Fin ((X.tr g).take j)).1 := by
    have h0 : ((X.tr g).take K0).take j = (X.tr g).take j := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have h1 : (X.tr g).take K0 = (X.tr g).take j ++ ((X.tr g).take K0).drop j := by
      conv_lhs => rw [← List.take_append_drop j ((X.tr g).take K0), h0]
    rw [h1, w0Fin_ext _ _ (fun f hf => by
      have := hmid f hf
      unfold w0ArrSPc w0ArrLPc
      omega)]
  refine ⟨K0, by omega, by omega, ⟨c0, hc0, hc0pc⟩, hsame, ?_⟩
  exact w0_mst_value hp hX hFw hw he hpc (by omega) hmid
    (W0Valid.take_le hv (m := j) (by omega)) hwok
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
