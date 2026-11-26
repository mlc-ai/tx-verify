-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.LseSum
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Lse
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Bot
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxSum
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiFree
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.LseExist
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList

@[expose] public section

/-! # The LSE word a lane stores is its row's

A complete lane `g` of warpgroup 0 below thread 64 makes its LSE store (pc 1178), and the bytes it
writes are the word of the epilogue (`w0_lse_value_free`) from the lane's carried statistics and
the partner's carried sum (`rmax_peer_sum`). With the pair's weights the row sum (`w0_pair_sum`)
the word is `+inf` for an empty row and the Spec's `lse` otherwise (`w0LseV_row`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The LSE store of a lane** (valid rows, complete): lane `g` below thread 64 stores at pc 1178
the `+inf` word if its row's sum is zero, and the Spec's `lse` otherwise. -/
theorem w0_lse_row (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) (hC : Complete L X)
    (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV) {g : Nat}
    (hw : warp L g < 4) (hg : g < L.threads) (hlow : tidOf L g < 64) :
    ∃ k a bs, X.get (g, k) = some ⟨1178, .wr a bs⟩ ∧
      ((rowSum P (w0Batch L g) (w0Query L g) (w0Head L g) = 0 ∧
        bs = (Value.bits 32 (BitVec.ofNat 64 2139095040)).toBytes) ∨
      (rowSum P (w0Batch L g) (w0Query L g) (w0Head L g) ≠ 0 ∧
        bs = (Value.float .f32 (lse P (w0Batch L g) (w0Query L g) (w0Head L g))).toBytes)) := by
  obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
  have hvg := w0Trace_of_rows hV hX hw
  have hvh := w0Trace_of_rows hV hX hwh
  obtain ⟨k, a, bs, hk⟩ := w0_lse_exists hp hX hFw hnu hw hvg hlow hC hg
  obtain ⟨kp, f, a', bs', rP, kq, e', hf, hf1157, hfk, hkp, hfirst, he', hpc', hlenq, hrd,
    hcarL, hcarQ, hlenL⟩ := rmax_peer_sum hp hX hFw hnu hR hw hvg hvh hC hk (by simp) (by simp)
  have hKl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hk).1
  have hfinEq := w0_fin_epi hp hX hFw hw hvg hf hf1157 hfk hkp hKl hfirst
  have hlenp := w0_len_epi hp hX hFw hw hf (noUb_kind hnu hf) (Or.inr hf1157)
  have hbytes := w0_lse_value_free hp hX hFw hw hvg hk rfl hf hf1157 hfk hkp hfirst
    (w0Carry_nonneg _ _) hrd a bs rfl
  have hpair := w0_pair_sum hp hX hFw hnu hR hC hV hS hM hw hg hlow hf hf1157 he' hpc' hlenp
    hlenq
  rw [← hfinEq] at hpair
  obtain ⟨hag, hsum⟩ := hpair
  refine ⟨k, a, bs, hk, ?_⟩
  rw [hbytes]
  unfold w0EpiLse
  rw [hcarL]
  have hbot : rP = ⊥ → rowSum P (w0Batch L g) (w0Query L g) (w0Head L g) = 0 := by
    intro hb
    rw [← hsum, add_mul, hag]
    have h1 := w0Carry_sum P.scale (w0Fin ((X.tr g).take k)).1
    have h2 := w0Carry_sum P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1
    rw [hag] at h1
    have hsc : 0 < P.scale := hp.scalePos
    rw [h1, h2, w0MxCarry_bot hsc _ (hcarL.trans hb), w0MxCarry_bot hsc _ (hcarQ.trans hb)]
    simp
  have := w0LseV_row (r := rP) (w0Carry_nonneg P.scale (w0Fin ((X.tr g).take k)).1)
    (w0Carry_nonneg P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1) hsum hbot
  rcases this with ⟨h0, hv⟩ | ⟨h0, hv⟩
  · left
    exact ⟨h0, by rw [hv]⟩
  · right
    exact ⟨h0, by rw [hv]; rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
