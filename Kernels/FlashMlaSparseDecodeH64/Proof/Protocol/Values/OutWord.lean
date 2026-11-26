-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Bot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Out
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.LseSum
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxSum
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiFree
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen

@[expose] public section

/-! # The words a lane stages are the reference's output

At a staging store `ost2 c j` of a lane of warpgroup 0 (valid rows, complete), the bytes it writes
are the bf16 pair of two columns of the lane's output row (`w0_out_word`): the accumulator word
of a column (`OutRead`: `O 2 ^ m` is the numerator) times the epilogue's factor
(`w0_ost2_value_free`, with the peer's row sum of `rmax_peer_sum`) is the Spec's `attn`
(`w0Fac_attn`: the pair's sums give the row sum, `w0_row_sum`). -/

/-! # The pair's carried sums are the row sum, for either lane of the pair

`w0_pair_sum` takes the lane below thread 64. A lane of the upper half is the partner of one
below it, and the pair's sum is symmetric: `w0_row_sum` states it for every lane of warpgroup 0. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The partner of a lane is in the same row: same batch, query and head. -/
theorem w0Partner_row (hp : Pre P L m) {g : Nat} (hw : warp L g < 4) (hg : g < L.threads) :
    w0Batch L (w0Partner L g) = w0Batch L g ∧ w0Query L (w0Partner L g) = w0Query L g ∧
      w0Head L (w0Partner L g) = w0Head L g := by
  obtain ⟨-, -, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  have hx := tidOf_x_eq hp g
  have hxp := tidOf_x_eq hp (w0Partner L g)
  have hb : L.block = 384 := by have := hp.block; omega
  have hlt : g % 384 < 128 := by
    simp only [warp, tidOf_x_eq hp] at hw
    omega
  have hxor := xor64_of_lt (g % 384) hlt
  refine ⟨by unfold w0Batch; rw [hdiv], by unfold w0Query; rw [hdiv], ?_⟩
  unfold w0Head
  rw [hxp, hx, ← hb, hmod, hb, hxor]
  split_ifs <;> omega

/-- **The pair's carried sums are the row sum** (valid rows, complete), for any lane of
warpgroup 0 with its row-sum read at `kp` and its partner's at `kq`: the carried maxima agree and
`(l + l') 2 ^ m` is the row sum. -/
theorem w0_row_sum (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) (hC : Complete L X)
    (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV) {g kp kq : Nat}
    {f e' : Event} (hw : warp L g < 4) (hg : g < L.threads)
    (hf : X.get (g, kp) = some f) (hf1157 : f.pc = 1157)
    (he' : X.get (w0Partner L g, kq) = some e') (hpc' : e'.pc = 1157)
    (hn : (w0Fin ((X.tr g).take kp)).1.length = blocksOf P L (g / L.block))
    (hn' : (w0Fin ((X.tr (w0Partner L g)).take kq)).1.length = blocksOf P L (g / L.block)) :
    (w0Carry P.scale (w0Fin ((X.tr g).take kp)).1).1 =
        (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1).1 ∧
      ((w0Carry P.scale (w0Fin ((X.tr g).take kp)).1).2 +
          (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1).2) *
        (2 : ℝ) ^ (w0Carry P.scale (w0Fin ((X.tr g).take kp)).1).1 =
      rowSum P (w0Batch L g) (w0Query L g) (w0Head L g) := by
  by_cases hlow : tidOf L g < 64
  · exact w0_pair_sum hp hX hFw hnu hR hC hV hS hM hw hg hlow hf hf1157 he' hpc' hn hn'
  obtain ⟨-, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  have hpp := w0Partner_partner hp hw hg
  have hgh : w0Partner L g < L.threads := by
    have hb : L.block = 384 := by have := hp.block; omega
    have := Frame.lt_of_get hX he'
    exact this
  have hlow' : tidOf L (w0Partner L g) < 64 := by
    have hx := tidOf_x_eq hp g
    have hxp := tidOf_x_eq hp (w0Partner L g)
    have hb : L.block = 384 := by have := hp.block; omega
    have hlt : g % 384 < 128 := by
      simp only [warp, tidOf_x_eq hp] at hw
      omega
    have hxor := xor64_of_lt (g % 384) hlt
    have hg64 : ¬ g % 384 < 64 := by simp only [tidOf, hx] at hlow; exact hlow
    simp only [tidOf, hxp]
    rw [← hb, hmod, hb, hxor]
    simp only [hg64, ↓reduceIte]
    omega
  have hpf : X.get (w0Partner L (w0Partner L g), kp) = some f := by rw [hpp]; exact hf
  obtain ⟨hag, hsum⟩ := w0_pair_sum hp hX hFw hnu hR hC hV hS hM hwh hgh hlow' he' hpc' hpf
    hf1157 (by rw [hdiv]; exact hn') (by rw [hpp, hdiv]; exact hn)
  rw [hpp] at hag hsum
  obtain ⟨hb1, hq1, hh1⟩ := w0Partner_row hp hw hg
  rw [hb1, hq1, hh1] at hsum
  refine ⟨hag.symm, ?_⟩
  rw [← hsum, add_comm, ← hag]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The sink word's weight: the Spec's `sinkWeight` for the reading `w0SinkE`. -/
theorem w0SinkE_weight (P : Params) (h : Nat) :
    (w0SinkE P h = ⊥ ∧ sinkWeight P h = 0) ∨
      ∃ x : ℝ, w0SinkE P h = (x : EReal) ∧ sinkWeight P h = (2 : ℝ) ^ x := by
  unfold w0SinkE sinkWeight
  rcases P.sink h with _ | s
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨_, rfl, rfl⟩

/-- **The numerator of a column** from the finished blocks' sum (all the CTA's blocks). -/
theorem w0_numerator (hp : Pre P L m) {g : Nat} {l : List (List Event)} (d : Nat)
    (hn : l.length = blocksOf P L (g / L.block)) :
    ∑ t ∈ Finset.range l.length, ∑ j' ∈ Finset.range 64,
      weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) t)
          (w0BlockSlot P (w0Batch L g) t j') *
        slotValue P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) t)
          (w0BlockSlot P (w0Batch L g) t j') d =
      numerator P (w0Batch L g) (w0Query L g) (w0Head L g) d := by
  obtain ⟨-, -, -, htopk, hextra⟩ := len_words hp (g / L.block)
  have hrow : rowOf L (g / L.block) = w0Batch L g := rfl
  rw [hrow] at htopk hextra
  rw [← Result.sum_blockWeight_mul_value_eq_numerator P _ (w0Query L g) (w0Head L g) d htopk hextra,
    hn, blocksOf_eq hp, hrow]
  simp only [Result.blockWeight, Result.blockValue, w0BlockExtra_eq, w0BlockSlot_eq,
    Result.topkBlock]

/-- **The staging stores' bytes** (valid rows, complete): the store `ost2 c j` of a lane of
warpgroup 0 writes the bf16 pair of the Spec's `attn` at the output columns
`128 half + off c + 2 (4 j + q)` and the next, at the word `q` of the store's place. -/
theorem w0_out_word (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) (hC : Complete L X)
    (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV)
    (hOR : OutRead P L X hV) {g k : Nat} {e : Event} {c : Fin 4} {j : Fin 8}
    (hw : warp L g < 4) (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hpc : e.pc = Wg0.ost2Base c + j.val) :
    ∀ a bs, e.kind = .wr a bs → ∃ q < 4, a.size = 4 ∧ a.loc = wsLoc L (g / L.block)
        (65536 + 16384 * (tidOf L g / 64) + 128 * (tidOf L g % 64) +
          16 * (j.val ^^^ tidOf L g % 8) + MemRow.wg0OutOff c.val + 4 * q) ∧
      bs = (Assumptions.bf16Pair
        (attn P (w0Batch L g) (w0Query L g) (w0Head L g)
          (128 * w0Half L g + [0, 64, 256, 320].getD c.val 0 + 2 * (4 * j.val + q)))
        (attn P (w0Batch L g) (w0Query L g) (w0Head L g)
          (128 * w0Half L g + [0, 64, 256, 320].getD c.val 0 + (2 * (4 * j.val + q) + 1)))).toBytes
      := by
  intro a bs hk
  have hvg := w0Trace_of_rows hV hX hw
  obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
  have hvh := w0Trace_of_rows hV hX hwh
  have hjl := j.isLt
  have hpcr : 1157 < e.pc ∧ e.pc < 1840 := by
    rw [hpc]
    fin_cases c <;> simp only [Wg0.ost2Base, List.getD_cons_zero, List.getD_cons_succ] <;> omega
  obtain ⟨kp, f, a', bs', rP, kq, e', hf, hf1157, hfk, hkp, hfirst, he', hpc', hlenq, hrd,
    hcarL, hcarQ, hlenL⟩ := rmax_peer_sum hp hX hFw hnu hR hw hvg hvh hC he hpcr.1 hpcr.2
  have hKl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hlen, hsk, hOi⟩ := hOR g k e c j hg he hpc
  choose! O hOrd hOeq using hOi
  have hfin := w0_fin_epi hp hX hFw hw hvg hf hf1157 hfk hkp hKl hfirst
  have hlenp := w0_len_epi hp hX hFw hw hf (noUb_kind hnu hf) (Or.inr hf1157)
  have hbytes := w0_ost2_value_free hp hX hFw hw hvg he hpc hsk hlen hOrd hf hf1157 hfk hkp
    hfirst (w0Carry_nonneg _ _) hrd hcarL a bs hk
  obtain ⟨hag, hsum⟩ := w0_row_sum hp hX hFw hnu hR hC hV hS hM hw hg hf hf1157 he' hpc' hlenp
    hlenq
  rw [← hfin] at hsum hag
  have hbot : rP = ⊥ → rowSum P (w0Batch L g) (w0Query L g) (w0Head L g) = 0 := by
    intro hb
    rw [← hsum, add_mul, hag]
    have h1 := w0Carry_sum P.scale (w0Fin ((X.tr g).take k)).1
    have h2 := w0Carry_sum P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1
    rw [hag] at h1
    have hsc : 0 < P.scale := hp.scalePos
    rw [h1, h2, w0MxCarry_bot hsc _ (hcarL.trans hb), w0MxCarry_bot hsc _ (hcarQ.trans hb)]
    simp
  have hcol : ∀ i < 64, O i * w0EpiF P.scale ((X.tr g).take k)
      (w0ESum rP (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1).2)
      (w0SinkE P (w0Head L g)) =
      attn P (w0Batch L g) (w0Query L g) (w0Head L g)
        (128 * w0Half L g + [0, 64, 256, 320].getD c.val 0 + i) := by
    intro i hi
    have hN := (hOeq i hi).trans (w0_numerator hp _ (hfin ▸ hlenL))
    unfold w0EpiF
    rw [hcarL]
    have := w0Fac_attn (r := rP) (sk := w0SinkE P (w0Head L g)) (m := (w0Carry P.scale
      (w0Fin ((X.tr g).take k)).1).1) (w0Carry_nonneg _ _) (w0Carry_nonneg _ _) hsum hbot hN
      (w0SinkE_weight P (w0Head L g))
    rw [this]
    unfold attn
    rfl
  obtain ⟨q, hq, hsz, hloc, hb⟩ := hbytes
  refine ⟨q, hq, hsz, hloc, ?_⟩
  rw [hb, hcol _ (by omega), hcol _ (by omega)]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
