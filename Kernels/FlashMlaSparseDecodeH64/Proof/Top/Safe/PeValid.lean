-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PeCarry
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TcSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.MstWord
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxRead

@[expose] public section

/-! # The row-sum load keeps warpgroup 0's trace valid

The load at pc 1157 of lane `g` reads the word the partner's row-sum store at pc 1155 wrote
(`rmax_read_bytes`, with the partner's valid prefixes below the load): that word reads as
`w0ESum` of the partner's carried statistics (`w0_est_word`), which is nonnegative, and zero when
the lane's own true maximum is `-inf`, as the partner's carried maximum is the lane's
(`w0_carry_eq`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The word of the row-sum load** (valid rows): it reads as `p`, with `0 ≤ p`, and `p = 0`
while the lane's true maximum is `-inf`. -/
theorem w0_pe_payload (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {a : Acc} {bs : List (Option Byte)} (hw : warp L g < 4)
    (he : X.get (g, k) = some ⟨1157, .rd a bs⟩) (hv : W0Valid P.scale ((X.tr g).take k))
    (hU : W0Under P L X g k) :
    ∃ (v : Value) (p : ℝ), rebuild 3 bs = .ok v ∧ 0 ≤ p ∧ Rd v p ∧
      (w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1 = ⊥ → p = 0) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hwh, hdiv, -⟩ := w0Partner_facts hp hw hg
  have hub : ∀ u, (⟨1157, .rd a bs⟩ : Event).kind ≠ .ub u := fun _ h => by cases h
  have hcnt := w0_cnt_exch hp hX hFw hw he hub (Or.inr rfl)
  have hlx := w0_len_epi hp hX hFw hw he hub (Or.inr rfl)
  have hbelow : W0Below P L X (w0Partner L g) g k := fun j f hf htc =>
    ⟨hU _ j f hf hwh htc, tcTrans_nonUb hX htc hf⟩
  have hp566 : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 566 →
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) →
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) =
        2 * (w0Fin ((X.tr g).take k)).1.length + 1 → False := by
    intro j f hf h566 htc hcj
    have h1 := w0Fin_length_st hp hX hFw hwh hf (tcTrans_nonUb hX htc hf) (Or.inl h566) hcj
    have h2 := w0_len_lt hp hX hFw hwh hf (tcTrans_nonUb hX htc hf) (Or.inl h566)
    rw [hdiv] at h2
    omega
  have hlen : ∀ j f a' ws, X.get (w0Partner L g, j) = some f → (f.pc = 566 ∨ f.pc = 1155) →
      f.kind = .wr a' ws → Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) →
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) =
        2 * (w0Fin ((X.tr g).take k)).1.length + 1 → ws.length = 4 := by
    intro j f a' ws hf hfpc hk' htc hcj
    rcases hfpc with h566 | h1155
    · exact (hp566 j f hf h566 htc hcj).elim
    · obtain ⟨v, h1, -, hRd⟩ := w0_est_word hp hX hFw hwh hf h1155
        (Wg0.W0Valid.take_le (hbelow j f hf htc).1 (Nat.le_succ j)) a' ws hk'
      rw [h1]
      simp [Value.toBytes, hRd.1.1]
  obtain ⟨j, f, a', ws, hf, hfpc, hk', hcj, htc, hbs⟩ := rmax_read_bytes hp hX hFw
    (hIn.bar hp X hX hFw) hw he (Or.inr rfl) hcnt hlx.le hbelow hlen
  have h1155 : f.pc = 1155 := hfpc.resolve_left fun h566 => hp566 j f hf h566 htc hcj
  obtain ⟨v, hv1, hv2, hRd⟩ := w0_est_word hp hX hFw hwh hf h1155
    (Wg0.W0Valid.take_le (hbelow j f hf htc).1 (Nat.le_succ j)) a' ws hk'
  have hcar := w0_carry_eq hp hIn hX hFw hw he hv hf h1155 htc hU
  refine ⟨v, _, ?_, ?_, hRd, fun hbot => ?_⟩
  · rw [hbs, hv1]
    exact rebuild_of_scal (by rw [hRd.1.1]; omega) hv2
  · unfold w0ESum
    split_ifs
    · exact le_rfl
    · exact w0Carry_nonneg _ _
  · have hb : w0MxCarry P.scale (w0Fin ((X.tr (w0Partner L g)).take j)).1 = ⊥ := hcar ▸ hbot
    simp [w0ESum, hb]

/-- **The row-sum load keeps the trace valid.** -/
theorem w0Valid_snoc_pe (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {a : Acc} {bs : List (Option Byte)} (hw : warp L g < 4)
    (he : X.get (g, k) = some ⟨1157, .rd a bs⟩) (hv : W0Valid P.scale ((X.tr g).take k))
    (hU : W0Under P L X g k) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  rw [trace_take_succ he]
  exact w0Core_pe hp.scalePos rfl rfl (w0_pe_payload hp hIn hX hFw hw he hv hU) hv

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
