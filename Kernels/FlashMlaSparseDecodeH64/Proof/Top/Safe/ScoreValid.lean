-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.ScoreWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SldCol
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemLoad

@[expose] public section

/-! # A score load keeps warpgroup 0's trace valid

The load at pc 278, 280, 283 or 285 reads 32 words of the QK chain's cells (`score_ld_word_at`,
from the Tensor Memory words of the events before it in the tcgen05 order): each reads as a
single-precision number, so the new half of the block's words is valid. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The words of a score load** (valid rows): 32 words that read as `f32` numbers, the high
half's clean and finite, the low half's score halves. -/
theorem w0_pay_score (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {g k : Nat} {e : Event} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hw : warp L g < 4) (hpc : e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285)
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w) :
    ∃ vals, w0TcVals e = some vals ∧ vals.length = 32 ∧ ∀ c < 32,
      W0HiWord (vals.getD c (.pred false)) ∧ W0LoWord (vals.getD c (.pred false)) := by
  obtain ⟨a, vals, hk, -, -⟩ := wg0_sldKind hp hX hFw he hub hpc
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk
  subst hk
  obtain ⟨hc4, hc3⟩ := wg0_sldCol hp hX hFw he hpc
  have hlen : vals.length = 32 := scoreLdLen hp hX he rfl (by simp only [List.mem_cons]; omega)
  have hat : Wg0At L g pc := ⟨hw, by omega, by omega⟩
  refine ⟨vals, rfl, hlen, fun c hc => ?_⟩
  obtain ⟨-, -, ⟨x, hx⟩, -⟩ := score_ld_word_at hp hIn hX hFw hbelow he hat
    (by by_cases h1 : pc = 278 ∨ pc = 283
        · have := hc4 h1; omega
        · have := hc3 (by omega); omega)
    (j := c) (by omega)
  rw [List.getD_eq_getElem?_getD, hx]
  exact ⟨⟨clean_float x, x, by simp [valFloat]; rfl⟩, trivial⟩

/-- **A score load keeps the trace valid.** -/
theorem w0Valid_snoc_score (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {g k : Nat} {e : Event} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hw : warp L g < 4)
    (hpc : e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285)
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (h : W0Valid P.scale ((X.tr g).take k)) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  obtain ⟨vals, hv, hlen, hpay⟩ := w0_pay_score hp hIn hX hFw he hub hw hpc hbelow
  rw [trace_take_succ he]
  obtain ⟨hb, -, -⟩ := w0_boundSeen hp hX hFw hw he hub (by omega : 103 ≤ e.pc) h
  exact w0Core_score hp.scalePos hpc hv hb (fun _ => ⟨hlen, fun c hc => (hpay c hc).1⟩)
    (fun _ => ⟨hlen, fun c hc => (hpay c hc).2⟩) h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
