-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ShiftExact
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
import Lemmas.Flow.MaxCore

@[expose] public section

/-! # The running maximum of the rounds is the fold's

With the words of the rounds exact (`Ev`), the words of the carried maximum (`mAfter`) are the
maxima of `SoftFold.run`: round `j` brings the maxima of the two halves of block `j`, whose
maximum is the block's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof
open Lib.SoftFold Classical

set_option maxRecDepth 100000
noncomputable section

theorem ne_top_max {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : max x y ≠ ⊤ := by
  rcases max_choice x y with h | h <;> rw [h] <;> assumption

theorem ev_max3 {d a b c : Value} {x y z : EReal} (ha : Ev a x) (hb : Ev b y) (hc : Ev c z) :
    Ev (okVal d (maxE [a, b, c])) (max (max x y) z) := by
  have e : maxE [a, b, c] = pure (erealValue .f32 (max (max x y) z)) := by
    unfold maxE
    simp only [idealMax, ha.read, hb.read, hc.read, bindRead]
  rw [e]
  exact ⟨rfl, ne_top_max (ne_top_max ha.2 hb.2) hc.2⟩

theorem mxWord_ev {m a b : Value} {mE aE bE : EReal} (hm : Ev m mE) (ha : Ev a aE)
    (hb : Ev b bE) : Ev (Lib.mxWord m a b) (max (max mE aE) bE) := by
  simp only [Lib.mxWord, Lib.maxItem, xFinal, XItem.upd, XItem.vals, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, Function.update_self]
  simp only [ite_true, show (1520 : Nat) ≠ 1914 by decide, ite_false, show (1521 : Nat) ≠ 1914
    by decide, show (1521 : Nat) ≠ 1520 by decide]
  exact ev_max3 hm ha hb

/-- **The carried maximum after a round**: the maximum or the new one, by the lazy test. -/
theorem mNext_ev {c m mx : Value} {sc : ℝ} {mE xE : EReal} (hc : Ev c sc) (hpos : 0 < sc)
    (hm : Ev m mE) (hmx : Ev mx xE) :
    Ev (Lib.mNext c m mx) (if Keep (alphaLog2 sc mE xE) then mE else xE) := by
  obtain ⟨-, hp, -⟩ := alpha_exact hc hpos hm hmx
  have e : Lib.mNext c m mx = if predOf (Lib.alphaVal c m mx 168) = true then m else mx := by
    simp [Lib.mNext, oFinal, Lib.updItem, OItem.upd, OItem.vals, Function.update, Lib.alphaVal,
      Lib.alphaRest, xFinal, XItem.upd, XItem.vals, Lib.alphaIn, opndVal]
  rw [e]
  by_cases hk : Keep (alphaLog2 sc mE xE)
  · simp only [hp.mpr hk, hk, ite_true]; exact hm
  · simp only [mt hp.mp hk, hk, ite_false]; exact hmx

/-- One round of the carried maximum is a step of the fold when the words are the halves'. -/
theorem round_ev {c m a b : Value} {sc : ℝ} {st : St} {aE bE : EReal} {blk : List (ℝ × ℝ)}
    (hc : Ev c sc) (hpos : 0 < sc) (hm : Ev m st.m) (ha : Ev a aE) (hb : Ev b bE)
    (hmax : max aE bE = blockMax blk) :
    Ev (Lib.mNext c m (Lib.mxWord m a b)) (step sc blk st).m := by
  have h := mxWord_ev hm ha hb
  rw [max_assoc, hmax] at h
  have := mNext_ev hc hpos hm h
  simpa only [step] using this

/-- **The carried maximum after the rounds is the fold's.** -/
theorem mAfter_ev {c : Value} {sc : ℝ} (hc : Ev c sc) (hpos : 0 < sc) :
    ∀ (ps : List (Value × Value)) (bs : List (List (ℝ × ℝ))),
      List.Forall₂ (fun p blk => ∃ aE bE, Ev p.1 aE ∧ Ev p.2 bE ∧ max aE bE = blockMax blk) ps bs →
      Ev (mAfter c ps) (Lib.SoftFold.run sc bs).m := by
  have key : ∀ (ps : List (Value × Value)) (bs : List (List (ℝ × ℝ))) (m : Value) (st : St),
      Ev m st.m →
      List.Forall₂ (fun p blk => ∃ aE bE, Ev p.1 aE ∧ Ev p.2 bE ∧ max aE bE = blockMax blk) ps bs →
      Ev (ps.foldl (fun m p => Lib.mNext c m (Lib.mxWord m p.1 p.2)) m)
        (bs.foldl (fun st blk => step sc blk st) st).m := by
    intro ps bs m st hm h
    induction h generalizing m st with
    | nil => exact hm
    | cons hp _ ih =>
      obtain ⟨aE, bE, ha, hb, hmax⟩ := hp
      exact ih _ _ (round_ev hc hpos hm ha hb hmax)
  intro ps bs h
  exact key ps bs _ ⟨⊥, 0, 0⟩ ev_bot h

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
