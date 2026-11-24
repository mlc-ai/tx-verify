-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaOrder
public import Lemmas.Tcgen05.TcDataCell

@[expose] public section

/-! Tensor Memory stores against MMA-only reasoning: one event is one instruction, so an
MMA issue is never a store or a load, and orders from an MMA are MMA orders. -/
namespace PTX.TcMma
noncomputable section
variable {L : Launch} {X : Execution}

theorem mmaIssue_not_tst {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {a : Nat} {vals : List Value} {sh : TcShape} (hm : X.MmaIssue i d s acc mask)
    (ht : X.TSt i a vals sh) :
    False := by
  obtain ⟨pc, hp⟩ := hm
  obtain ⟨pc', hq⟩ := ht
  rw [hp] at hq; cases hq

theorem tld_not_mmaIssue {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {a : Nat} {vals : List Value} {sh : TcShape} (hl : X.TLd i a vals sh)
    (hm : X.MmaIssue i d s acc mask) :
    False := by
  obtain ⟨pc, hp⟩ := hm
  obtain ⟨pc', hq⟩ := hl
  rw [hp] at hq; cases hq

/-- A store-done order starts at a store. -/
theorem StoreDoneBefore.store {x y : EvId} (h : StoreDoneBefore L X x y) :
    ∃ a vals sh, X.TSt x a vals sh := h.1

/-- From an MMA, `WriteBefore` is the MMA order `Before`. -/
theorem WriteBefore.of_mma {x y : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hm : X.MmaIssue x d s acc mask) (h : WriteBefore L X x y) :
    Before L X x y := by
  rcases h with h | h | h
  · exact h
  · obtain ⟨a, vals, sh, ht⟩ := h.1
    exact (mmaIssue_not_tst hm ht).elim
  · have hcx : ∃ c, X.CpIssue x c := by
      obtain ⟨c, d₁, s₁, a₁, m₁, hcx, -, -, -⟩ := h.2.2
      exact ⟨c, hcx⟩
    obtain ⟨pc, hp⟩ := hm
    obtain ⟨c, hq⟩ := hcx
    obtain ⟨pc', hq'⟩ := hq
    rw [hp] at hq'; cases hq'

/-- From an MMA to a load, the only order is observed completion. -/
theorem WriteBefore.mma_load {x y : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {a : Nat} {vals : List Value} {sh : TcShape}
    (hm : X.MmaIssue x d s acc mask) (hl : X.TLd y a vals sh) (h : WriteBefore L X x y) :
    DoneBefore L X x y := by
  rcases h.of_mma hm with h | h
  · exact h
  · obtain ⟨d', s', acc', mask', hy⟩ : ∃ d s accum mask, X.MmaIssue y d s accum mask := by
      obtain ⟨-, -, -, -, d₁, s₁, a₁, m₁, -, hy, -⟩ := h.2.2
      exact ⟨d₁, s₁, a₁, m₁, hy⟩
    exact (tld_not_mmaIssue hl hy).elim

/-- Without stores, copies and shifts, Tensor Memory writes are MMA result cells. -/
theorem tmemWrite_of_no_store (hs : ∀ e a vals sh, ¬ X.TSt e a vals sh)
    (hc : ∀ e c, ¬ X.CpIssue e c) (hsh : ∀ e s, ¬ X.ShiftIssue e s) {w : EvId} {cell : Cell}
    (h : TmemWrite L X w cell) : X.MmaCell w cell := by
  rcases h with h | ⟨a, vals, sh, j, ht, -⟩ | ⟨c, cta, index, lane, hc', -⟩ |
    ⟨s, hsh', -⟩
  · exact h
  · exact (hs _ _ _ _ ht).elim
  · exact (hc _ c hc').elim
  · exact (hsh _ s hsh').elim

end
end PTX.TcMma
