-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.CountNth

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- A bounded ordinal assigned injectively to each actual issue bounds the trace count. -/
theorem count_le_tags {α : Type} {es : List α} {p : α → Bool} {n : Nat} (tag : Nat → Nat)
    (bound : ∀ {k e}, es[k]?=some e → p e → tag k<n)
    (one : ∀ {k j e f}, es[k]?=some e → p e → es[j]?=some f → p f → tag k=tag j → k=j) :
    es.countP p≤n := by
  classical
  let ids := (Finset.range es.length).filter (fun k => es[k]?.any p = true)
  have present {k} (h : k∈ids) : ∃ e, es[k]?=some e ∧ p e := by
    have hit := (Finset.mem_filter.mp h).2
    cases get : es[k]? with
    | none => rw [get] at hit; cases hit
    | some e => exact ⟨e,rfl,by simpa only [get,Option.any_some] using hit⟩
  have size : ids.card≤(Finset.range n).card := by
    apply Finset.card_le_card_of_injOn tag
    · intro k h
      obtain ⟨_,get,hit⟩ := present h
      exact Finset.mem_range.mpr (bound get hit)
    · intro k a j b eq
      obtain ⟨_,get,hit⟩ := present a
      obtain ⟨_,other,use⟩ := present b
      exact one get hit other use eq
  dsimp only [ids] at size
  rwa [←MbarRing.Slot.countP_take_card,List.take_length,Finset.card_range] at size

end PTX.Kernels.InklingRelDecode.Proof.Lib
