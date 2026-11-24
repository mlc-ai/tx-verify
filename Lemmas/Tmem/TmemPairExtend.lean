-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcExtend
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Snoc.SnocReady

@[expose] public section

/-! Appending one instruction: the allocation-management rules only constrain the thread's previous
last event: its request must be performed, and its operation complete if it waits for it, and the
address store after lane 0's recorded allocation holds its column. -/

namespace PTX.Tmem.Pair
noncomputable section

variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}

/-- The thread's last event, if an allocation-management event, must be ready before its thread
continues. -/
theorem Blocking.snoc (hb : Blocking L X)
    (hlast : ∀ pc grp dst act, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource grp dst act)⟩ → Ready L X (g, (X.tr g).length - 1)) :
    Blocking L (X.snoc g e r) := by
  intro i pc grp dst act hget hlen
  by_cases hnew : i = (g, (X.tr g).length)
  · subst hnew
    simp [snoc_len] at hlen
  have hold : i.2 < (X.tr i.1).length := by
    rw [snoc_get] at hget
    rw [ite_eq_right hnew] at hget
    exact len_of_get hget
  have hgetX : X.get i = some ⟨pc, .tc (.resource grp dst act)⟩ := by
    rwa [snoc_get_old hold] at hget
  have hrX : Ready L X i := by
    by_cases hi : i.1 = g ∧ i.2 + 1 = (X.tr g).length
    · obtain ⟨h1, h2⟩ := hi
      have hi' : i = (g, (X.tr g).length - 1) := Prod.ext h1 (by omega)
      rw [hi'] at hgetX ⊢
      exact hlast pc grp dst act hgetX
    · apply hb i pc grp dst act hgetX
      rw [snoc_len] at hlen
      split_ifs at hlen with hg
      · have := fun h => hi ⟨hg, h⟩
        rw [hg]
        omega
      · exact hlen
  exact ready_snocHistory_old (records := X.objects) SnocRecords.same
    (fun ⟨pc', op, own, recv, h⟩ => by rw [hgetX] at h; cases h) hnew hrX

/-- The address store after lane 0's allocation event `i` of a recorded completion holds its
column (the obligation OBJ-TMEM-ALLOC-RESULT places on the event after `i`). -/
def StoreOk (L : Launch) (X : Execution) (i : EvId) (bs : List Byte) : Prop :=
  ∀ pc group dst n, X.get i = some ⟨pc, .tc (.resource group dst (.alloc n))⟩ →
    ∀ cta x base, x ∈ X.tmemHistory cta → x.own.event L 0 = i →
      x.action = .alloc n base → bs = (Value.bits 32 (BitVec.ofNat 64 base)).toBytes

/-- Appending an event keeps the result rule when, if it is a store, its bytes satisfy the
obligation of the thread's previous last event. -/
theorem ResultOk.snoc (hx : ResultOk L X)
    (hstore : ∀ pc a bs, e = ⟨pc, .wr a bs⟩ → 0 < (X.tr g).length →
      StoreOk L X (g, (X.tr g).length - 1) bs) :
    ResultOk L (X.snoc g e r) := by
  intro i pc group dst n hi cta x base hx' hwi hwa pc' a bs hs
  rcases snoc_get_cases hi with ⟨rfl, hev⟩ | ⟨hlt, hget⟩
  · rw [snoc_get, ite_eq_right (by simp)] at hs
    have := len_of_get hs
    simp at this
  · rcases snoc_get_cases hs with ⟨hnew, hev⟩ | ⟨-, hs'⟩
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hnew
      have hi' : i = (g, (X.tr g).length - 1) := Prod.ext h1 (by simp at h2 ⊢; omega)
      subst hev
      exact hstore pc' a bs rfl (by have := h2; omega) pc group dst n (hi' ▸ hget) cta x base hx'
        (hwi.trans hi') hwa
    · exact hx i pc group dst n hget cta x base hx' hwi hwa pc' a bs hs'

/-- An appended event that is not a store keeps the result rule. -/
theorem ResultOk.snoc_not_wr (hx : ResultOk L X) (hn : ∀ pc a bs, e ≠ ⟨pc, .wr a bs⟩) :
    ResultOk L (X.snoc g e r) :=
  hx.snoc fun pc a bs he => (hn pc a bs he).elim

/-- Appending to a thread whose last event is no allocation event of a recorded lane 0 keeps the
result rule. -/
theorem ResultOk.snoc_last (hx : ResultOk L X)
    (hl : ∀ pc group dst n, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource group dst (.alloc n))⟩ →
      ∀ cta x, x ∈ X.tmemHistory cta → x.own.event L 0 ≠ (g, (X.tr g).length - 1)) :
    ResultOk L (X.snoc g e r) :=
  hx.snoc fun _ _ _ _ _ pc group dst n hget cta x _ hx' hwi _ =>
    (hl pc group dst n hget cta x hx' hwi).elim

end
end PTX.Tmem.Pair
