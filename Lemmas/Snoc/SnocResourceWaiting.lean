-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.Legacy
public import Lemmas.Snoc.SnocWaiting
public import Lemmas.Snoc.SnocMemory

@[expose] public section

namespace PTX
open AsyncCopy
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

theorem snoc_index_cases {i : EvId} (hi : i.2 < ((X.snoc g e r).tr i.1).length) :
    i.2 < (X.tr i.1).length ∨ i = (g, (X.tr g).length) := by
  by_cases ho : i.2 < (X.tr i.1).length
  · exact .inl ho
  · right
    rw [snoc_len] at hi
    split_ifs at hi with hg
    · exact Prod.ext hg (by rw [hg] at ho; omega)
    · exact (ho hi).elim

theorem snoc_get_not_kind {v : EvId} {ev : Event}
    (h : (X.snoc g e r).get v = some ev) (hk : e.kind ≠ ev.kind) : X.get v = some ev := by
  rw [snoc_get] at h
  split_ifs at h
  · exact (hk (congrArg Event.kind (Option.some.inj h))).elim
  · exact h

/-- A recorded group operation's participants are old events, so appending an
instruction adds no resource wait edge. -/
theorem snoc_pairWaits (hv : Tmem.Pair.HistoriesOk L X) {i j : EvId}
    (hw : Tmem.Pair.WaitEdge L (X.snoc g e r) i j) : Tmem.Pair.WaitEdge L X i j := by
  obtain ⟨ws, hws, hi, ⟨w, hw, lane, rfl⟩, pc, group, dst, action, hget, hm⟩ := hw
  obtain ⟨grp, hvalid⟩ := Tmem.Pair.Completed.valid hv hws hw
  have hold := len_of_get (hvalid.2.2.1 lane)
  rw [snoc_get_old hold] at hget
  exact ⟨ws, hws, hi, ⟨w, hw, lane, rfl⟩, pc, group, dst, action, hget, hm⟩

theorem snoc_elect (hk : e.kind.Ordinary) {i : EvId} {pc mask inst leader : Nat} :
    (X.snoc g e r).Elect i pc mask inst leader ↔ X.Elect i pc mask inst leader := by
  constructor
  · intro hi; exact snoc_get_not_kind hi (fun he => by simp [Kind.Ordinary,he] at hk)
  · exact Execution.le_get le_snoc

theorem snoc_warpBar (hk : e.kind.Ordinary) {i : EvId} {mask inst : Nat} :
    (X.snoc g e r).WarpBar i mask inst ↔ X.WarpBar i mask inst := by
  apply snoc_kind_iff
  intro he; simp [Kind.Ordinary,he] at hk

theorem snoc_warpWaits (hk : e.kind.Ordinary) {i j : EvId} :
    WarpBarEdge L (X.snoc g e r) i j ↔ WarpBarEdge L X i j := by
  simp only [WarpBarEdge,snoc_warpBar hk]

theorem snoc_regRequest (hk : e.kind.Ordinary)
    {i : EvId} {pc n inst : Nat} {inc : Bool} :
    SetMaxNReg.Request (X.snoc g e r) i pc inc n inst ↔ SetMaxNReg.Request X i pc inc n inst := by
  constructor
  · intro hi; exact snoc_get_not_kind hi (fun he => by simp [Kind.Ordinary,he] at hk)
  · exact Execution.le_get le_snoc

/-- Appending an instruction that is not a register request preserves every
request ordinal, including indices beyond the old source prefix. -/
theorem snoc_regOrdinal (hk : e.kind.Ordinary) {i : EvId} :
    SetMaxNReg.ordinal (X.snoc g e r) i = SetMaxNReg.ordinal X i := by
  have he : (match e.kind with | .setMaxReg .. => true | _ => false) = false := by
    cases hkind : e.kind <;> first | rfl | simp [Kind.Ordinary,hkind] at hk
  unfold SetMaxNReg.ordinal
  rw [snoc_tr]
  split_ifs with hthread
  · rw [← hthread,List.take_append,List.countP_append]
    cases hsub : i.2 - (X.tr i.1).length <;> simp [List.take]
    exact he
  · rfl

theorem snoc_regWaits (hk : e.kind.Ordinary) {i j : EvId} {b b' : Bool} :
    SetMaxNReg.WaitEdge L (X.snoc g e r) i j b b' ↔ SetMaxNReg.WaitEdge L X i j b b' := by
  simp only [SetMaxNReg.WaitEdge,SetMaxNReg.SameRequest,snoc_regRequest hk,snoc_regOrdinal hk]

end
end
end PTX
