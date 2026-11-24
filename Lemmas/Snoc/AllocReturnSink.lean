-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocAsync

@[expose] public section

/-! # Terminal allocator returns in the dependence graph -/

namespace PTX

open AsyncCopy

variable {L : Launch} {K : Kernel} {X : Execution} {i : EvId}
  {pc count : Nat} {group : CtaGroup} {dst : Option Loc}

/-- A terminal allocation has no outgoing dependency or enabling-object edge. -/
theorem alloc_return_dep_sink (hobj : ObjectsOk X) (hcluster : ClusterHistoryOk L X)
    (hi : X.get i = some ⟨pc, .tc (.resource group dst (.alloc count))⟩)
    (hlast : i.2 + 1 = (X.tr i.1).length) {o : OrderObject} (ho : o.Enabling)
    (v : Ref × Bool) :
    ¬ (DepStep L K X (.thread i, true) v ∨ ObjectOrder L X o (.thread i, true) v) := by
  obtain ⟨f, b⟩ := v
  rintro (hd | horder)
  · rcases hd with hs | hi' | ⟨hissue, _⟩ | ⟨_, _, w, j, hwi, _, hresume⟩
    · rcases hs with ⟨_, hissue, _, _⟩ | ⟨_, _, hedge⟩
      · cases hissue
      · exact hedge
    · exact Bool.noConfusion hi'.1
    · cases hissue
    · obtain rfl := Ref.thread.inj hwi
      obtain ⟨heq, hj, hlen⟩ := hresume.1
      rw [← heq, ← hlast] at hlen
      omega
  · cases o with
    | mbar m =>
      obtain ⟨_, _, _, _, record, _, hrecord, ht, _⟩ := horder
      obtain ⟨ha, _⟩ := (hobj m).2.1 record (List.mem_of_getElem? hrecord)
      rw [ht, show objectAction X X.async m (.thread i) = none by simp [objectAction, hi]] at ha
      cases ha
    | ctaBar c id => exact Bool.noConfusion horder.1
    | cluster c =>
      obtain ⟨j, _, hji, _, _, _, _, _, rec, _, hrec, _, _, hmem, _, _, _⟩ := horder
      obtain rfl := Ref.thread.inj hji
      rcases hcluster.ref_operation (List.mem_of_getElem? hrec) hmem with
        ⟨_, _, h⟩ | ⟨_, h⟩
      all_goals (rw [hi] at h; cases h)
    | tmem c => exact ho

/-- A plain append preserves the histories needed to classify a terminal allocation return. -/
theorem snoc_alloc_return_dep_sink {A : List Assumption} {mem0 : Mem0}
    {g : Nat} {e : Event} {r : Nat → Option Ref}
    (hX : Consistent L K A mem0 X) (hk : e.kind.isTma = false)
    (hi : X.get i = some ⟨pc, .tc (.resource group dst (.alloc count))⟩)
    (hlast : i.2 + 1 = ((X.snoc g e r).tr i.1).length) {o : OrderObject} (ho : o.Enabling)
    (v : Ref × Bool) :
    ¬ (DepStep L K (X.snoc g e r) (.thread i, true) v ∨
      ObjectOrder L (X.snoc g e r) o (.thread i, true) v) :=
  alloc_return_dep_sink (tmaOk_snoc_plain hX.tma hk).2.2.1
    (hX.cluster.preserving le_snoc rfl) (Execution.le_get le_snoc hi) hlast ho v

end PTX
