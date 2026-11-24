-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorCopySize
public import Lemmas.TensorStore.TensorStoreSize
public import Core.Data.Events

@[expose] public section

namespace PTX
noncomputable section

private theorem sums_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sums_strict {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) (x : α) (hx : x ∈ xs) (hlt : f x < g x) :
    (xs.map f).sum < (xs.map g).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    have hh := h y (by simp)
    have ht : ∀ z ∈ ys, f z ≤ g z := fun z hz => h z (by simp [hz])
    simp only [List.mem_cons] at hx
    simp only [List.map_cons, List.sum_cons]
    rcases hx with rfl | hx
    · have := sums_mono ys f g ht
      omega
    · have := ih ht hx
      omega

/-- Growing a recorded async stage grows the complete execution measure. -/
theorem Execution.size_lt_of_asyncStages {X Y : Execution} {L : Launch} {i : EvId}
    (htr : Y.tr = X.tr) (hp : X.pairSize L ≤ Y.pairSize L) (hg : i.1 < L.threads)
    (hi : i.2 < (X.tr i.1).length)
    (hm : ∀ j, X.asyncSize j ≤ Y.asyncSize j)
    (hs : X.asyncSize i < Y.asyncSize i) : X.size L < Y.size L := by
  apply Nat.add_lt_add_of_lt_of_le ?_ hp
  unfold Execution.threadSize
  rw [htr]
  apply sums_strict _ _ _ ?_ i.1 (List.mem_range.mpr hg) ?_
  · intro g _
    exact Nat.add_le_add_left (sums_mono _ _ _ (fun k _ => hm (g, k))) _
  · apply Nat.add_lt_add_left
    exact sums_strict _ _ _ (fun k _ => hm (i.1, k)) i.2 (List.mem_range.mpr hi) hs

/-- Updating one tensor observation with strictly more effects makes counted progress.
Consistency, read sources and object histories must separately justify the update. -/
theorem Execution.tensor_update_size {X : Execution} {L : Launch} {i : EvId}
    {old newer : TensorCopy.Observation} (ho : X.tensor i = some old)
    (hg : i.1 < L.threads) (hi : i.2 < (X.tr i.1).length)
    (hs : old.effects.size < newer.effects.size) :
    X.size L < ({ X with tensor := fun j => if j = i then some newer else X.tensor j }).size L := by
  let Y := { X with tensor := fun j => if j = i then some newer else X.tensor j }
  have hstrict : X.asyncSize i < Y.asyncSize i := by
    simp only [Execution.asyncSize, Y, ↓reduceIte, ho]
    exact Nat.add_lt_add_right
      (Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add_left hs _) _) _) _
  apply Execution.size_lt_of_asyncStages (X := X) (Y := Y) rfl (Nat.le_refl _) hg hi ?_ hstrict
  intro j
  by_cases hj : j = i
  · subst j; exact Nat.le_of_lt hstrict
  · simp [Execution.asyncSize, Execution.elemSize, Execution.get, Y, hj]

/-- Output source reads, writes and both completion stages make counted progress. -/
theorem Execution.tensorStore_update_size {X : Execution} {L : Launch} {i : EvId}
    {old newer : TensorStore.Observation} (ho : X.tensorStores i = some old)
    (hg : i.1 < L.threads) (hi : i.2 < (X.tr i.1).length)
    (hs : old.effects.size < newer.effects.size) :
    X.size L <
      ({ X with tensorStores := fun j =>
        if j = i then some newer else X.tensorStores j }).size L := by
  let Y :=
    { X with tensorStores := fun j => if j = i then some newer else X.tensorStores j }
  have hstrict : X.asyncSize i < Y.asyncSize i := by
    simp only [Execution.asyncSize, Y, ↓reduceIte, ho]
    exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add_left hs _) _) _
  apply Execution.size_lt_of_asyncStages (X := X) (Y := Y) rfl (Nat.le_refl _) hg hi ?_ hstrict
  intro j
  by_cases hj : j = i
  · subst j; exact Nat.le_of_lt hstrict
  · simp [Execution.asyncSize, Execution.elemSize, Execution.get, Y, hj]

end
end PTX
