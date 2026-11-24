-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Lemmas.Tensor.TensorCopySize
public import Lemmas.TensorStore.TensorStoreSize
public import Mathlib.Data.List.Range
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section

section
namespace PTX.Proof.ExecutionCountedPrefix
noncomputable section

private theorem flag_mono {a b : Bool} (h : a=true → b=true) :
    (if a then 1 else 0 : Nat)≤(if b then 1 else 0) := by
  cases a <;>cases b <;>simp_all

private theorem option_flag_mono {α : Type} {a b : Option α}
    (h : ∀v,a=some v → b=some v) :
    (if a.isSome then 1 else 0 : Nat)≤(if b.isSome then 1 else 0) := by
  cases ha:a with
  | none=>simp []
  | some v=>simp [h v ha]

private theorem copy_observation_size {a b : TensorCopy.Observation}
    (h : a.Extends b) : a.effects.size≤b.effects.size := by
  rcases a with ⟨sa,ea⟩
  rcases b with ⟨sb,eb⟩
  obtain ⟨hs,he⟩:=h
  cases hs
  exact TensorCopy.Extends.size_mono he

private theorem store_observation_size {a b : TensorStore.Observation}
    (h : a.Extends b) : a.effects.size≤b.effects.size := by
  rcases a with ⟨sa,ea⟩
  rcases b with ⟨sb,eb⟩
  obtain ⟨hs,he⟩:=h
  cases hs
  exact TensorStore.Extends.size_mono he

theorem tensorCopy_size_mono {ι : Type} {a b : ι→Option TensorCopy.Observation}
    (h : TensorCopy.SnapshotExtends a b) (i : ι) :
    ((a i).map fun o=>o.effects.size).getD 0≤((b i).map fun o=>o.effects.size).getD 0 := by
  cases ha:a i with
  | none=>simp []
  | some old=>
    obtain ⟨newer,hb,he⟩:=h i old ha
    simpa only [ha,hb,Option.map_some,Option.getD_some] using copy_observation_size he

theorem tensorStore_size_mono {ι : Type} {a b : ι→Option TensorStore.Observation}
    (h : TensorStore.SnapshotExtends a b) (i : ι) :
    ((a i).map fun o=>o.effects.size).getD 0≤((b i).map fun o=>o.effects.size).getD 0 := by
  cases ha:a i with
  | none=>simp []
  | some old=>
    obtain ⟨newer,hb,he⟩:=h i old ha
    simpa only [ha,hb,Option.map_some,Option.getD_some] using store_observation_size he

/-- Positions already present in a thread's trace keep their event under extension. -/
private theorem get_of_le {X Y : Execution} (h : Execution.le X Y) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : Y.get e = some ev := by
  obtain ⟨suffix, hs⟩ := h.1 e.1
  have hi : e.2 < (X.tr e.1).length := (List.getElem?_eq_some_iff.mp he).1
  unfold Execution.get at he ⊢
  rw [← hs, List.getElem?_append_left hi]
  exact he

/-- Element stages are monotone in an extension of the same linear operation. -/
theorem elemSize_mono {X Y : Execution} (h : Execution.le X Y) (i : EvId) :
    X.elemSize i≤Y.elemSize i := by
  obtain ⟨_,_,_,_,_,_,helemW,helemO⟩ : AsyncCopy.Extends X.async Y.async := h.2.2.1
  cases hg : X.get i with
  | none =>
    have h0 : X.elemSize i=0 := by
      unfold Execution.elemSize
      rw [hg]
    omega
  | some ev =>
    obtain ⟨pc,k⟩:=ev
    have hgy : Y.get i=some ⟨pc,k⟩ := get_of_le h hg
    unfold Execution.elemSize
    rw [hg, hgy]
    split
    · rename_i x pc' s heq
      have hw := List.countP_mono_left (l := List.range s.elems.length)
        (p := fun j => ((X.async.copies i).elemWrites j).isSome)
        (q := fun j => ((Y.async.copies i).elemWrites j).isSome)
        (fun j _ hj => by
          obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hj
          simp [helemW i j bs hbs])
      have ho := List.countP_mono_left (l := List.range s.elems.length)
        (p := fun j => ((X.async.copies i).elemOld j).isSome)
        (q := fun j => ((Y.async.copies i).elemOld j).isSome)
        (fun j _ hj => by
          obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hj
          simp [helemO i j bs hbs])
      omega
    · omega

/-- Execution extension preserves every recorded asynchronous contribution,
including tensor snapshots and collective completion notifications. -/
theorem asyncSize_mono {X Y : Execution} (h : Execution.le X Y) (i : EvId) :
    X.asyncSize i≤Y.asyncSize i := by
  have helem:=elemSize_mono h i
  rcases h with ⟨_,_,ha,_,_,_,hc,_,ht,hs,_,_,hn⟩
  obtain ⟨hread0,hwrite0,hnotify0,hmmaOperands,hmmaDone,harrived0,_,_⟩ := ha
  have hread:=option_flag_mono (hread0 i)
  have hwrite:=option_flag_mono (hwrite0 i)
  have hnotify:=flag_mono (hnotify0 i)
  have hstarted:=option_flag_mono (hmmaOperands i)
  have hdone:=flag_mono (hmmaDone i)
  have harrived:=flag_mono (harrived0 i)
  have hresolve:=option_flag_mono (hc i).1
  have hwritten:=Finset.card_le_card (hc i).2.1
  have hnotified:=Finset.card_le_card (hc i).2.2
  have htensor:=tensorCopy_size_mono ht i
  have hstore:=tensorStore_size_mono hs i
  have htc:=Finset.card_le_card (hn i)
  change (if (X.async.mmaOperands i).isSome then 1 else 0)≤
    (if (Y.async.mmaOperands i).isSome then 1 else 0) at hstarted
  unfold Execution.asyncSize AsyncCopy.Snapshot.mmaStarted
  omega

end
end PTX.Proof.ExecutionCountedPrefix
end

section
namespace PTX.Proof.ExecutionCountedPrefix
open PTX
noncomputable section

/-- Extension preserves the allocator's complete paired-resource history. -/
theorem pairSize_mono {X Y : Execution} (h : Execution.le X Y) (L : Launch) :
    X.pairSize L≤Y.pairSize L := by
  rcases h with ⟨_,_,_,_,_,_,_,_,_,_,hp,_,_⟩
  exact Nat.add_le_add (List.sum_le_sum (fun cta _=>(hp.1 cta).length_le)) hp.2.length_le

theorem sum_range_mono {n m : Nat} {f g : Nat→Nat} (hn : n≤m)
    (hfg : ∀i,f i≤g i) :
    ((List.range n).map f).sum≤((List.range m).map g).sum := by
  have hfirst:((List.range n).map f).sum≤((List.range n).map g).sum:=
    List.sum_le_sum (fun i _=>hfg i)
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hn
  rw [hk,List.range_add,List.map_append,List.sum_append]
  omega

def threadMeasure (X : Execution) (g : Nat) : Nat :=
  (X.tr g).countP Event.counts+((List.range (X.tr g).length).map fun j=>X.asyncSize (g,j)).sum

theorem asyncRange_mono {X Y : Execution} (h : Execution.le X Y) (g : Nat) :
    ((List.range (X.tr g).length).map fun j=>X.asyncSize (g,j)).sum≤
      ((List.range (Y.tr g).length).map fun j=>Y.asyncSize (g,j)).sum :=
  sum_range_mono (h.1 g).length_le (fun j=>asyncSize_mono h (g,j))

theorem threadMeasure_mono {X Y : Execution} (h : Execution.le X Y) (g : Nat) :
    threadMeasure X g≤threadMeasure Y g :=
  Nat.add_le_add ((h.1 g).countP_le (p:=Event.counts)) (asyncRange_mono h g)

theorem threadSize_mono {X Y : Execution} (h : Execution.le X Y) (L : Launch) :
    X.threadSize L≤Y.threadSize L :=
  List.sum_le_sum (fun g _=>threadMeasure_mono h g)

/-- This monotonicity includes every asynchronous stage, paired allocator
completion in the actual execution measure. -/
theorem size_mono {X Y : Execution} (h : Execution.le X Y) (L : Launch) : X.size L≤Y.size L := by
  have ht:=threadSize_mono h L
  have hp:=pairSize_mono h L
  unfold Execution.size
  omega

end
end PTX.Proof.ExecutionCountedPrefix
end
