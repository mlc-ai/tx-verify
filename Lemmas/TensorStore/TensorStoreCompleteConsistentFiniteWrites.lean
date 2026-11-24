-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.PlainExtend
public import Lemmas.Tensor.TensorCompleteConsistentRead
public import Lemmas.Order.ByteCausalityAcyclic

@[expose] public section

/-! A finite overapproximation of every actual memory write. Slots are enumerated
from the actual observation descriptor; no fixed transfer dimensions are assumed. -/
namespace PTX
open AsyncCopy
noncomputable section

/-- The element write stages of the linear copy issued by `i`, one per element of its spec. -/
def Execution.copyElemWriteCandidates (X : Execution) (i : EvId) : List Ref :=
  match X.get i with
  | some ⟨_, .copy s⟩ => (List.range s.elems.length).map fun j => .async i (.write (.elem j))
  | _ => []

def Execution.storeProgressWriteCandidatesAt (X : Execution) (i : EvId) : List Ref :=
  [.thread i,.async i (.write .copy)] ++ X.copyElemWriteCandidates i ++
  ((X.clc i).written.toList.map fun c => .async i (.write (.cta c))) ++
  ((X.tensor i).toList.flatMap fun o =>
    (Finset.univ : Finset (TensorTransfer.Slot o.spec.descriptor)).toList.map fun s =>
      .async i (.write (.load s.1.val s.2.1.val s.2.2.val))) ++
  ((X.tensorStores i).toList.flatMap fun o =>
    (Finset.univ : Finset (TensorTransfer.Slot o.spec.descriptor)).toList.map fun s =>
      .async i (.write (.store s.1.val s.2.1.val s.2.2.val)))

def Execution.storeProgressWriteCandidates (X : Execution) (L : Launch) : List Ref :=
  (X.events L).flatMap X.storeProgressWriteCandidatesAt

private theorem candidate_tensor {X : Execution} {i : EvId} {o : TensorCopy.Observation}
    {x y k : Nat} (ho : X.tensor i=some o)
    (hs : ∃slot,TensorTransfer.slotAt o.spec.descriptor x y k=some slot) :
    Ref.async i (.write (.load x y k)) ∈ X.storeProgressWriteCandidatesAt i := by
  obtain ⟨slot,hs⟩ := hs
  obtain ⟨hx,hy,hk⟩ := TensorCopy.slotAt_coordinates hs
  simp only [Execution.storeProgressWriteCandidatesAt,List.mem_append]
  refine Or.inl (Or.inr ?_)
  simp only [ho,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_map]
  refine ⟨slot,by simp,?_⟩
  simp [hx,hy,hk]

private theorem candidate_store {X : Execution} {i : EvId} {o : TensorStore.Observation}
    {x y k : Nat} (ho : X.tensorStores i=some o)
    (hs : ∃slot,TensorTransfer.slotAt o.spec.descriptor x y k=some slot) :
    Ref.async i (.write (.store x y k)) ∈ X.storeProgressWriteCandidatesAt i := by
  obtain ⟨slot,hs⟩ := hs
  obtain ⟨hx,hy,hk⟩ := TensorCopy.slotAt_coordinates hs
  simp only [Execution.storeProgressWriteCandidatesAt,List.mem_append]
  refine Or.inr ?_
  simp only [ho,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_map]
  refine ⟨slot,by simp,?_⟩
  simp [hx,hy,hk]

theorem memWrite_storeProgressCandidates {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {r : Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites r a bs) :
    r ∈ X.storeProgressWriteCandidates L := by
  have eventMember {i : EvId} {ev : Event} (he : X.get i=some ev) : i ∈ X.events L := by
    apply mem_events
    · by_contra hn
      have ht := hX.outside i.1 (Nat.le_of_not_gt hn)
      have hi := len_of_get he
      rw [ht] at hi
      simp at hi
    · exact len_of_get he
  apply List.mem_flatMap.mpr
  cases r with
  | thread i =>
    rcases hw with ⟨pc,he⟩ | ⟨old,pc,he⟩ <;>
      exact ⟨i,eventMember he,by simp [Execution.storeProgressWriteCandidatesAt]⟩
  | async i p =>
    cases p <;> try (cases hw; done)
    case writeCopy =>
      obtain ⟨s,⟨pc,he⟩,_⟩ := hw
      exact ⟨i,eventMember he,by simp [Execution.storeProgressWriteCandidatesAt]⟩
    case writeElem j =>
      obtain ⟨s,⟨pc,he⟩,hel,_⟩ := hw
      have hj := (List.getElem?_eq_some_iff.mp hel).1
      exact ⟨i,eventMember he,by
        simp [Execution.storeProgressWriteCandidatesAt,Execution.copyElemWriteCandidates,he,hj]⟩
    case writeCta c =>
      obtain ⟨s,targets,⟨pc,he⟩,_,hc,_⟩ := hw
      exact ⟨i,eventMember he,by simp [Execution.storeProgressWriteCandidatesAt,hc]⟩
    case writeLoad x y k =>
      obtain ⟨o,address,b,ho,⟨pc,he⟩,_,hb,_⟩ := hw
      have hs : ∃slot,TensorTransfer.slotAt o.spec.descriptor x y k=some slot := by
        cases hslot : TensorTransfer.slotAt o.spec.descriptor x y k with
        | none => simp [TensorCopy.writeByte,hslot] at hb
        | some slot => exact ⟨slot,rfl⟩
      exact ⟨i,eventMember he,candidate_tensor ho hs⟩
    case writeStore x y k =>
      obtain ⟨o,address,b,ho,⟨pc,he⟩,_,hb,_⟩ := hw
      have hs : ∃slot,TensorTransfer.slotAt o.spec.descriptor x y k=some slot := by
        cases hslot : TensorTransfer.slotAt o.spec.descriptor x y k with
        | none => simp [TensorStore.writeByte,hslot] at hb
        | some slot => exact ⟨slot,rfl⟩
      exact ⟨i,eventMember he,candidate_store ho hs⟩

/-- Source selection uses the real causal order. Every selected source is visible,
and maximality eliminates precisely the Hidden obligation of a new read. -/
theorem exists_storeProgress_latest_visible {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    {l : Loc} {read : Ref}
    (hex : ∃w a bs,X.MemWrites w a bs ∧ a.Covers l ∧ ByteCausality L X l w read)
    (hbytes : ∀w a bs,X.MemWrites w a bs → a.Covers l → ByteCausality L X l w read →
      ∃value,wbyte a bs l=some value) :
    ∃w a bs value,X.MemWrites w a bs ∧ a.Covers l ∧ wbyte a bs l=some value ∧
      ByteCausality L X l w read ∧
      ∀other footprint bytes,X.MemWrites other footprint bytes → footprint.Covers l →
        ByteCausality L X l other read → ¬ByteCausality L X l w other := by
  let P : Ref → Prop := fun w => ∃a bs,X.MemWrites w a bs ∧ a.Covers l ∧ ByteCausality L X l w read
  let R : Ref → Ref → Prop := Relation.TransGen (ByteCausality L X l)
  have hne : ∃w∈X.storeProgressWriteCandidates L,P w := by
    obtain ⟨w,a,bs,hw,hc,hv⟩ := hex
    exact ⟨w,memWrite_storeProgressCandidates hX hw,a,bs,hw,hc,hv⟩
  obtain ⟨w,_,⟨a,bs,hw,hc,hv⟩,hmax⟩ := exists_maximal
    (R:=R) (fun _ _ _ h h' => h.trans h')
    (ByteCausality.acyclic hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk l)
    P (X.storeProgressWriteCandidates L) hne
  obtain ⟨value,hvalue⟩ := hbytes w a bs hw hc hv
  refine ⟨w,a,bs,value,hw,hc,hvalue,hv,?_⟩
  intro other footprint bytes ho hcover hvis hafter
  exact hmax other (memWrite_storeProgressCandidates hX ho)
    ⟨footprint,bytes,ho,hcover,hvis⟩ (.single hafter)

end
end PTX
