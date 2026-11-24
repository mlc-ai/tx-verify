-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcCompleteConsistentArbitration
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! Recording a response whose arbitration result already exists. This is a
counted independent effect; no response write or notification is fabricated. -/
namespace PTX
noncomputable section

def Execution.resolveClc (X : Execution) (i : EvId) (r : ClcResponse) : Execution :=
  { X with clc := fun j => if j=i then {X.clc j with resolved:=some r} else X.clc j }

 theorem resolveClc_clcOk {L : Launch} {X : Execution} {i : EvId} {r : ClcResponse}
    {s : Clc.Spec} {targets : List Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets) (hn : (X.clc i).resolved=none)
    (hr : Clc.Result L i X.clcState r) : ClcOk L (X.resolveClc i r) := by
  have _ := hn
  refine ⟨hX.1,hX.2.1,?_,?_,hX.2.2.2.2⟩
  · intro j he
    by_cases hj : j=i
    · subst j
      exact ⟨s,targets,hi⟩
    · exact hX.2.2.1 j (by simpa only [Execution.resolveClc,ite_eq_right hj] using he)
  · intro j t ts hj
    obtain ⟨he,hnd,htarget⟩ := hX.2.2.2.1 j t ts hj
    by_cases hji : j=i
    · subst j
      refine ⟨⟨hX.1,?_,?_,?_⟩,hnd,htarget⟩
      · intro q hq
        have hqr : r=q := by
          simpa [Execution.resolveClc] using hq
        exact hqr ▸ hr
      · intro c hc
        have ho : c∈(X.clc i).written := by
          simpa only [Execution.resolveClc,↓reduceIte] using hc
        exact ⟨(he.writes c ho).1,by simp [Execution.resolveClc]⟩
      · simpa [Execution.resolveClc] using he.notified
    · simpa only [Execution.resolveClc,ite_eq_right hji] using ⟨he,hnd,htarget⟩

/-- An unresolved issued request has not written any replica. -/
theorem clc_unresolved_unwritten {L : Launch} {X : Execution} {i : EvId}
    {s : Clc.Spec} {targets : List Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets) (hn : (X.clc i).resolved=none) (c : Nat) :
    c∉(X.clc i).written := by
  intro hw
  have hh := (hX.2.2.2.1 i s targets hi).1.writes c hw
  simp only [hn,Option.isSome_none,Bool.false_eq_true] at hh
  exact hh.2

/-- A resolve stage changes no actual memory write; only its later write
stages can introduce response bytes. -/
theorem resolveClc_memWrites {L : Launch} {X : Execution} {i : EvId} {r : ClcResponse}
    {s : Clc.Spec} {targets : List Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets) (hn : (X.clc i).resolved=none)
    {e : AsyncCopy.Ref} {a : Acc} {bs : List Byte} :
    (X.resolveClc i r).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => exact Iff.rfl
  | async j part =>
    cases part <;> try exact Iff.rfl
    case writeCta c =>
      by_cases hj : j=i
      · subst j
        have hc := clc_unresolved_unwritten hX hi hn c
        simp [Execution.MemWrites,Clc.ResponseWrite,Execution.resolveClc,hc]
      · simp only [Execution.MemWrites,Execution.resolveClc,ite_eq_right hj]
        rfl

/-- Existing RF witnesses remain valid when only the resolve stage is added. -/
theorem resolveClc_rf {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {r : ClcResponse}
    {s : Clc.Spec} {targets : List Nat} (hX : Consistent L K A mem0 X)
    (hi : X.ClcIssue i s targets) (hn : (X.clc i).resolved=none) :
    RfWf mem0 (X.resolveClc i r) := by
  intro e a bs he
  have hold : X.MemReads e a bs := he
  obtain ⟨hlen,hvalues⟩ := hX.rf e a bs hold
  refine ⟨hlen,?_⟩
  intro k hk
  have hv := hvalues k hk
  change match X.rf e k with
    | none => _
    | some w => _
  cases hsrc : X.rf e k with
  | none => simp only [hsrc] at hv ⊢; exact hv
  | some w =>
    rw [hsrc] at hv
    obtain ⟨dst,bytes,hw,hcover,hval⟩ := hv
    exact ⟨dst,bytes,(resolveClc_memWrites hX.clc hi hn).mpr hw,hcover,hval⟩

 theorem resolveClc_le {X : Execution} {i : EvId} {r : ClcResponse}
    (hn : (X.clc i).resolved=none) : X.le (X.resolveClc i r) := by
  have h := Execution.le_refl X
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    ?_,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro j
  by_cases hj : j=i
  · subst j
    simp only [Execution.resolveClc,↓reduceIte]
    refine ⟨?_,fun _ h => h,fun _ h => h⟩
    intro q hq
    rw [hn] at hq
    cases hq
  · simpa only [Execution.resolveClc,ite_eq_right hj] using Clc.Extends.refl (X.clc j)

 theorem resolveClc_asyncSize {X : Execution} {i j : EvId} {r : ClcResponse}
    (hn : (X.clc i).resolved=none) :
    (X.resolveClc i r).asyncSize j=if j=i then X.asyncSize j+1 else X.asyncSize j := by
  have hres (k : EvId) : ((X.resolveClc i r).clc k).resolved=
      if k=i then some r else (X.clc k).resolved := by
    by_cases hk : k=i <;> simp [Execution.resolveClc,hk]
  have hwr (k : EvId) : ((X.resolveClc i r).clc k).written=(X.clc k).written := by
    by_cases hk : k=i <;> simp [Execution.resolveClc,hk]
  have hnf (k : EvId) : ((X.resolveClc i r).clc k).notified=(X.clc k).notified := by
    by_cases hk : k=i <;> simp [Execution.resolveClc,hk]
  have helem (k : EvId) : (X.resolveClc i r).elemSize k=X.elemSize k := by
    obtain ⟨a, b⟩ := k
    rfl
  have hasync : (X.resolveClc i r).async=X.async := rfl
  have htensor : (X.resolveClc i r).tensor=X.tensor := rfl
  have hstores : (X.resolveClc i r).tensorStores=X.tensorStores := rfl
  have htc : (X.resolveClc i r).tcNotified=X.tcNotified := rfl
  by_cases hj : j=i
  · subst j
    simp only [Execution.asyncSize,hres,hwr,hnf,helem,hasync,htensor,hstores,htc,hn,
      Option.isSome_none,Option.isSome_some,Bool.false_eq_true,ite_false,ite_true]
    omega
  · rw [Execution.asyncSize,Execution.asyncSize,hres j,hwr j,hnf j,helem j,hasync,htensor,
      hstores,htc]
    simp only [ite_eq_right hj]

 theorem resolveClc_size {L : Launch} {X : Execution} {i : EvId} {r : ClcResponse}
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) (hn : (X.clc i).resolved=none) :
    (X.resolveClc i r).size L=X.size L+1 := by
  have hs (j : EvId) := resolveClc_asyncSize (X:=X) (i:=i) (j:=j) (r:=r) hn
  have heq (g k : Nat) : (g,k)=i ↔ g=i.1 ∧ k=i.2 := Prod.ext_iff
  have hthread (g : Nat) :
      ((List.range (X.tr g).length).map fun k => (X.resolveClc i r).asyncSize (g,k)).sum=
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+
          (if g=i.1 then 1 else 0) := by
    simp_rw [hs,heq]
    by_cases hg' : g=i.1
    · subst g
      simp only [true_and,↓reduceIte]
      exact sum_range_bump _ _ _ |>.trans (by rw [ite_eq_left hi])
    · simp only [hg',false_and,ite_false,Nat.add_zero]
  unfold Execution.size Execution.threadSize
  change ((List.range L.threads).map fun g =>
    (X.tr g).countP Event.counts+
      ((List.range (X.tr g).length).map fun k => (X.resolveClc i r).asyncSize (g,k)).sum).sum+
      X.pairSize L=_
  simp_rw [hthread]
  have hb := sum_range_bump
    (fun g => (X.tr g).countP Event.counts+
      ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum) i.1 L.threads
  rw [ite_eq_left hg] at hb
  have hh : ∀g, (X.tr g).countP Event.counts+
      (((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+
        (if g=i.1 then 1 else 0))=
      if g=i.1 then (X.tr g).countP Event.counts+
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+1
      else (X.tr g).countP Event.counts+
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum := by
    intro g
    split_ifs <;> omega
  simp_rw [hh]
  rw [hb]
  omega

end
end PTX
