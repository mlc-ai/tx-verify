-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocObjectWaiting

@[expose] public section

/-! The execution-order axioms after appending one event whose two nodes are a sink: the event
is ordinary and waits for nothing (`Kind.WaitFree`), is no shuffle, fills no need of any event and
starts no causality. Object histories are given separately, so the same frame serves a plain
append and an append with records of the appended event. -/
namespace PTX
open AsyncCopy
noncomputable section

/-- The appended event of thread `g` adds no waiting edge out of its own nodes. -/
structure SnocWaitFrame (L : Launch) (X : Execution) (g : Nat) (e : Event)
    (r : Nat → Option Ref) : Prop where
  waitFree : e.kind.WaitFree
  noShfl : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok
  notWitness : ∀ j, ¬ Witness L (X.snoc g e r) (.thread (X.newId g)) j
  noBase : ∀ f, ¬ baseCausality L (X.snoc g e r) (X.newId g) f

namespace SnocWaitFrame
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
    {records : Loc → List (MBarrier.Record Ref)}
    {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- An ordinary event that waits for nothing, is no shuffle, exit, lane-value collective, matrix
event, releasing arrival or releasing atomic. -/
theorem of_waitFree (hX : Consistent L K A mem0 X) (hk : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok) (hx : e.kind ≠ .exit)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hrmw : ∀ a old new, e.kind = .rmw a old new → a.release = false)
    (hpublish : ∀ j, ¬ Tmem.Pair.AllocResultFill L (X.snoc g e r) j (.thread (X.newId g))) :
    SnocWaitFrame L X g e r where
  waitFree := hk
  noShfl := hns
  notWitness := fun j => snoc_new_not_witness hX hk hns (fun h => absurd h hx) hlv hmat
    (hpublish j)
  noBase := fun _ => snoc_no_baseCausality_from_new_of_not_arrive hna
    (fun a bs he => by have h := hk.ordinary; rw [he] at h; exact h) hrmw
    (fun s he => by have h := hk.ordinary; rw [he] at h; exact h)

/-- An exit appended to a thread that has not exited. -/
theorem of_exit (hX : Consistent L K A mem0 X) (he : e.kind = .exit)
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) : SnocWaitFrame L X g e r where
  waitFree := .of_plain (by rw [he]; rfl)
  noShfl := by intros; rw [he]; simp
  notWitness := fun j => snoc_new_not_witness hX (.of_plain (by rw [he]; rfl))
    (by intros; rw [he]; simp) (fun _ => hgx) (by rw [he]; rfl)
    (by obtain ⟨pc, k⟩ := e; simp only at he; subst he; rfl)
    (snoc_not_allocResult_of_not_wr (by simp [he]) j)
  noBase := fun _ => snoc_no_baseCausality_from_new_of_not_arrive (by intros; rw [he]; simp)
    (by intros _ _ h; rw [he] at h; cases h) (by intros _ _ _ h; rw [he] at h; cases h)
    (by intros; rw [he]; simp)

/-- A need of an old event that the appended node fills in an append whose histories only gain
records of the appended event is a need it fills in the plain append: a poll of an old event
observes no record of the appended event, since the poll's own record precedes every such
record. -/
theorem witness_snocHistory (hX : Consistent L K A mem0 X) (hrec : SnocRecords X g records)
    {j : EvId} (hj : j ≠ X.newId g)
    (h : Witness L (X.snocHistory g e r records) (.thread (X.newId g)) j) :
    Witness L (X.snoc g e r) (.thread (X.newId g)) j := by
  obtain ⟨fills, hmem, hp, hf⟩ := h
  refine ⟨fills, ?_, hp, hf⟩
  have hget' : (X.snocHistory g e r records).get j = (X.snoc g e r).get j := rfl
  unfold Needs at hmem ⊢
  rw [hget'] at hmem
  cases hget : (X.snoc g e r).get j with
  | none => simp [hget] at hmem
  | some ev =>
  simp only [hget] at hmem ⊢
  obtain ⟨pc, k⟩ := ev
  cases k
  case wait m q ok acq sc =>
    cases ok
    · simp [KindNeeds] at hmem
    exfalso
    simp only [KindNeeds, ite_true, pollNeeds] at hmem
    obtain ⟨rc, -, hm⟩ := List.mem_flatMap.mp hmem
    by_cases hob : MbarObserved (X.snocHistory g e r records) rc.id (.thread j)
    swap
    · simp [needsIf, hob] at hm
    simp only [needsIf, hob, ite_true, List.mem_singleton] at hm
    obtain rfl := Need.node.inj hm
    obtain ⟨-, j', l, acq', ws, hj', ⟨-, i, i', ru, w, ph, hru, hid, -, hw, hwid, -, -, hlt, -⟩,
      -⟩ := hob
    cases hj'
    obtain ⟨L', hl, hq⟩ := hrec l
    change (records l)[i]? = some ru at hru
    change (records l)[i']? = some w at hw
    rw [hl] at hru hw
    by_cases hi : i < (X.objects l).length
    · rw [List.getElem?_append_left hi] at hru
      exact snoc_fresh_object_id hX.tma (List.mem_of_getElem? hru) (hid.trans hf.symm)
    · have hi' : (X.objects l).length ≤ i' := by omega
      rw [List.getElem?_append_right hi'] at hw
      have := hq w (List.mem_of_getElem? hw)
      rw [hwid] at this
      exact hj (Ref.thread.inj this)
  case tc k => cases k <;> exact hmem
  all_goals exact hmem

/-- The appended event has no dependency to another event. -/
theorem from_new (hf : SnocWaitFrame L X g e r) (hX : Consistent L K A mem0 X)
    (hrec : SnocRecords X g records)
    (hno : ∀ m f, ¬ MBarrier.Before (records m) (.thread (X.newId g)) f)
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.snocHistory g e r records) (.thread (X.newId g),b) v) :
    b = false ∧ v = (.thread (X.newId g),true) := by
  have hk := hf.waitFree
  have hord := hk.ordinary
  have noOld : ¬ Waits L X (.thread (X.newId g),b) v := by
    intro hw
    obtain ⟨ev,he⟩ := (waits_present hX.effectValidity hw).1
    have hl := len_of_get he
    simp at hl
  rcases h with ⟨heq,hb,hb',_⟩ | ⟨_,_,i,j,hi,_,hij,hs,hl⟩ |
    ⟨i,j,hi,hj,hbar⟩ | ⟨_,_,i,j,hi,_,_,n,his,_⟩ |
    ⟨_,_,i,j,hi,_,_,k,hit,_⟩ | ⟨h1,h2,ha⟩ | ⟨h1,h2,m,ho⟩ |
    ⟨i,j,hi,hj,hcl⟩ | ⟨h1,h2,j,hj,hw⟩ | ⟨h1,h2,i,j,hi,hj,hw⟩ |
    ⟨h1,h2,i,j,hi,hj,hw⟩ | ⟨i,j,hi,hj,hw⟩ | ⟨h1,h2,i,j,hi,hj,cta,hp⟩ |
    ⟨h1,h2,i,j,hi,hj,hw⟩ | ⟨h1,h2,hi⟩
  · exact ⟨hb,Prod.ext heq.symm hb'⟩
  · cases hi
    change j.2 < ((X.snoc g e r).tr j.1).length at hl
    rw [← hij,snoc_len,ite_eq_left rfl] at hl
    simp only at hs; omega
  · cases hi
    obtain ⟨ev,he⟩ := (ctaWaits_snoc_old (r := r) hX.ctaBar hbar).1
    have hl := len_of_get he; simp at hl
  · cases hi
    have hl := ((snoc_shflK (X := X) (r := r) hf.noShfl).mp his).1; simp at hl
  · cases hi
    have hl := ((snoc_tcK (X := X) (r := r) hk.notTc).mp hit).lt; simp at hl
  · rcases ha with ⟨-, hb0, -⟩ | ⟨-, -, hs⟩
    · rw [h1] at hb0; cases hb0
    · simp [StageEdge] at hs
  · exact (hno m _ ho).elim
  · cases hi
    obtain ⟨ev,he⟩ := (clusterWaits_snoc_old (r := r) hX.cluster hcl).1
    have hl := len_of_get he; simp at hl
  · by_cases hjn : j = X.newId g
    · subst hjn; exact ⟨h1, Prod.ext hj h2⟩
    · exact (hf.notWitness j (witness_snocHistory hX hrec hjn hw)).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1,h2,i,j,hi,hj,(snoc_warpWaits (r := r) hord).mp hw⟩))))))))))).elim
  · cases hi
    exact (hf.noBase j (.single (.inr (.inr (.inr (.inr (.inr (.inl hw)))))))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨i,j,hi,hj,(snoc_regWaits (r := r) hord).mp hw⟩))))))))))))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1,h2,i,j,hi,hj,cta,hp⟩)))))))))))))).elim
  · cases hi
    exact (hf.noBase j (.single (.inr (.inr (.inr (.inr (.inr (.inr hw)))))))).elim
  · obtain ⟨-, -, i, p, he, -, -, hap, -⟩ := hi
    have hl := refPresent_issuer_lt hX.effectValidity (f := .async _ p)
      ((snoc_asyncPresent_of_not_tc (r := r) hk.notTc).mp hap)
    rw [← Ref.thread.inj he] at hl
    exact absurd hl (lt_irrefl _)

/-- Appending the event with object histories that only gain its own records, none followed
by another record, is a sink frame for the event's two nodes. -/
theorem history_sinkFrame (hf : SnocWaitFrame L X g e r) (hX : Consistent L K A mem0 X)
    (hrec : SnocRecords X g records)
    (hno : ∀ m f, ¬ MBarrier.Before (records m) (.thread (X.newId g)) f) :
    SinkFrame L K A X (X.snocHistory g e r records) (fun x => x.1 = .thread (X.newId g)) :=
  snoc_sinkFrame hX (fun _ h => h) (fun _ h => Ref.thread.inj h) hrec
    (fun _ _ h => (snoc_asyncPresent_of_not_tc hf.waitFree.notTc).mp h)
    (fun _ _ hj h => baseCausality_snocHistory_ordinary hX hrec hf.waitFree.ordinary _ _ hj h)
    (snoc_closed fun _ _ h => hf.from_new hX hrec hno h)

/-- Appending the event together with its own record on one object. -/
theorem object_sinkFrame (hf : SnocWaitFrame L X g e r) (hX : Consistent L K A mem0 X)
    (m : Loc) (rec : MBarrier.Record Ref) (hid : rec.id = .thread (X.newId g)) :
    SinkFrame L K A X ((X.snoc g e r).appendObject m rec)
      (fun x => x.1 = .thread (X.newId g)) := by
  apply hf.history_sinkFrame hX (SnocRecords.append hid)
  intro l f hb
  have old_record : ∃ q ∈ X.objects l, q.id = .thread (X.newId g) := by
    by_cases hl : l = m
    · subst l
      simp only [↓reduceIte] at hb
      obtain ⟨a, b, qa, qb, ha, hid', hb, _, hab⟩ := hb
      have hbl := (List.getElem?_eq_some_iff.mp hb).1
      have hal : a < (X.objects m).length := by
        simp only [List.length_append, List.length_singleton] at hbl
        omega
      rw [List.getElem?_append_left hal] at ha
      exact ⟨qa, List.mem_of_getElem? ha, hid'⟩
    · simp only [ite_eq_right hl] at hb
      obtain ⟨a, b, qa, qb, ha, hid', _⟩ := hb
      exact ⟨qa, List.mem_of_getElem? ha, hid'⟩
  obtain ⟨q, hq, hid'⟩ := old_record
  exact snoc_fresh_object_id hX.tma hq hid'

/-- Appending the event with every object history unchanged. -/
theorem sinkFrame (hf : SnocWaitFrame L X g e r) (hX : Consistent L K A mem0 X) :
    SinkFrame L K A X (X.snoc g e r) (fun x => x.1 = .thread (X.newId g)) := by
  apply hf.history_sinkFrame hX (records := X.objects) SnocRecords.same
  rintro m f ⟨a, b, qa, qb, ha, hid, _⟩
  exact snoc_fresh_object_id hX.tma (List.mem_of_getElem? ha) hid

theorem orderOk (hf : SnocWaitFrame L X g e r) (hX : Consistent L K A mem0 X) :
    OrderOk L K A (X.snoc g e r) :=
  (hf.sinkFrame hX).orderOk hX.orderOk

theorem objectOrderOk (hf : SnocWaitFrame L X g e r) (hX : Consistent L K A mem0 X)
    (m : Loc) (rec : MBarrier.Record Ref) (hid : rec.id = .thread (X.newId g)) :
    OrderOk L K A ((X.snoc g e r).appendObject m rec) :=
  (hf.object_sinkFrame hX m rec hid).orderOk hX.orderOk

end SnocWaitFrame

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
    {K : Kernel} {A : List Assumption} {mem0 : Mem0}

end
end
end PTX
