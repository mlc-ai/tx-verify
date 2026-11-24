-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.BulkWait

@[expose] public section

/-! # A bulk-group wait after its operations are drained

A proof tool. An operation that a bulk-group wait covers is a tensor store or a bulk-group linear
copy issued in the waiting thread's prefix (`observed_source`). So when every tensor store issue
has finished all its effects and every bulk-group copy has read and written, every bulk-group
wait is ready (`ready_of_drained`, DEP-ORDER): the thread may go on after the wait, or some store
or copy is an open obligation. Conversely, a wait that returned has the stages it waits for of
every operation it covers (`stages_of_returned`), and each waited stage is a witness of the
wait (`witness_of_waitsFor`). -/

namespace PTX.Step.BulkWait

open PTX AsyncCopy

noncomputable section

variable {L : Launch} {X : Execution}

/-- An operation that a bulk-group wait observes is a tensor store issue or a linear copy
completed through the bulk group. -/
theorem observed_source {waiter i : EvId} {remaining : Nat}
    (hob : BulkGroup.Observes (bulkStateBefore X waiter) remaining i) :
    (∃ address spec, X.TensorStoreIssue i address spec) ∨
      ∃ s, X.Copy i s ∧ s.completion = .bulkGroup := by
  obtain ⟨ev, hev, hk⟩ := issue_of_waitsFor (act := bulkAction) (fun g index k i h => by
    unfold bulkAction at h
    split at h <;> grind) hob
  obtain ⟨pc, kind⟩ := ev
  cases kind <;> simp only [bulkAction] at hk <;> try cases hk
  case tensorStore address spec => exact .inl ⟨address, spec, pc, hev⟩
  case copy s =>
    split at hk
    · exact .inr ⟨s, ⟨pc, hev⟩, by assumption⟩
    · cases hk

/-- **A bulk-group wait is ready when the stores and the bulk-group copies are drained.** Every
operation it covers has the stages it waits for (`GroupWaitStages`). -/
theorem ready_of_drained {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {w : EvId} {pc : Nat} {mode : BulkGroup.WaitMode}
    {remaining : Nat} (hw : X.get w = some ⟨pc, .bulkWait mode remaining⟩)
    (hd : ∀ i address spec, X.TensorStoreIssue i address spec →
      ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true)
    (hc : ∀ i s, X.Copy i s → s.completion = .bulkGroup →
      X.AsyncPresent i (.read .copy) ∧ X.AsyncPresent i (.write .copy)) :
    Ready L X w := by
  intro n hn
  simp only [Needs, hw, KindNeeds, groupNeeds] at hn
  obtain ⟨j, -, hm⟩ := List.mem_flatMap.mp hn
  unfold needsIf at hm
  split_ifs at hm with hgw
  swap
  · simp at hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  refine ⟨_, ?_, rfl⟩
  show X.AsyncPresent (w.1, j) p
  obtain ⟨_, _, _, hob⟩ := (hgw : BulkWaitsFor X mode (w.1, j) w)
  rcases observed_source hob with ⟨address, spec, pci, hi⟩ | ⟨s, ⟨pci, hi⟩, hs⟩
  · obtain ⟨o, ho, hfull⟩ := hd _ address spec ⟨pci, hi⟩
    have hreads := ((hX.store _ o ho).2.2.complete hfull).1
    simp only [GroupWaitStages, hi, Option.map_some] at hp
    cases mode <;> simp at hp <;> rcases hp with rfl | rfl <;>
      first | exact ⟨o, ho, hreads⟩ | exact ⟨o, ho, hfull⟩
  · obtain ⟨hr, hwr⟩ := hc _ s ⟨pci, hi⟩ hs
    simp only [GroupWaitStages, hi, Option.map_some] at hp
    cases mode <;> simp at hp <;> rcases hp with rfl | rfl <;> assumption

/-- **The waited stages of an operation are needs of the bulk-group wait covering it**: the
operation is issued earlier in the waiter's thread, and the wait needs its stages
`GroupWaitStages` (DEP-ASYNC-STAGE-ORDER). -/
theorem stage_need {i w : EvId} {mode : BulkGroup.WaitMode} (hw : BulkWaitsFor X mode i w)
    {q : Part} (hq : q ∈ GroupWaitStages X i (.bulk mode)) :
    Need.node (· = AsyncCopy.Ref.async i q) ∈ Needs L X w := by
  have hgw : GroupWaitsFor X (.bulk mode) i w := hw
  obtain ⟨pc, remaining, hget, hob⟩ := hw
  obtain ⟨hi1, ev, hev, -⟩ := issue_mem_actions (act := bulkAction) (fun g index k i h => by
    unfold bulkAction at h
    split at h <;> grind) (BulkGroup.issue_of_observes hob)
  have hi2 : i.2 < w.2 := by
    have := (List.getElem?_eq_some_iff.mp hev).1
    simp only [List.length_take] at this
    omega
  have hi : (w.1, i.2) = i := Prod.ext hi1.symm rfl
  simp only [Needs, hget, KindNeeds, groupNeeds]
  refine List.mem_flatMap.mpr ⟨i.2, List.mem_range.mpr hi2, ?_⟩
  rw [hi]
  unfold needsIf
  rw [ite_eq_left hgw]
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- **A waited stage is a witness of the bulk-group wait covering its operation.** -/
theorem witness_of_waitsFor {i w : EvId} {mode : BulkGroup.WaitMode}
    (hw : BulkWaitsFor X mode i w) {q : Part} (hq : q ∈ GroupWaitStages X i (.bulk mode))
    (hp : X.AsyncPresent i q) : Witness L X (.async i q) w :=
  Witness.of_need L (stage_need hw hq) hp rfl

/-- **A returned bulk-group wait has the stages it waits for**: they are needs of the wait
(`stage_need`), which DEP-ORDER fills once the wait has returned. -/
theorem stages_of_returned {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {i w : EvId} {mode : BulkGroup.WaitMode}
    (hw : BulkWaitsFor X mode i w) (hlt : w.2 + 1 < (X.tr w.1).length) :
    ∀ q ∈ GroupWaitStages X i (.bulk mode), X.AsyncPresent i q := by
  have hret : Returned X w := by
    obtain ⟨pc, remaining, hget, -⟩ := hw
    simp [Returned, hget, Kind.resume, hlt]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := hX.dependency.ready w hret _ (stage_need hw hq)
  exact hx

end

end PTX.Step.BulkWait
