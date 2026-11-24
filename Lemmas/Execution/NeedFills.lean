-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Mathlib.Tactic.ByContra

@[expose] public section

/-! The nodes that fill a need of a thread instruction (DEP-ORDER) are thread nodes, the stages
that a group wait covers, and the ids of recorded object updates. An extension that keeps the
events, the object histories and the presence of these nodes keeps the needs and the readiness
of every event. -/
namespace PTX
open AsyncCopy
noncomputable section

variable {L : Launch} {X : Execution}

/-- A node that can fill a need: a thread node, a stage of a group-wait-covered operation, or the
id of a recorded object update. -/
def NeedRef (X : Execution) (x : Ref) : Prop :=
  (∃ t, x = .thread t) ∨ (∃ a k p, x = .async a p ∧ p ∈ GroupWaitStages X a k) ∨
    ∃ m r, r ∈ X.objects m ∧ x = r.id

theorem needs_node_cases {j : EvId} {fills : Ref → Prop} (hn : Need.node fills ∈ Needs L X j)
    {x : Ref} (hf : fills x) : NeedRef X x := by
  unfold Needs at hn
  cases hg : X.get j with
  | none => simp [hg] at hn
  | some ev =>
    simp only [hg] at hn
    cases hk : ev.kind <;> simp [KindNeeds, hk, maskNeeds, tcNeeds, ctaBarNeeds, ctaBarWarpNeeds,
      clusterNeeds, clusterWarpNeeds, resourceNeeds, groupNeeds, pollNeeds, needsIf,
      warpLanes] at hn
    all_goals try (obtain ⟨a', -, rfl⟩ := hn; obtain ⟨t, rfl, -⟩ := hf; exact .inl ⟨_, rfl⟩)
    all_goals try (split at hn <;> simp at hn <;> obtain ⟨l, -, rfl⟩ := hn <;>
      obtain ⟨t, rfl, -⟩ := hf; exact .inl ⟨_, rfl⟩)
    case bar =>
      rcases hn with ⟨a', -, rfl⟩ | hn
      · obtain ⟨i, r, -, -, b, rfl, -⟩ := hf
        exact .inl ⟨_, rfl⟩
      · rename_i mode
        cases mode
        · simp at hn
          obtain ⟨a1, b1, -, -, rfl⟩ := hn
          exact .inl ⟨_, hf⟩
        · simp at hn
    case cluster =>
      rcases hn with ⟨a', -, rfl⟩ | hn
      · obtain ⟨i, r, -, -, b, rfl, -⟩ := hf
        exact .inl ⟨_, rfl⟩
      · rename_i op
        cases op
        · simp at hn
        · simp at hn
          obtain ⟨a1, b1, -, -, rfl⟩ := hn
          exact .inl ⟨_, hf⟩
    case wait =>
      obtain ⟨-, r, hr, -, rfl⟩ := hn
      exact .inr (.inr ⟨_, r, hr, hf⟩)
    case bulkWait =>
      obtain ⟨a', -, -, q, hq, rfl⟩ := hn
      exact .inr (.inl ⟨_, _, q, hf, hq⟩)
    case asyncWait =>
      obtain ⟨a', -, -, q, hq, rfl⟩ := hn
      exact .inr (.inl ⟨_, _, q, hf, hq⟩)
    case tc =>
      rename_i k
      cases k <;> simp at hn
      all_goals try (obtain ⟨a', -, rfl⟩ := hn; obtain ⟨t, rfl, -⟩ := hf; exact .inl ⟨_, rfl⟩)
      rename_i h
      rcases h with ⟨-, hn | hn⟩ | hresult
      · split at hn <;> simp at hn
        obtain ⟨l, rfl⟩ := hn
        obtain ⟨a, b, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := hf <;> exact .inl ⟨_, rfl⟩
      · split at hn <;> simp at hn
        obtain ⟨a1, -, -, l, rfl⟩ := hn
        obtain ⟨d, -, rfl⟩ := hf
        exact .inl ⟨_, rfl⟩
      · cases Tmem.Pair.allocResultNeeds_node L hresult
        obtain ⟨store, _, _, _, rfl, _⟩ := Tmem.Pair.AllocResultFill.written L hf
        exact .inl ⟨store, rfl⟩

/-- The needs of an extension that keeps the events and the polls' observed updates. -/
theorem needs_congr {Y : Execution} (hget : ∀ e, Y.get e = X.get e)
    (hk : ∀ k e, (∀ m q ok a s, k ≠ Kind.wait m q ok a s) → KindNeeds L Y k e = KindNeeds L X k e)
    (hp : ∀ e m, pollNeeds Y e m = pollNeeds X e m) (e : EvId) : Needs L Y e = Needs L X e := by
  unfold Needs
  rw [hget e]
  cases X.get e with
  | none => rfl
  | some ev =>
    simp only
    by_cases hw : ∃ m q ok a s, ev.kind = Kind.wait m q ok a s
    · obtain ⟨m, q, ok, a, s, hw⟩ := hw
      rw [hw]
      simp only [KindNeeds, hp]
    · exact hk ev.kind e fun m q ok a s h => hw ⟨m, q, ok, a, s, h⟩

/-- The poll needs of an extension that keeps the object histories and the observation of the
recorded updates. -/
theorem pollNeeds_congr {Y : Execution} (hobj : ∀ m, Y.objects m = X.objects m)
    (hmb : ∀ m r, r ∈ X.objects m → ∀ w, MbarObserved Y r.id w ↔ MbarObserved X r.id w)
    (e : EvId) (m : Loc) : pollNeeds Y e m = pollNeeds X e m := by
  unfold pollNeeds
  rw [hobj m]
  refine List.flatMap_congr fun r hr => ?_
  unfold needsIf
  by_cases hP : MbarObserved X r.id (.thread e)
  · simp only [hP, (hmb m r hr _).mpr hP, ↓reduceIte]
  · simp only [hP, mt (hmb m r hr _).mp hP, ↓reduceIte]

/-- Readiness transfers to an extension with the same needs whose nodes that fill a need stay
present. -/
theorem ready_congr {Y : Execution} (hneeds : ∀ e, Needs L Y e = Needs L X e)
    (hret : ∀ e, Returned Y e → Returned X e)
    (hpres : ∀ j fills x, Need.node fills ∈ Needs L X j → fills x → X.RefPresent x →
      Y.RefPresent x)
    (hX : ∀ e, Returned X e → Ready L X e) : ∀ e, Returned Y e → Ready L Y e := by
  intro e hr n hn
  rw [hneeds] at hn
  have h := hX e (hret e hr) n hn
  cases n with
  | cond holds => exact h
  | node fills =>
    obtain ⟨x, hx, hf⟩ := h
    exact ⟨x, hpres e fills x hn hf hx, hf⟩

theorem groupWaitStages_cases (X : Execution) (a : EvId) (k : GroupWait) {p : Part}
    (hp : p ∈ GroupWaitStages X a k) :
    p = .readsDone ∨ p = .fullDone ∨ p = .read .copy ∨ p = .write .copy := by
  unfold GroupWaitStages at hp
  split at hp <;> simp at hp <;> tauto

/-- The updates that an object records are thread operations and the notifications of copies,
tensor loads, CLC responses, commits and `cp.async.mbarrier.arrive`. -/
theorem record_id_cases (ho : ObjectsOk X) {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) :
    (∃ t, r.id = .thread t) ∨ (∃ j, r.id = .async j (.notify .copy)) ∨
      (∃ j, r.id = .async j (.notify .load)) ∨ (∃ j c, r.id = .async j (.notify (.cta c))) ∨
      (∃ j, r.id = .async j .arriveOn) ∨ ∃ j rank, r.id = .async j (.tcNotify rank) := by
  have hm := ((ho m).2.1 r hr).1
  generalize r.id = id at hm ⊢
  cases id with
  | thread t => exact .inl ⟨t, rfl⟩
  | async j p =>
    cases p <;> simp [objectAction] at hm
    case notify t =>
      cases t
      · exact .inr (.inl ⟨j, rfl⟩)
      · exact .inr (.inr (.inl ⟨j, rfl⟩))
      · exact .inr (.inr (.inr (.inl ⟨j, _, rfl⟩)))
    case tcNotify => exact .inr (.inr (.inr (.inr (.inr ⟨j, _, rfl⟩))))
    case arriveOn => exact .inr (.inr (.inr (.inr (.inl ⟨j, rfl⟩))))

/-- Atomicity transports to an extension that keeps the atomic operations, their old reads and
their morally strong pairs. -/
theorem atomicOk_congr {Y : Execution} (hat : ∀ p l n, Y.RmwAt p l n ↔ X.RmwAt p l n)
    (hs : ∀ p q, RmwStrong L Y p q ↔ RmwStrong L X p q)
    (hold : ∀ p k, Y.oldRf p k = X.oldRf p k) (h : AtomicOk L X) : AtomicOk L Y := by
  refine ⟨fun p q l n k hp hq hne hst hk => ?_, fun p hc => ?_⟩
  · rw [hold, hold]
    exact h.unique p q l n k ((hat p l n).mp hp) ((hat q l n).mp hq) hne ((hs p q).mp hst) hk
  · refine h.acyclic p (Relation.TransGen.mono (fun a b hab => ?_) _ _ hc)
    obtain ⟨l, n, h1, h2, h3, k, k', hk, hr⟩ := hab
    exact ⟨l, n, (hat a l n).mp h1, (hat b l n).mp h2, (hs a b).mp h3, k, k', hk,
      by rw [← hold]; exact hr⟩

/-- An event that needs a node that is not present has not returned. -/
theorem not_returned_of_need {w : EvId} {x : Ref} (hready : Returned X w → Ready L X w)
    (hn : Need.node (· = x) ∈ Needs L X w) (hx : ¬ X.RefPresent x) : ¬ Returned X w := by
  intro hr
  obtain ⟨y, hy, rfl⟩ := hready hr _ hn
  exact hx hy

/-- A group wait that has not returned is the last event of its thread. -/
theorem last_of_not_returned_bulkWait {w : EvId} {pc : Nat} {mode : BulkGroup.WaitMode}
    {rem : Nat} (hg : X.get w = some ⟨pc, .bulkWait mode rem⟩) (hr : ¬ Returned X w) :
    (X.tr w.1).length ≤ w.2 + 1 := by
  unfold Returned at hr
  simp only [hg, Kind.resume] at hr
  omega

end
end PTX
