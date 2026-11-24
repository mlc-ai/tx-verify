-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocOrder
public import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! Ordinary thread events preserve the issued async operations, their independent
stages and their object histories. No restriction on the number of phases, writers or
async operations is used by these lemmas. -/
namespace PTX
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event}
  {r : Nat → Option AsyncCopy.Ref}

theorem snoc_tc_old (hk : ∀ k, e.kind ≠ .tc k) {v : EvId} {pc : Nat} {k : TcKind}
    (h : (X.snoc g e r).get v = some ⟨pc, .tc k⟩) : X.get v = some ⟨pc, .tc k⟩ := by
  rw [snoc_get] at h
  split_ifs at h with hv
  · exact absurd (congrArg Event.kind (Option.some.inj h)) (hk k)
  · exact h

theorem snoc_tc_iff (hk : ∀ k, e.kind ≠ .tc k) {v : EvId} {pc : Nat} {k : TcKind} :
    (X.snoc g e r).get v = some ⟨pc, .tc k⟩ ↔ X.get v = some ⟨pc, .tc k⟩ :=
  ⟨snoc_tc_old hk, fun h => by rw [snoc_get_old (len_of_get h)]; exact h⟩

theorem snoc_commit (hk : ∀ k, e.kind ≠ .tc k) {v : EvId} {s : TcCommit.Spec} :
    (X.snoc g e r).Commit v s ↔ X.Commit v s :=
  exists_congr fun _ => snoc_tc_iff hk

theorem snoc_mmaIssue (hk : ∀ k, e.kind ≠ .tc k)
    {i : EvId} {d : Nat} {spec : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} :
    (X.snoc g e r).MmaIssue i d spec accum mask ↔ X.MmaIssue i d spec accum mask :=
  exists_congr fun _ => snoc_tc_iff hk

theorem snoc_cpIssue (hk : ∀ k, e.kind ≠ .tc k) {i : EvId} {c : TcCopy.Spec} :
    (X.snoc g e r).CpIssue i c ↔ X.CpIssue i c :=
  exists_congr fun _ => snoc_tc_iff hk

theorem snoc_shiftIssue (hk : ∀ k, e.kind ≠ .tc k) {i : EvId} {s : TcShift.Spec} :
    (X.snoc g e r).ShiftIssue i s ↔ X.ShiftIssue i s :=
  exists_congr fun _ => snoc_tc_iff hk

theorem snoc_tcAsync (hk : ∀ k, e.kind ≠ .tc k) {i : EvId} :
    (X.snoc g e r).TcAsync i ↔ X.TcAsync i := by
  simp only [Execution.TcAsync, snoc_mmaIssue hk, snoc_cpIssue hk, snoc_shiftIssue hk]

theorem isTcColl_tc {ev : Event} (h : isTcColl ev = true) : ∃ pc k, ev = ⟨pc, .tc k⟩ := by
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp [isTcColl] at h
  exact ⟨pc, _, rfl⟩

theorem snoc_tcK (hk : ∀ k, e.kind ≠ .tc k) {v : EvId} {n : Nat} :
    (X.snoc g e r).TcK v n ↔ X.TcK v n := by
  constructor
  · rintro ⟨⟨ev, hv, hc⟩, hn⟩
    obtain ⟨pc, kd, rfl⟩ := isTcColl_tc hc
    have hv' := snoc_tc_old hk hv
    refine ⟨⟨_, hv', hc⟩, ?_⟩
    rwa [snoc_take (len_of_get hv').le] at hn
  · rintro ⟨⟨ev, hv, hc⟩, hn⟩
    have hlt := len_of_get hv
    exact ⟨⟨ev, by rw [snoc_get_old hlt]; exact hv, hc⟩, by rwa [snoc_take hlt.le]⟩


theorem plain_not_tc (hk : e.kind.isTma = false) : ∀ k, e.kind ≠ .tc k := by
  intro k he; rw [he] at hk; cases hk

theorem snoc_issuedBy (hk : e.kind.isTma = false) :
    AsyncCopy.issuedBy (X.snoc g e r) = AsyncCopy.issuedBy X := by
  funext i
  unfold AsyncCopy.issuedBy
  rw [snoc_get]
  split_ifs with hi
  · subst hi
    have hn : X.get (g, (X.tr g).length) = none := List.getElem?_eq_none (le_refl _)
    rw [hn]
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp_all [Kind.isTma]
  · rfl

/-- Appending a non-tc instruction preserves independently performed stages, even
when the new instruction itself initializes, arrives at, or polls an mbarrier. -/
theorem snoc_mmaRead (hk : ∀ k, e.kind ≠ .tc k)
    {i : EvId} {isB : Bool} {k : Nat} {loc : Loc} {byte : Option Byte} :
    (X.snoc g e r).MmaRead i isB k loc byte ↔ X.MmaRead i isB k loc byte := by
  simp only [Execution.MmaRead,Execution.MmaFootprint,snoc_mmaIssue hk,snoc_cpIssue hk,snoc_async]

theorem snoc_bulkWaits (hw : ∀ mode n, e.kind ≠ .bulkWait mode n)
    {mode : BulkGroup.WaitMode} {i w : EvId} :
    BulkWaitsFor (X.snoc g e r) mode i w ↔ BulkWaitsFor X mode i w := by
  have old {pc n : Nat} (hp : (X.snoc g e r).get w = some ⟨pc,.bulkWait mode n⟩) :
      X.get w = some ⟨pc,.bulkWait mode n⟩ := by
    rw [snoc_get] at hp
    split_ifs at hp
    · exact (hw mode n (congrArg Event.kind (Option.some.inj hp))).elim
    · exact hp
  constructor
  · rintro ⟨pc,n,hp,hs⟩
    have hp' := old hp
    refine ⟨pc,n,hp',?_⟩
    simpa only [bulkStateBefore,snoc_take (len_of_get hp').le] using hs
  · rintro ⟨pc,n,hp,hs⟩
    refine ⟨pc,n,Execution.le_get le_snoc hp,?_⟩
    simpa only [bulkStateBefore,snoc_take (len_of_get hp).le] using hs

theorem snoc_asyncPresent_of_not_tc (hk : ∀ k, e.kind ≠ .tc k)
    {i : EvId} {p : AsyncCopy.Part} :
    (X.snoc g e r).AsyncPresent i p ↔ X.AsyncPresent i p := by
  cases p <;> simp only [Execution.AsyncPresent, snoc_mmaRead hk, snoc_async]
  all_goals rfl

theorem snoc_tracksMma_of_not_tc (hk : ∀ k, e.kind ≠ .tc k) {x c : EvId} :
    AsyncCopy.TracksMma (X.snoc g e r) x c ↔ AsyncCopy.TracksMma X x c := by
  simp only [AsyncCopy.TracksMma, snoc_tcAsync hk, snoc_commit hk]

theorem snoc_asyncPresent (hk : e.kind.isTma = false) {i : EvId} {p : AsyncCopy.Part} :
    (X.snoc g e r).AsyncPresent i p ↔ X.AsyncPresent i p :=
  snoc_asyncPresent_of_not_tc (plain_not_tc hk)

theorem snoc_tracksMma (hk : e.kind.isTma = false) {x c : EvId} :
    AsyncCopy.TracksMma (X.snoc g e r) x c ↔ AsyncCopy.TracksMma X x c :=
  snoc_tracksMma_of_not_tc (plain_not_tc hk)

theorem snoc_acquireWait (hk : e.kind.isTma = false) {w : EvId} {m : Loc} :
    (X.snoc g e r).AcquireWait w m ↔ X.AcquireWait w m := by
  by_cases hw : w = (g,(X.tr g).length)
  · have hn : X.get w = none := by rw [hw]; exact List.getElem?_eq_none (le_refl _)
    simp only [Execution.AcquireWait,snoc_get,ite_eq_left hw,hn]
    cases e with | mk pc kind =>
      cases kind <;> simp_all [Kind.isTma]
  · simp only [Execution.AcquireWait,snoc_get,ite_eq_right hw]

theorem snoc_wait (hk : e.kind.isTma = false) {w : EvId} {pc : Nat} {m : Loc} {q : Nat}
    {ok acq : Bool} {sc : MbarScope} :
    (X.snoc g e r).get w = some ⟨pc, .wait m q ok acq sc⟩ ↔
      X.get w = some ⟨pc, .wait m q ok acq sc⟩ := by
  by_cases hw : w = (g,(X.tr g).length)
  · have hn : X.get w = none := by rw [hw]; exact List.getElem?_eq_none (le_refl _)
    simp only [snoc_get,ite_eq_left hw,hn]
    cases e with | mk pc kind =>
      cases kind <;> simp_all [Kind.isTma]
  · simp only [snoc_get,ite_eq_right hw]

theorem snoc_waitObserves (hk : e.kind.isTma = false) {x : AsyncCopy.Ref} {w : EvId} {m : Loc}
    {acq : Bool} {ws : MbarScope} :
    AsyncCopy.WaitObserves (X.snoc g e r) x w m acq ws ↔ AsyncCopy.WaitObserves X x w m acq ws := by
  simp only [AsyncCopy.WaitObserves, snoc_wait hk, snoc_objects]

theorem snoc_objectAction (hk : e.kind.isTma = false) (m : Loc) (id : AsyncCopy.Ref) :
    AsyncCopy.objectAction (X.snoc g e r) X.async m id =
      AsyncCopy.objectAction X X.async m id := by
  cases id with
  | thread i =>
    simp only [AsyncCopy.objectAction]
    rw [snoc_get]
    split_ifs with hi
    · subst hi
      have hn : X.get (g, (X.tr g).length) = none := List.getElem?_eq_none (le_refl _)
      rw [hn]
      obtain ⟨pc, kind⟩ := e
      cases kind <;> simp_all [Kind.isTma]
    · rfl
  | async i p =>
    cases p <;> simp only [AsyncCopy.objectAction]
    all_goals first

      | (rw [snoc_issuedBy hk])
      | (rw [snoc_get]
         split_ifs with hi
         · subst hi
           have hn : X.get (g,(X.tr g).length) = none := List.getElem?_eq_none (le_refl _)
           rw [hn]
           obtain ⟨pc,kind⟩ := e
           cases kind <;> simp_all [Kind.isTma]
         · rfl)

theorem snoc_objectsOk (hk : e.kind.isTma = false) (ho : AsyncCopy.ObjectsOk X) :
    AsyncCopy.ObjectsOk (X.snoc g e r) := by
  intro m
  obtain ⟨hv, hm, hc⟩ := ho m
  refine ⟨hv, ?_, ?_⟩
  · intro rec hr
    simpa only [snoc_async, snoc_objectAction hk] using hm rec hr
  · intro id action hid
    apply hc id action
    simpa only [snoc_async, snoc_objectAction hk] using hid

theorem snoc_tcEffectsOk (hk : e.kind.isTma = false) (ht : AsyncCopy.TcEffectsOk X) :
    AsyncCopy.TcEffectsOk (X.snoc g e r) := by
  simpa only [AsyncCopy.TcEffectsOk, snoc_async, snoc_commit (plain_not_tc hk),
    snoc_tracksMma hk, snoc_mmaIssue (plain_not_tc hk), snoc_cpIssue (plain_not_tc hk),
    snoc_shiftIssue (plain_not_tc hk)] using ht

/-- Appending any event keeps the arrive-on rule: an arrive-on belongs to an old
`cp.async.mbarrier.arrive`, and every copy it tracks is older still. -/
theorem snoc_arriveOk (h : AsyncCopy.ArriveOk X) : AsyncCopy.ArriveOk (X.snoc g e r) := by
  intro i hi
  obtain ⟨⟨m, noinc, pc, ha⟩, hw⟩ := h i hi
  have hlt := len_of_get ha
  refine ⟨⟨m, noinc, pc, by rw [snoc_get_old hlt]; exact ha⟩, fun copy hc => hw copy ?_⟩
  obtain ⟨h1, h2, ⟨s, ⟨pcc, hcs⟩, hs⟩, m', noinc', pca, ha'⟩ := hc
  have hcl : copy.2 < (X.tr copy.1).length := by rw [h1]; omega
  exact ⟨h1, h2, ⟨s, ⟨pcc, by rwa [snoc_get_old hcl] at hcs⟩, hs⟩, m', noinc', pca,
    by rwa [snoc_get_old hlt] at ha'⟩

/-- Appending a plain instruction preserves the async/object constraints. All phases
and operations remain available. -/
theorem tmaOk_snoc_plain (ht : TmaOk X) (hk : e.kind.isTma = false) :
    TmaOk (X.snoc g e r) := by
  refine ⟨?_, snoc_tcEffectsOk hk ht.2.1, snoc_objectsOk hk ht.2.2.1, snoc_arriveOk ht.2.2.2⟩
  simpa only [snoc_issuedBy hk, snoc_async] using ht.1

end
end
end PTX
