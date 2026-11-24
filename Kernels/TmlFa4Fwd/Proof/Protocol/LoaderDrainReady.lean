-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActiveExitProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.IdleLoaderObjects
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarPending
import Lemmas.Protocol.MbarCount
import Lemmas.Protocol.MbarUnitTx

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Loader
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Thread.Loader
open Thread.Mma (ReleaseIssue emptyUpdateArrival emptyUnitsLeReadyAcquires)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvEmptyPhase)

noncomputable section

private theorem finalPhaseOfUnitUpdates {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (hc : cta < l.grid) (obj : IdleReleaseObject) (loc : Loc)
    (hLoc : obj.loc l cta = loc)
    (hShape : ∀ r ∈ X.objects loc, CounterUpdate r.action → r.action = .arrive 1 0) :
    let log := X.objects loc
    ∃ s, stateBefore log log.length = some s ∧ s.phase = unitsBefore log log.length := by
  dsimp only
  let log := X.objects loc
  have hX := hMax.1
  obtain ⟨hFirst,r,hr,hInit⟩ := idleReleaseInitialized hp hMax hc obj
  rw [hLoc] at hFirst hr
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  obtain ⟨s,hs⟩ := stateBefore_length_some hChecked hNo hr hInit (by decide)
  have hExpected := PairTmaRing.expected_of_init hX hFirst hNo hs
  have hInc : incrementsBefore log log.length = 0 := incrementsBefore_length_of log (by
    intro r hr h
    have ha := hShape r hr (by rw [h]; trivial)
    rw [h] at ha
    cases ha)
  have hTx := PTX.MBarrier.tx_zero hChecked hNo
    (fun r hr n b h => (Action.arrive.inj (h.symm.trans (hShape r hr (by rw [h]; trivial)))).2)
    (by
      intro r hr n h
      have ha := hShape r hr (by rw [h]; trivial)
      rw [h] at ha
      cases ha) hs
  have hPending := stateBefore_pending_pos hChecked hs hTx
  obtain ⟨hBound,hSum⟩ := (hChecked.accounted hNo (le_refl log.length)).2 s hs
  change unitsBefore log log.length + s.pending = _ at hSum
  rw [hExpected,hInc] at hBound hSum
  simp only [Nat.one_mul,Nat.add_zero] at hBound hSum
  change s.pending ≤ 1 at hBound
  change unitsBefore log log.length + s.pending = s.phase + 1 at hSum
  refine ⟨s,hs,?_⟩
  change s.phase = unitsBefore log log.length
  omega

/-- A recorded, non-faulting MMA credit to a release object. -/
def UnitRelease (X : Execution) (loc : Loc) : Prop :=
  ∃ r ∈ X.objects loc, r.action = .arrive 1 0 ∧ r.fault = none

private theorem unitCountPositive {loc : Loc} {X : Execution} (h : UnitRelease X loc) :
    0 < unitsBefore (X.objects loc) (X.objects loc).length := by
  rw [unitsBefore,List.take_length]
  obtain ⟨r,hr,hA,hF⟩ := h
  have aux {xs : List (Record Ref)} (hm : r ∈ xs) : 0 < arrivalUnits xs := by
    induction xs with
    | nil => simp at hm
    | cons q xs ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · simp [arrivalUnits,hA,hF]
      · have h := ih hm
        cases hAct : q.action <;> cases hFault : q.fault <;>
          simp only [arrivalUnits,hAct,hFault] <;> omega
  exact aux hr

/-- The actual second-query notification advances its drain object to phase one. -/
theorem queryDrainReadyOfUnitRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads)
    (hRelease : UnitRelease X (secondQueryEmpty l (g/l.block))) :
    QueryDrainReady l X g 0 := by
  let loc := secondQueryEmpty l (g/l.block)
  let log := X.objects loc
  have hX := hMax.1
  have hShape {r : Record Ref} (hr : r ∈ log) (ha : CounterUpdate r.action) :
      r.action = .arrive 1 0 := queryEmptyUpdate hp hX 1 hr ha
  obtain ⟨s,hs,hPhase⟩ := finalPhaseOfUnitUpdates hp hMax (NamedBar.cta_lt hg)
    .secondQuery loc (IdleReleaseObject.queryLoc l _) (fun _ => hShape)
  have hPositive := unitCountPositive hRelease
  obtain ⟨ref,href,hA,_⟩ := hRelease
  let select (r : Record Ref) : Bool := decide (r.action = .arrive 1 0)
  have hBound := countP_take_le_card (X.objects_checked hX loc).1 select
    (i := log.length) ({ref.id} : Finset Ref) (by
      intro _ _ r hr hSel
      have ha : r.action = .arrive 1 0 := of_decide_eq_true hSel
      exact Finset.mem_singleton.mpr (queryEmptyUpdateUnique hp hX 1 (List.mem_of_getElem? hr)
        href (by rw [ha]; trivial) (by rw [hA]; trivial)))
  have hUnitBound : unitsBefore log log.length ≤ 1 := by
    change (log.take log.length).countP select ≤ _ at hBound
    have hBound' : (log.take log.length).countP select ≤ 1 := by simpa using hBound
    refine (arrivalUnits_le_countP select ?_).trans hBound'
    intro r hr _ c tx ha
    have hOne := hShape ((List.take_sublist _ _).subset hr) (by rw [ha]; trivial)
    exact ⟨(Action.arrive.inj (ha.symm.trans hOne)).1, decide_eq_true hOne⟩
  have hOne : s.phase = 1 := by
    change 0 < unitsBefore log log.length at hPositive
    exact hPhase.trans (Nat.le_antisymm hUnitBound hPositive)
  exact ⟨s,hs,by rw [hOne]; decide⟩

/-- The single-visit drain sees phase one on K and V, and initial phase on the spare slot. -/
theorem cacheDrainReadyOfSingleVisitBudget {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g issuer index : Nat} (hg : g < l.threads) {form : Thread.Mma.ReleaseForm}
    {spec : TcCommit.Spec} (anchor : ReleaseIssue X issuer index form spec)
    (hCta : g/l.block = issuer/l.block)
    (hBudget : ∀ slot : Fin 3,
      (Thread.Mma.atPrefix l X issuer (X.tr issuer).length).kvAcquires slot ≤ (2+(2-slot.val))/3)
    (hKey : UnitRelease X (Thread.Mma.Observation.emptyObject l g 0))
    (hValue : UnitRelease X (Thread.Mma.Observation.emptyObject l g 1)) :
    CacheDrainReady l X g 2 := by
  have finalPhase (slot : Fin 3) :
      let log := X.objects (Thread.Mma.Observation.emptyObject l g slot)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = (2+(2-slot.val))/3 := by
    dsimp only
    let loc := Thread.Mma.Observation.emptyObject l g slot
    let log := X.objects loc
    obtain ⟨s,hs,hPhase⟩ := finalPhaseOfUnitUpdates hp hMax (NamedBar.cta_lt hg) (.cache slot)
      loc (IdleReleaseObject.cacheLoc l g slot) (by
        intro r hr ha
        obtain ⟨_,_,_,_,hA⟩ := emptyUpdateArrival hp hMax.1 hr ha
        exact hA)
    have hUpper := (emptyUnitsLeReadyAcquires hp hMax.1 (j := log.length) (slot := slot)
      anchor hCta).trans (hBudget slot)
    refine ⟨s,hs,?_⟩
    fin_cases slot
    · have hPositive := unitCountPositive hKey
      change 0 < unitsBefore log log.length at hPositive
      change unitsBefore log log.length ≤ 1 at hUpper
      change s.phase = 1
      exact hPhase.trans (Nat.le_antisymm hUpper hPositive)
    · have hPositive := unitCountPositive hValue
      change 0 < unitsBefore log log.length at hPositive
      change unitsBefore log log.length ≤ 1 at hUpper
      change s.phase = 1
      exact hPhase.trans (Nat.le_antisymm hUpper hPositive)
    · change unitsBefore log log.length ≤ 0 at hUpper
      change s.phase = 0
      exact hPhase.trans (Nat.le_zero.mp hUpper)
  intro i
  obtain ⟨s,hs,hPhase⟩ := finalPhase (kvUseStage (2+i.val))
  refine ⟨s,hs,?_⟩
  rw [hPhase]
  fin_cases i <;> decide

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Loader
