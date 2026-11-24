-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderDrainGenerations
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringWaitProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCohortIteration
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstCacheOrder
import Kernels.TmlFa4Fwd.Proof.Progress.MmaRecurringNotifications
import Lemmas.Protocol.MbarPending
import Lemmas.Protocol.MbarCount
import Lemmas.Protocol.PollPhase
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Loader
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Thread.Loader
open Thread.Mma (emptyUpdateArrival emptyReleaseAt EmptyReleaseAt)
open Protocol.LoaderReady (generation actualCompletedForIssuer phaseAlignment
  actualEmptyGuardLower)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvUseStage_val kvEmptyPhase)
open PTX.Flow (countP_take_succ countP_take_mono)

/-- The release history of one physical cache slot of a CTA. -/
abbrev cacheEmptyLog (l : Launch) (X : Execution) (g : Nat) (slot : Fin 3) :
    List (Record Ref) :=
  X.objects (Thread.Mma.Observation.emptyObject l g slot)

/-- The number of delivered MMA releases recorded on one physical cache slot. -/
abbrev cacheEmptyUnits (l : Launch) (X : Execution) (g : Nat) (slot : Fin 3) : Nat :=
  unitsBefore (cacheEmptyLog l X g slot) (cacheEmptyLog l X g slot).length

private theorem tcNotifyAction {X : Execution} {A : Snapshot} {m : Loc} {i : EvId}
    {rank : Fin 16} {act : MBarrier.Action}
    (h : objectAction X A m (.async i (.tcNotify rank)) = some act) : act = .arrive 1 0 := by
  simp only [objectAction] at h
  cases hg : X.get i with
  | none => simp [hg] at h
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    cases k with
    | tc k' =>
      cases k' with
      | commit s =>
        simp only [hg] at h
        split_ifs at h
        exact (Option.some.inj h).symm
      | _ => simp [hg] at h
    | _ => simp [hg] at h

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

/-- Every state of an empty-slot history has completed one phase per delivered release. -/
private theorem emptyPhaseEqUnits {g j : Nat} (hc : g/l.block < l.grid) (slot : Fin 3) {s : State}
    (hj : j ≤ (cacheEmptyLog l X g slot).length)
    (hs : stateBefore (cacheEmptyLog l X g slot) j = some s) :
    s.phase = unitsBefore (cacheEmptyLog l X g slot) j := by
  let loc := Thread.Mma.Observation.emptyObject l g slot
  let log := X.objects loc
  have hX := hMax.1
  obtain ⟨hFirst,_⟩ := idleReleaseInitialized hp hMax hc (.cache slot)
  rw [IdleReleaseObject.cacheLoc] at hFirst
  have hShape : ∀ r ∈ log, CounterUpdate r.action → r.action = .arrive 1 0 := by
    intro r hr hu
    obtain ⟨_,_,_,_,ha⟩ := emptyUpdateArrival hp hX hr hu
    exact ha
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hExpected := PairTmaRing.expected_of_init hX hFirst hNo hs
  have hIncAll : incrementsBefore log log.length = 0 := incrementsBefore_length_of log (by
    intro r hr h
    have ha := hShape r hr (by rw [h]; trivial)
    rw [h] at ha
    cases ha)
  have hInc := incrementsBefore_eq_zero log hIncAll j
  have hTx := PTX.MBarrier.tx_zero hChecked hNo
    (fun r hr n b h => (Action.arrive.inj (h.symm.trans (hShape r hr (by rw [h]; trivial)))).2)
    (by
      intro r hr n h
      have ha := hShape r hr (by rw [h]; trivial)
      rw [h] at ha
      cases ha) hs
  have hPending := stateBefore_pending_pos hChecked hs hTx
  obtain ⟨hBound,hSum⟩ := (hChecked.accounted hNo hj).2 s hs
  rw [hExpected] at hBound hSum
  change incrementsBefore log j = 0 at hInc
  rw [hInc] at hBound hSum
  simp only [Nat.one_mul,Nat.add_zero] at hBound hSum
  change s.phase = unitsBefore (X.objects loc) j
  omega

omit hp hMax in
/-- A delivered release record of an empty slot is a clean unit arrival. -/
private theorem releaseRecordUnit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} {issuer i : Nat}
    (a : EmptyReleaseAt l X loc issuer i) : a.record.action = .arrive 1 0 := by
  have hm := ((hX.tma.2.2.1 loc).2.1 a.record (List.mem_of_getElem? a.atIndex)).1
  rw [a.notification] at hm
  exact tcNotifyAction hm

/-- A delivered release whose ready generation is `ordinal` accounts for that many earlier
releases plus itself on the same physical slot. -/
theorem EmptyReleaseAt.unitsLower {g issuer i : Nat} (hc : g/l.block < l.grid) {slot : Fin 3}
    (a : EmptyReleaseAt l X (Thread.Mma.Observation.emptyObject l g slot) issuer i)
    (hClean : a.record.fault = none) :
    a.ordinal + 1 ≤ cacheEmptyUnits l X g slot := by
  let loc := Thread.Mma.Observation.emptyObject l g slot
  let log := X.objects loc
  have hX := hMax.1
  have hAct := releaseRecordUnit hX a
  have hChecked := X.objects_checked hX loc
  have hLen : i < log.length := (List.getElem?_eq_some_iff.mp a.atIndex).1
  obtain ⟨st,hSt⟩ : ∃ st, stateBefore log i = some st := by
    cases hState : stateBefore log i with
    | some st => exact ⟨st,rfl⟩
    | none =>
      have hOk := hChecked.at a.atIndex
      rw [hState] at hOk
      unfold RecordOk at hOk
      rw [hAct] at hOk
      have hErr : perform none (.arrive 1 0) = .error .invalidObject := rfl
      rw [hErr] at hOk
      rw [hClean] at hOk
      cases hOk.2
  have hPhase : phaseAt log i = some st.phase := by
    simp only [phaseAt,hSt,Option.map_some]
  have hExact := (phaseAlignment hp hX (actualEmptyGuardLower hp hX g slot) st.phase).2
    i issuer a hClean hPhase
  have hUnits := emptyPhaseEqUnits hp hMax hc slot (j := i) hLen.le hSt
  have hStep := unitsBefore_succ log a.atIndex
  have hOne : arrivalUnits [a.record] = 1 := by simp [arrivalUnits,hAct,hClean]
  have hMono := unitsBefore_mono log (show i+1 ≤ log.length by omega)
  change a.ordinal + 1 ≤ unitsBefore log log.length
  rw [hStep,hOne] at hMono
  change st.phase = unitsBefore log i at hUnits
  omega

omit hp hMax in
/-- Any delivered clean unit release puts at least one completed phase on its slot. -/
theorem unitReleaseUnitsLower {l : Launch} {X : Execution} {g : Nat} {slot : Fin 3}
    (h : ∃ r ∈ cacheEmptyLog l X g slot, r.action = .arrive 1 0 ∧ r.fault = none) :
    1 ≤ cacheEmptyUnits l X g slot := by
  obtain ⟨r,hr,hA,hF⟩ := h
  rw [cacheEmptyUnits,unitsBefore,List.take_length]
  have aux {xs : List (Record Ref)} (hm : r ∈ xs) : 1 ≤ arrivalUnits xs := by
    induction xs with
    | nil => simp at hm
    | cons q xs ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · simp [arrivalUnits,hA,hF]
      · have h := ih hm
        cases hAct : q.action <;> cases hFault : q.fault <;>
          simp only [arrivalUnits,hAct,hFault] <;> omega
  exact aux hr

/-- A retired MMA cache use has been delivered to the producer's slot together with every
earlier generation of that slot. -/
theorem retiredCacheUseUnitsLower (hFrame : OutputFootprint p X) {g mma use : Nat}
    {form : Thread.Mma.ReleaseForm} (hg : g < l.threads) (hCta : mma/l.block = g/l.block)
    (hRetired : Mma.RetiredCacheUse l X mma use form) :
    use/3 + 1 ≤ cacheEmptyUnits l X g (kvUseStage use) := by
  obtain ⟨issuer,k,a,_,_,hOrdinal,hClean⟩ :=
    Progress.deliveredRecurringCacheRetirement hp hMax hFrame hRetired
  have h := EmptyReleaseAt.unitsLower hp hMax (hCta ▸ NamedBar.cta_lt hg) a hClean
  have hSame : cacheEmptyUnits l X mma (Mma.readyStage use) =
      cacheEmptyUnits l X g (kvUseStage use) := by
    simp only [cacheEmptyUnits,cacheEmptyLog,Thread.Mma.Observation.emptyObject,hCta]
    rfl
  rw [← hSame,← hOrdinal]
  exact h

/-- The final state of an empty-slot history has one completed phase per delivered release. -/
theorem cacheEmptyFinalPhase {g : Nat} (hg : g < l.threads) (slot : Fin 3) :
    ∃ s, stateBefore (cacheEmptyLog l X g slot) (cacheEmptyLog l X g slot).length = some s ∧
      s.phase = cacheEmptyUnits l X g slot := by
  let loc := Thread.Mma.Observation.emptyObject l g slot
  have hX := hMax.1
  have hc := NamedBar.cta_lt hg
  obtain ⟨_,r0,hr0,hInit⟩ := idleReleaseInitialized hp hMax hc (.cache slot)
  rw [IdleReleaseObject.cacheLoc] at hr0
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  obtain ⟨s,hs⟩ := stateBefore_length_some hChecked hNo hr0 hInit (by decide)
  exact ⟨s,hs,emptyPhaseEqUnits hp hMax hc slot (le_refl _) hs⟩

/-- A slot never completes more phases than the generations that one loader lane of the
CTA has published to it: each release returns a generation that every lane published. -/
theorem cacheEmptyUnitsUpper {g k : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (slot : Fin 3)
    (hPublished : ∀ j, X.AsyncArrive (g,j) (readyObject l g slot) true →
      generation l X (g,j) slot < k) :
    cacheEmptyUnits l X g slot ≤ k := by
  classical
  by_contra! hMore
  let loc := Thread.Mma.Observation.emptyObject l g slot
  let log := X.objects loc
  have hX := hMax.1
  have hc := NamedBar.cta_lt hg
  obtain ⟨hFirst,_⟩ := idleReleaseInitialized hp hMax hc (.cache slot)
  rw [IdleReleaseObject.cacheLoc] at hFirst
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  obtain ⟨s,hs,hPhase⟩ := cacheEmptyFinalPhase hp hMax hg slot
  have update {r : Record Ref} (hMem : r ∈ log) (h : CounterUpdate r.action) :=
    emptyUpdateArrival hp hX hMem h
  have hNoIncrement : incrementsBefore log log.length = 0 :=
    incrementsBefore_length_of _ fun r hMem hAction => by
      obtain ⟨_,_,_,_,hArrival⟩ := update hMem (by rw [hAction]; trivial)
      rw [hAction] at hArrival
      cases hArrival
  have hUnits := hChecked.card_unit_arrivals_phase hNo (n := 1) (q := k)
    (fun _ r count tx hRecord _ hAction => by
      obtain ⟨_,_,_,_,hUnit⟩ := update (List.mem_of_getElem? hRecord)
        (by rw [hAction]; trivial)
      rw [hAction] at hUnit
      exact (Action.arrive.inj hUnit).1)
    (fun _ _ _ h => PairTmaRing.expected_of_init hX hFirst hNo h) hNoIncrement
    (le_refl _) hs (by rw [hPhase]; exact hMore)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < _ from hUnits.symm ▸ Nat.zero_lt_one)
  obtain ⟨_,r,tx,hRecord,hAction,hClean,hAt⟩ := Finset.mem_filter.mp hi
  obtain ⟨_,_,_,_,hUnit⟩ := update (List.mem_of_getElem? hRecord) (by rw [hAction]; trivial)
  obtain ⟨issuer,⟨a⟩⟩ := emptyReleaseAt hp hX hRecord hUnit
  have hSame : a.record = r := Option.some.inj (a.atIndex.symm.trans hRecord)
  have hExact := (phaseAlignment hp hX (actualEmptyGuardLower hp hX g slot) k).2
    i issuer a (hSame ▸ hClean) hAt
  have hReady := a.matched.ready
  rw [a.matchedSlot] at hReady
  obtain ⟨complete⟩ := actualCompletedForIssuer hp hX a.issue hReady
  obtain ⟨lane,hLane⟩ := producerOfLoaderWarp hp hw
  obtain ⟨issue,hIssue,hArrive,_,hGeneration,_⟩ := complete.actualPublicationOfLane hp hX lane
  rw [← a.issuerCta hp hX,← hLane] at hIssue
  have hObject : readyObject l issuer slot = readyObject l g slot := by
    simp only [readyObject,← a.issuerCta hp hX]
  rw [hObject] at hArrive
  obtain ⟨actor,j⟩ := issue
  change actor = g at hIssue
  subst actor
  have hBound := hPublished j hArrive
  have hOrd : a.ordinal = generation l X (g,j) slot := by
    simpa only [EmptyReleaseAt.ordinal,a.matchedSlot] using hGeneration.symm
  omega

omit hp hMax in
/-- Every recurring publication of a lane uses a ring position below `bound`. -/
def RecurringUsesBelow (X : Execution) (g bound : Nat) : Prop :=
  ∀ j e, X.get (g,j) = some e → recurringPublicationMark e = true →
    recurringUseBefore X (g,j) < bound

omit hp hMax in
/-- Under a use bound, each publication of the lane to a slot has a generation whose ring
position lies below the bound. Priming publications have positions zero and one. -/
theorem publishedPositionBelow {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g bound : Nat} (hUses : RecurringUsesBelow X g bound) (hBound : 2 ≤ bound)
    {slot : Fin 3} {j : Nat} (hPub : X.AsyncArrive (g,j) (readyObject l g slot) true) :
    3 * generation l X (g,j) slot + slot.val < bound := by
  by_cases hRepeat : 2 ≤ 3 * generation l X (g,j) slot + slot.val
  · obtain ⟨hUse,e,he,hMark⟩ := readyPublicationOccurrence hp hX hPub hRepeat
    have h := hUses j e he hMark
    change 3 * (atPrefix l X g j).published.countP (fun pub => pub.slot == slot) + slot.val <
      bound
    omega
  · omega

/-- The empty slot of `use` has completed exactly `use/3` phases, so the wait for `use`
returns, when the lane has published only earlier uses and the MMA has delivered the
generations of the slot before `use`. -/
theorem cacheEmptyReadyOfReleases {g use : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hUses : RecurringUsesBelow X g use) (hTwo : 2 ≤ use)
    (hReleased : use/3 ≤ cacheEmptyUnits l X g (kvUseStage use)) :
    CacheEmptyReady l X g use := by
  have hUpper := cacheEmptyUnitsUpper hp hMax hg hw (kvUseStage use) (k := use/3) (by
    intro j hPub
    have h := publishedPositionBelow hp hMax.1 hUses hTwo hPub
    rw [kvUseStage_val] at h
    omega)
  obtain ⟨s,hs,hPhase⟩ := cacheEmptyFinalPhase hp hMax hg (kvUseStage use)
  refine ⟨s,hs,?_⟩
  have hExact : s.phase = use/3 := by omega
  rw [hExact]
  change use/3%2 ≠ (if (use/3%2 == 0) = true then 1 else 0)
  by_cases h : use/3%2 = 0 <;> simp [h]

/-- The MMA's retirement of `use-3` accounts for the `use/3` releases that the poll for `use`
requires. -/
theorem releasedOfRetiredUse (hFrame : OutputFootprint p X) {g use mma : Nat}
    {form : Thread.Mma.ReleaseForm} (hg : g < l.threads) (hThree : 3 ≤ use)
    (hCta : mma/l.block = g/l.block) (hRetired : Mma.RetiredCacheUse l X mma (use-3) form) :
    use/3 ≤ cacheEmptyUnits l X g (kvUseStage use) := by
  have h := retiredCacheUseUnitsLower hp hMax hFrame hg hCta hRetired
  have hStage : kvUseStage (use-3) = kvUseStage use :=
    Fin.ext (by rw [kvUseStage_val,kvUseStage_val]; omega)
  rw [hStage] at h
  omega

/-- The release counts required by the terminal drain at `use` follow from the delivered
generations of the last three uses when the lane has published only uses below `use`. -/
theorem cacheReleaseCountsOfReleases {g use : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hUses : RecurringUsesBelow X g use) (hTwo : 2 ≤ use)
    (hReleased : ∀ slot : Fin 3, (use+(2-slot.val))/3 ≤ cacheEmptyUnits l X g slot) :
    CacheReleaseCounts l X g use := by
  intro slot
  have hUpper := cacheEmptyUnitsUpper hp hMax hg hw slot (k := (use+(2-slot.val))/3) (by
    intro j hPub
    have h := publishedPositionBelow hp hMax.1 hUses hTwo hPub
    have := slot.isLt
    omega)
  have h := hReleased slot
  change cacheEmptyUnits l X g slot = _
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Loader
