-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOperandReady
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Order.OrderBaseCausality
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaObservedValueBank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (readyObject emptyObject)

noncomputable section

abbrev readyCount (X : Execution) (g index : Nat) :=
  (((X.tr g).take index).filterMap readyEvent).length

private abbrev readyGateCount (X : Execution) (g index : Nat) (gate : Fin 4) :=
  ((X.tr g).take index).countP (readyAtSite gate)

private theorem readyCount_mono {X : Execution} {g a b : Nat} (h : a ≤ b) :
    readyCount X g a ≤ readyCount X g b :=
  ((List.take_sublist_take_left (l := X.tr g) h).filterMap readyEvent).length_le

private theorem readyMarkOfGate {e : Event} {gate : Fin 4}
    (h : readyAtSite gate e = true) : (readyEvent e).isSome = true := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try cases h
  case wait loc parity ok acquire scope =>
    cases ok
    · cases h
    have hp : pc = (slotWait gate).pc := beq_iff_eq.mp h
    have hSite : (slotWait gate).pc = readyHead gate := by fin_cases gate <;> rfl
    have hAny : (List.finRange 4).any (fun i => readyHead i == pc) = true :=
      List.any_eq_true.mpr ⟨gate, by simp, beq_iff_eq.mpr (hp.trans hSite).symm⟩
    simp [readyEvent, hAny]

private theorem gateCountStable {X : Execution} {g a b : Nat} (h : a ≤ b)
    (hCount : readyCount X g a = readyCount X g b) (gate : Fin 4) :
    readyGateCount X g a gate = readyGateCount X g b gate := by
  obtain ⟨mid, hSplit⟩ := List.take_prefix a ((X.tr g).take b)
  rw [List.take_take, Nat.min_eq_left h] at hSplit
  have hEmpty : mid.filterMap readyEvent = [] := by
    unfold readyCount at hCount
    rw [← hSplit, List.filterMap_append, List.length_append] at hCount
    exact List.length_eq_zero_iff.mp (by omega)
  have hNo : mid.countP (readyAtSite gate) = 0 := by
    apply List.countP_eq_zero.mpr
    intro e he hOn
    have hOff := List.filterMap_eq_nil_iff.mp hEmpty e he
    have hMarked := readyMarkOfGate hOn
    simp [hOff] at hMarked
  unfold readyGateCount
  rw [← hSplit, List.countP_append, hNo, Nat.add_zero]

private theorem countsAfterReady {X : Execution} {g j pc : Nat} {loc : Loc} {parity : Nat}
    (hPoll : X.get (g,j) = some ⟨pc, .wait loc parity true true .cta⟩)
    (hReady : ∃ i : Fin 4, pc = readyHead i) :
    readyCount X g (j+1) = readyCount X g j+1 ∧
    ∀ i : Fin 4, readyGateCount X g (j+1) i =
      readyGateCount X g j i + (if pc = (slotWait i).pc then 1 else 0) := by
  have hGet : (X.tr g)[j]? = _ := hPoll
  obtain ⟨gate, hGate⟩ := hReady
  have hm : (List.finRange 4).any (fun i => readyHead i == pc) = true :=
    List.any_eq_true.mpr ⟨gate, by simp, beq_iff_eq.mpr hGate.symm⟩
  constructor
  · simp [readyCount, List.take_add_one, hGet, List.filterMap_append, readyEvent, hm]
  · intro i
    by_cases h : pc = (slotWait i).pc <;>
      simp [readyGateCount, List.take_add_one, hGet, List.countP_append, readyAtSite, h]

private theorem beforeGateCountMono {X : Execution} {g a b : Nat} (h : a ≤ b) (gate : Fin 4) :
    readyGateCount X g a gate ≤ readyGateCount X g b gate :=
  (List.take_sublist_take_left (l := X.tr g) h).countP_le

private theorem valueGateAtBroadcast (steady : Bool) :
    let site := releaseIndex (valueReleaseForm steady)
    (slotWait site).pc + 3 ≤ valueBroadcast steady ∧ valueBroadcast steady ≤ (slotElect site).pc :=
  by cases steady <;> decide

private theorem otherVReadyGate (steady : Bool) (i : Fin 4) :
    let gate := releaseIndex (valueReleaseForm steady)
    (i = 1 ∨ i = 3) → readyHead i ≠ (slotWait gate).pc →
      2145 ≤ readyHead i ∧ readyHead i < 2768 ∧ readyHead i ≠ (slotWait gate).pc + 1 ∧
      ¬ ((slotWait gate).pc + 2 < readyHead i ∧ readyHead i ≤ (slotElect gate).pc) := by
  cases steady <;> fin_cases i <;> decide

/-- A fragment's V ready acquire retains its global use as well as its local
release ordinal. No later V acquire precedes the fragment. -/
theorem actualValueReadyOfFragment {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (hFragment : PvInstruction X (g,index) block step d op accum mask) :
    let steady := decide (block.val < 2)
    ∃ use broadcast wait, ValueDescriptorUse l X (g,broadcast) steady use ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ PvShape l g op ∧
      ReadyPoll l X g wait (readyStage use) (readyWord use) true .cta ∧
      ReleaseReadyObservation X g wait (valueReleaseForm steady)
        (readyObject l g (readyStage use)) (readyWord use) ∧
      readyOccurrence X g wait (valueReleaseForm steady) =
        releaseElections X g index (valueReleaseForm steady) ∧
      readyCount X g wait = use ∧ TraceBefore X (g,wait) (g,index) ∧
      ∀ j slot parity, wait < j → j < index → ReadyPoll l X g j slot parity true .cta →
        readyCount X g j % 2 = 0 := by
  let steady : Bool := decide (block.val < 2)
  let form := valueReleaseForm steady
  let gate := releaseIndex form
  obtain ⟨use, broadcast, hb, hDescriptor, hB, hShape, hCursor⟩ :=
    hFragment.valueOperandUseAndReadyCursor hp hX
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_, hFragment.decoded⟩
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hMma).1
  have hTyped : ValueDescriptorUse l X (g,broadcast) steady use := hDescriptor
  obtain ⟨wait, hPoll, hRank, hBefore⟩ := hTyped.readyBefore hp hX hWarp
  obtain ⟨pc, hGet, hSite⟩ := hPoll.useSite hp hX hWarp
  have hRank' : readyCount X g wait = use := hRank
  change ReadyUseSite (readyCount X g wait) pc at hSite
  rw [hRank'] at hSite
  obtain ⟨⟨sent, valid, hBroadcast⟩, hUse, hOdd⟩ := hDescriptor
  have hg := event_thread_lt hX hBroadcast
  have hTotal := readyUsesAtPrefix hp hX hg hWarp broadcast
  have hUse' : use = readyCount X g broadcast - 1 :=
    hUse.trans (congrArg (· - 1) hTotal.symm)
  have hTotal' : readyCount X g broadcast = use + 1 := by omega
  have hVSite : pc = readyHead 1 ∨ pc = readyHead 3 := by
    rcases hSite with ⟨_, hz⟩ | ⟨_, _, hz⟩ | ⟨hV, _⟩
    · omega
    · omega
    · exact hV
  have hReady : ∃ i : Fin 4, pc = readyHead i :=
    hVSite.elim (fun h => ⟨1,h⟩) (fun h => ⟨3,h⟩)
  obtain ⟨hTotalStep, hGateStep⟩ := countsAfterReady hGet hReady
  have hBound : wait+1 ≤ broadcast := hBefore.2.1
  have hStable (i : Fin 4) (hi : i = 1 ∨ i = 3) :
      readyGateCount X g (wait+1) i = readyGateCount X g index i :=
    (gateCountStable hBound (by omega : readyCount X g (wait+1) = readyCount X g broadcast) i).trans
      (hCursor i hi)
  have hDoneGate (i : Fin 4) : readyGateCount X g (wait+1) i =
      readyGateCount X g broadcast i := gateCountStable hBound (by omega) i
  have hPending := pendingReadyBalance hp hX gate hBroadcast (valueGateAtBroadcast steady)
  have hForm : pc = (slotWait gate).pc := by
    by_contra! hOff
    have hBounds : 2145 ≤ pc ∧ pc < 2768 ∧ pc ≠ (slotWait gate).pc + 1 ∧
        ¬ ((slotWait gate).pc + 2 < pc ∧ pc ≤ (slotElect gate).pc) := by
      rcases hVSite with h | h
      · rw [h] at hOff ⊢
        exact otherVReadyGate steady 1 (.inl rfl) hOff
      · rw [h] at hOff ⊢
        exact otherVReadyGate steady 3 (.inr rfl) hOff
    have hEarlier := readyBalanceAtEvent hp hX gate hGet hBounds.1 hBounds.2.1 hBounds.2.2.1
    simp only [hBounds.2.2.2, ↓reduceIte, Nat.zero_add] at hEarlier
    have hMonotone := (List.take_sublist_take_left (l := X.tr g) hBefore.2.1.le).countP_le
      (p := ElectOrd.atSites (· == (slotElect gate).pc))
    have hQuiet := hGateStep gate
    simp only [hOff, ↓reduceIte, Nat.add_zero] at hQuiet
    have hReadyCount := hQuiet.symm.trans (hDoneGate gate)
    change readyGateCount X g broadcast gate =
      1 + ElectOrd.siteOrdinal (· == (slotElect gate).pc) X g broadcast at hPending
    change readyGateCount X g wait gate = _ at hEarlier
    change ElectOrd.siteOrdinal (· == (slotElect gate).pc) X g wait ≤
      ElectOrd.siteOrdinal (· == (slotElect gate).pc) X g broadcast at hMonotone
    omega
  have hGateChoice : gate = 1 ∨ gate = 3 := by fin_cases block <;> decide
  have hLive : (slotWait gate).pc + 3 ≤ pvPc block step ∧
      pvPc block step ≤ (slotElect gate).pc := by fin_cases block <;> fin_cases step <;> decide
  have hFragmentBalance := pendingReadyBalance hp hX gate hFragment.decoded hLive
  have hOrdinal : readyOccurrence X g wait form = releaseElections X g index form := by
    have hE := hGateStep gate
    simp only [hForm, ↓reduceIte] at hE
    have hS := hStable gate hGateChoice
    change readyGateCount X g index gate =
      1 + ElectOrd.siteOrdinal (· == (slotElect gate).pc) X g index at hFragmentBalance
    change readyGateCount X g wait gate =
      ElectOrd.siteOrdinal (· == (slotElect gate).pc) X g index
    omega
  have hObservation : ReleaseReadyObservation X g wait form
      (readyObject l g (readyStage use)) (readyWord use) := by
    change X.get (g,wait) = some ⟨(slotWait gate).pc,
      .wait (readyObject l g (readyStage use)) (readyWord use) true true .cta⟩
    rwa [← hForm]
  refine ⟨use, broadcast, wait, hTyped, hB, hShape, hPoll, hObservation,
    hOrdinal, hRank, hBefore.trans ⟨rfl,hb,len_of_get hFragment.decoded⟩, ?_⟩
  intro j slot parity hAfter hPrior hJ
  obtain ⟨other, hOther, hType⟩ := hJ.useSite hp hX hWarp
  rcases hType with ⟨_, h0⟩ | ⟨_, _, hEven⟩ | ⟨hOddSite, _⟩
  · simp [h0]
  · exact hEven
  exfalso
  obtain ⟨i, hI, hSite⟩ : ∃ i : Fin 4, (i = 1 ∨ i = 3) ∧ other = readyHead i := by
    rcases hOddSite with h | h
    · exact ⟨1,.inl rfl,h⟩
    · exact ⟨3,.inr rfl,h⟩
  have hMark : other = (slotWait i).pc := hSite.trans (by fin_cases i <;> rfl)
  have hAt := (countsAfterReady hOther ⟨i,hSite⟩).2 i
  simp only [hMark, ↓reduceIte] at hAt
  have hLower : readyGateCount X g (wait+1) i ≤ readyGateCount X g j i :=
    beforeGateCountMono hAfter i
  have hUpper : readyGateCount X g (j+1) i ≤ readyGateCount X g index i :=
    beforeGateCountMono hPrior i
  have hSame := hStable i hI
  omega


/-- A V fragment precedes the slot release at its use or at a later generation.
An intervening ready on another slot does not change this order. -/
theorem valueFragmentBeforeRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index use wait d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hFragment : X.MmaIssue (g,index) d op accum mask)
    {owner position : Nat} {slot : Fin 3} {form : ReleaseForm}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g position)
    (hPoll : ReadyPoll l X g wait (readyStage use) (readyWord use) true .cta)
    (hReady : ReleaseReadyObservation X g wait form (readyObject l g (readyStage use))
      (readyWord use))
    (hOrdinal : readyOccurrence X g wait form = releaseElections X g index form)
    (hUse : readyCount X g wait = use) (hOdd : use % 2 = 1)
    (hNoValue : ∀ j stage parity, wait < j → j < index →
      ReadyPoll l X g j stage parity true .cta → readyCount X g j % 2 = 0)
    (hSlot : slot = readyStage use) (hBound : use ≤ 3 * release.ordinal + slot.val) :
    TraceBefore X (g,index) (g,release.index) := by
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hFragment).1
  have hg : g < l.threads := event_thread_lt hX hFragment.choose_spec
  have hCount (k : Nat) := readyUsesAtPrefix hp hX hg hWarp k
  let next := 3 * release.ordinal + slot.val
  have hLaterUse : readyCount X g release.matched.wait = next := by
    have hFacts := release.matched.ready.exactOccurrence hp hX hWarp
    dsimp only at hFacts
    rw [← hCount] at hFacts
    change release.matched.slot.val = (readyCount X g release.matched.wait) % 3 ∧
      release.ordinal = readyCount X g release.matched.wait / 3 ∧ _ at hFacts
    rw [release.matchedSlot] at hFacts
    dsimp only [next]
    omega
  rcases hBound.lt_or_eq with hLt | hEq
  · have hSame : next % 3 = use % 3 := by
      change (3 * release.ordinal + slot.val) % 3 = use % 3
      have hVal : slot.val = use % 3 := congrArg Fin.val hSlot
      omega
    have hGap : use + 2 < next := by
      change use < next at hLt
      omega
    have hBefore : index ≤ release.matched.wait := by
      by_contra! hLate
      obtain ⟨j,hJ,hReady',hRank⟩ := readyPollAtOrdinalBefore hp hX hg hWarp
        (stop := release.matched.wait) (use := use+2) (by
          change use+2 < readyCount X g release.matched.wait
          rwa [hLaterUse])
      have hAfter : wait < j := by
        by_contra! hj
        have hm := readyCount_mono (X := X) (g := g) hj
        rw [hUse] at hm
        change readyCount X g j = use+2 at hRank
        omega
      have hEven := hNoValue j (readyStage (use+2)) (readyWord (use+2)) hAfter
        (hJ.trans hLate) hReady'
      change readyCount X g j = use+2 at hRank
      omega
    exact ⟨rfl,hBefore.trans_lt release.matched.earlier,release.matched.resumes.1.2.2⟩
  · subst slot
    have hFacts := hPoll.exactOccurrence hp hX hWarp
    change _ ∧ (atPrefix l X g wait).kvAcquires (readyStage use) = _ ∧ _ at hFacts
    have hPhase : (atPrefix l X g wait).kvAcquires (readyStage use) = release.ordinal := by
      rw [hFacts.2.1, ← hCount]
      change readyCount X g wait / 3 = release.ordinal
      rw [hUse]
      change use = 3 * release.ordinal + use % 3 at hEq
      omega
    exact (release.afterFragmentOfReady hp hX hFragment hReady hOrdinal hPhase).2


/-- A value use is selected by the latest successful V ready before the fragment. -/
def LatestValueReadyUse (l : Launch) (X : Execution) (g index use : Nat) : Prop :=
  ∃ wait, ReadyPoll l X g wait (readyStage use) (readyWord use) true .cta ∧
    readyCount X g wait = use ∧ use % 2 = 1 ∧ TraceBefore X (g,wait) (g,index) ∧
    ∀ j slot parity, wait < j → j < index → ReadyPoll l X g j slot parity true .cta →
      readyCount X g j % 2 = 0

theorem LatestValueReadyUse.unique {l : Launch} {X : Execution} {g index u v : Nat}
    (hu : LatestValueReadyUse l X g index u) (hv : LatestValueReadyUse l X g index v) : u = v := by
  obtain ⟨a,hA,hUseA,hOddA,hBeforeA,hOnlyA⟩ := hu
  obtain ⟨b,hB,hUseB,hOddB,hBeforeB,hOnlyB⟩ := hv
  rcases lt_trichotomy a b with hab | hab | hba
  · have hEven := hOnlyA b (readyStage v) (readyWord v) hab hBeforeB.2.1 hB
    omega
  · subst b
    exact hUseA.symm.trans hUseB
  · have hEven := hOnlyB a (readyStage u) (readyWord u) hba hBeforeA.2.1 hA
    omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index d : Nat} {block : Fin 4} {step : Fin 8}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hFragment : PvInstruction X (g,index) block step d op accum mask)
include hp hX hFragment

/-- A PV fragment between a ready acquire and its matching V release uses
that same acquire as its latest V ready. -/
theorem valueFragmentLatestUseOfReadyAndRelease {ready commit parity : Nat} {slot : Fin 3}
    (hMatched : ReleaseReadyObservation X g ready (valueReleaseForm (decide (block.val < 2)))
      (readyObject l g slot) parity)
    (hMatchedOrdinal : readyOccurrence X g ready (valueReleaseForm (decide (block.val < 2))) =
      releaseOccurrence X g commit (valueReleaseForm (decide (block.val < 2))))
    (hAfter : TraceBefore X (g,ready) (g,index)) (hBefore : TraceBefore X (g,index) (g,commit)) :
    LatestValueReadyUse l X g index (readyCount X g ready) ∧
      op.b = sharedDescriptor (kvStart l (readyCount X g ready) + pvFragment step) 16384 := by
  let form := valueReleaseForm (decide (block.val < 2))
  let gate := releaseIndex form
  obtain ⟨use, broadcast, wait, hDescriptor, hB, hShape, hPoll, hReady,
      hOrdinal, hRank, hEarlier, hNoLater⟩ := actualValueReadyOfFragment hp hX hFragment
  have hMatch : X.get (g,ready) = some ⟨(slotWait gate).pc,
      .wait (readyObject l g slot) parity true true .cta⟩ := hMatched
  have hReady' : X.get (g,wait) = some ⟨(slotWait gate).pc,
      .wait (readyObject l g (readyStage use)) (readyWord use) true true .cta⟩ := hReady
  have headPc (i : Fin 4) : (slotWait i).pc = readyHead i := by fin_cases i <;> rfl
  have hGatePc := headPc gate
  have hCountLower := (countsAfterReady hMatch ⟨gate,hGatePc⟩).2 gate
  simp only [↓reduceIte] at hCountLower
  have hExpected : readyGateCount X g index gate = 1 + releaseElections X g index form := by
    have hLive : (slotWait gate).pc + 3 ≤ pvPc block step ∧
        pvPc block step ≤ (slotElect gate).pc := by fin_cases block <;> fin_cases step <;> decide
    exact pendingReadyBalance hp hX gate hFragment.decoded hLive
  have hMono := beforeGateCountMono (X := X) (g := g) hAfter.2.1 gate
  have hLow : readyOccurrence X g ready form ≤
      readyOccurrence X g wait form := by
    change readyGateCount X g ready gate ≤ readyGateCount X g wait gate
    change readyGateCount X g wait gate = releaseElections X g index form at hOrdinal
    change readyGateCount X g (ready+1) gate ≤ readyGateCount X g index gate at hMono
    omega
  have hHigh : readyOccurrence X g wait form ≤
      readyOccurrence X g ready form := by
    rw [hOrdinal,hMatchedOrdinal]
    exact (List.take_sublist_take_left (l := X.tr g)
      (show index ≤ commit-1 by have := hBefore.2.1; omega)).countP_le
  have hEqual : wait = ready :=
    Flow.eq_of_count_eq (readyAtSite gate) (X.tr g) hReady'
      (by simp [readyAtSite]) hMatch (by simp [readyAtSite]) (Nat.le_antisymm hHigh hLow)
  subst wait
  rw [hRank]
  exact ⟨⟨ready,hPoll,hRank,hDescriptor.2.2,hEarlier,hNoLater⟩,hB⟩

/-- The V fragment bracketed by a ready acquire and its release issue addresses
the slot of the acquire. -/
theorem valueFragmentDescriptorOfReadyAndRelease {ready commit parity : Nat} {slot : Fin 3}
    (hMatched : ReleaseReadyObservation X g ready (valueReleaseForm (decide (block.val < 2)))
      (readyObject l g slot) parity) (hMatchPoll : ReadyPoll l X g ready slot parity true .cta)
    (hMatchedOrdinal : readyOccurrence X g ready (valueReleaseForm (decide (block.val < 2))) =
      releaseOccurrence X g commit (valueReleaseForm (decide (block.val < 2))))
    (hAfter : TraceBefore X (g,ready) (g,index)) (hBefore : TraceBefore X (g,index) (g,commit)) :
    op.b = sharedDescriptor (kvStart l slot.val + pvFragment step) 16384 := by
  obtain ⟨_,hB⟩ := valueFragmentLatestUseOfReadyAndRelease hp hX hFragment
    hMatched hMatchedOrdinal hAfter hBefore
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hFragment.decoded⟩
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hMma).1
  have hSlot := (hMatchPoll.exactOccurrence hp hX hWarp).1
  have hTotal := readyUsesAtPrefix hp hX
    (show g < l.threads from event_thread_lt hX hFragment.decoded) hWarp ready
  rw [← hTotal] at hSlot
  change slot.val = readyCount X g ready % 3 at hSlot
  have hSame : kvSlot slot.val = kvSlot (readyCount X g ready) := by
    change slot.val % 3 = readyCount X g ready % 3
    rwa [Nat.mod_eq_of_lt slot.isLt]
  simpa only [kvStart, hSame] using hB

/-- The V fragment bracketed by a delivered release addresses the slot
named by that release's completed ready. -/
theorem valueFragmentReleasedDescriptor {owner position : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g position)
    (hForm : release.form = valueReleaseForm (decide (block.val < 2)))
    (hAfter : TraceBefore X (g,release.matched.wait) (g,index))
    (hBefore : TraceBefore X (g,index) (g,release.index)) :
    op.b = sharedDescriptor (kvStart l slot.val + pvFragment step) 16384 := by
  let observe (f : ReleaseForm) := ReleaseReadyObservation X g release.matched.wait f
    (readyObject l g release.matched.slot) release.matched.parity
  have hObs := Eq.mp (congrArg observe hForm) release.matched.readyForm
  let count (f : ReleaseForm) := readyOccurrence X g release.matched.wait f =
    releaseOccurrence X g release.index f
  have hOrd := Eq.mp (congrArg count hForm) release.matched.ordinal
  have hMatch := release.matched.ready
  dsimp only [observe] at hObs
  rw [release.matchedSlot] at hObs hMatch
  exact valueFragmentDescriptorOfReadyAndRelease hp hX hFragment hObs hMatch hOrd hAfter hBefore

/-- The latest V acquisition determines both the operand's shared slot and its
logical use, including when the K acquire in the same iteration is visible. -/
theorem valueFragmentUse :
    ∃ use, LatestValueReadyUse l X g index use ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ PvShape l g op := by
  obtain ⟨use, _, wait, hDescriptor, hB, hShape, hPoll, _, _, hRank, hBefore, hOnly⟩ :=
    actualValueReadyOfFragment hp hX hFragment
  exact ⟨use, ⟨wait,hPoll,hRank,hDescriptor.2.2,hBefore,hOnly⟩, hB, hShape⟩
end

/-- A released generation of the B slot is ordered after the given V use. -/
theorem valueBeforeReleaseOfUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index d use : Nat} {block : Fin 4} {step : Fin 8} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (hFragment : PvInstruction X (g,index) block step d op accum mask)
    {owner position : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g position)
    (hLatest : LatestValueReadyUse l X g index use)
    (hSlot : slot = readyStage use) (hBound : use ≤ 3 * release.ordinal + slot.val) :
    TraceBefore X (g,index) (g,release.index) := by
  obtain ⟨actual, _, wait, hDescriptor, _, _, hPoll, hReady, hOrdinal, hRank, hBefore, hOnly⟩ :=
    actualValueReadyOfFragment hp hX hFragment
  have hOdd := hDescriptor.2.2
  have hExact : LatestValueReadyUse l X g index actual := ⟨wait,hPoll,hRank,hOdd,hBefore,hOnly⟩
  obtain rfl := hLatest.unique hExact
  exact valueFragmentBeforeRelease hp hX ⟨_,hFragment.decoded⟩ release hPoll hReady
    hOrdinal hRank hOdd hOnly hSlot hBound

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
