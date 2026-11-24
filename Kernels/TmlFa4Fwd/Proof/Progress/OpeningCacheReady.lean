-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstCacheReadyPhase
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstKeyReleaseProgress
import Kernels.TmlFa4Fwd.Proof.Progress.FirstQueryAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing Prologue
open Thread.Mma (ReadyPoll atPrefix)
open Thread.Loader (readyObject)
open Thread.Output (queryObject)

/-- A ready object past its initial completed phase has a recurrent publication. -/
theorem positivePublicationOfAdvancedReady {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (slot : Fin 3) {s : State}
    (hs : let log := X.objects (readyObject l g slot); stateBefore log log.length = some s)
    (hPhase : 1 < s.phase) :
    ∃ issue, X.AsyncArrive issue (readyObject l g slot) true ∧
      0 < Protocol.LoaderReady.generation l X issue slot := by
  let loc := readyObject l g slot
  let log := X.objects loc
  change stateBefore log log.length = some s at hs
  have hNonempty : log ≠ [] := by
    intro h
    rw [h] at hs
    cases hs
  obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil log hNonempty
  have hObj := Loader.actualReadyHistoryObject hp hX slot hr
  have hChecked := X.objects_checked hX loc
  obtain ⟨i,hInit,hAction,hClean,_⟩ := hObj.init r hr
  have hIn := (List.getElem?_eq_some_iff.mp hInit).1
  have hE := ObjectInit.checked_expected_after_init hChecked hObj.noInval
    hInit hAction hClean hIn (Nat.le_refl _)
  obtain ⟨current,hCurrent,hExpected⟩ := hE
  change stateBefore log log.length = some current at hCurrent
  rw [hs] at hCurrent
  obtain rfl := Option.some.inj hCurrent
  have hBalance := ((hChecked.accounted hObj.noInval (Nat.le_refl _)).2 s hs).2
  have hNoIncrement : incrementsBefore log log.length = 0 := hObj.noIncrement
  rw [hExpected,hNoIncrement] at hBalance
  change unitsBefore log log.length + s.pending = 64 * (s.phase+1)+0 at hBalance
  have hPending := ((hChecked.accounted hObj.noInval (Nat.le_refl _)).2 s hs).1
  rw [hExpected,hNoIncrement] at hPending
  by_contra! hNo
  have hUnits : unitsBefore log log.length ≤ 64 * (0+1) := by
    apply Loader.readyUnitsBefore hp hX slot hObj
    dsimp only
    intro k hk r' issue hAt _ ha hId
    obtain ⟨_,_,actual,hActual,hPub,_⟩ := hObj.arrive_source hAt ha
    have hIdEq := (Ref.async.inj (hActual.symm.trans hId)).1
    subst actual
    change Loader.readyOrdinal X (readyObject l g slot) issue ≤ 0
    rw [← Thread.Loader.publicationOrdinalAtObject hp hX hPub]
    exact hNo issue hPub
  omega

/-- An opening cache object past phase one implies that the MMA warp has already
recorded the first K acquire. The later publication used a matching release. -/
theorem openingCacheReadyPhaseOrAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hHistory : let log := X.objects (readyObject l g 0)
      ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase) :
    (let log := X.objects (readyObject l g 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 1) ∨
      ∃ j, ReadyPoll l X g j 0 0 true .cta ∧ (atPrefix l X g j).kvAcquires 0 = 0 := by
  obtain ⟨s, hs, hPhase⟩ := hHistory
  by_cases h : s.phase = 1
  · exact .inl ⟨s,hs,h⟩
  have hLate : 1 < s.phase := by omega
  obtain ⟨issue,hPub,hPositive⟩ := positivePublicationOfAdvancedReady hp hX 0 hs hLate
  let n := Protocol.LoaderReady.generation l X issue 0 - 1
  have hGen : Protocol.LoaderReady.generation l X issue 0 = n+1 := by dsimp [n]; omega
  obtain ⟨guard,peer,_,release,_,_⟩ :=
    Protocol.LoaderReady.actualReleaseForNextPublicationExact hp hX hPub hGen
  have hCta : g/l.block = peer/l.block := by
    rw [Protocol.LoaderReady.publicationCta hp hX hPub,← guard.issuer,
      release.issuerCta hp hX]
  have hWarp : SameWarp l peer g :=
    ⟨⟨PTX.Proof.event_thread_lt hX release.issue,hg,hCta.symm⟩,
      (release.issue.issuerWarp hp hX).trans hw.symm⟩
  exact .inr (release.issue.peerFirstKeyAcquire hp hX hWarp)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

/-- An active MMA lane acquires its opening K packet once the Q0 and K0
object histories reach the corresponding phases. -/
theorem openingKeyAcquireOfReadyHistories {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hQ : let log := X.objects (queryObject l (g / l.block) 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 1)
    (hK : let log := X.objects (readyObject l g 0)
      ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase) :
    ∃ j, ReadyPoll l X g j 0 0 true .cta ∧ (atPrefix l X g j).kvAcquires 0 = 0 := by
  rcases openingCacheReadyPhaseOrAcquire hp hMax.1 hg hw hK with hReady | hAcquired
  · exact (openingAcquiresOfReadyPhase hp hMax hFrame hg hw hb hLo hHi hQ).2 hReady
  · exact hAcquired

/-- Every active MMA lane acquires its opening K packet from the selected loader. -/
theorem openingKeyAcquireOfMaximal {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ j, ReadyPoll l X g j 0 0 true .cta ∧ (atPrefix l X g j).kvAcquires 0 = 0 :=
  openingKeyAcquireOfReadyHistories hp hMax hFrame hg hw hb hLo hHi
    (openingQueryReadyPhaseOfMaximal hp hMax hFrame (NamedBar.cta_lt hg) hb hLo hHi)
    (selectedCacheReadyPhaseOfMaximal hp hMax hFrame (NamedBar.cta_lt hg) hb hLo hHi)

end PTX.Kernels.TmlFa4Fwd.Progress
