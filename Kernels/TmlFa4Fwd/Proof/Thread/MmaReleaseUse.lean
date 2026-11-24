-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (emptyObject readyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The actual successful first K poll is the first ready acquisition. -/
private theorem firstKeyPollRank {g wait parity : Nat} {loc : Loc} {acq : Bool} {scope : MbarScope}
    (hw : Prologue.warpIndex l g = 12)
    (he : X.get (g,wait) = some ⟨2145,.wait loc parity true acq scope⟩) :
    readyCount X g wait = 0 := by
  obtain ⟨hLoc,hPhase,hAcq,hScope⟩ := initialReadyPollOperands hp hX he
  have hReady : ReadyPoll l X g wait 0 0 true .cta := by
    refine ⟨_,he,?_⟩
    rw [hLoc,hPhase,hAcq,hScope]
    rfl
  obtain ⟨gate,hGet,hSite⟩ := hReady.useSite hp hX hw
  have hGate : gate = readyHead 0 :=
    congrArg Event.pc (Option.some.inj (hGet.symm.trans he))
  rw [hGate] at hSite
  rcases hSite with ⟨_,hZero⟩ | ⟨hGate,_,_⟩ | ⟨hGate,_⟩
  · exact hZero
  · contradiction
  · rcases hGate with h | h <;> contradiction

/-- The actual opening K poll has zero previous uses of its slot in the lane summary. -/
theorem firstKeyAcquireOrdinal {g i q : Nat} {loc : Loc} {acq : Bool} {scope : MbarScope}
    (hw : Prologue.warpIndex l g = 12) (he : X.get (g,i) = some ⟨2145,.wait loc q true acq scope⟩) :
    (atPrefix l X g i).kvAcquires 0 = 0 := by
  have hr := firstKeyPollRank hp hX hw he
  have hCount := readyUsesAtPrefix hp hX (g := g) (event_thread_lt hX he) hw i
  change readyCount X g i = _ at hCount
  omega

/-- The successful startup K acquisition on a lane is unique. -/
theorem firstKeyAcquireUnique {g i j qa qb : Nat} {a b : Loc} {pa pb : Bool} {sa sb : MbarScope}
    (hw : Prologue.warpIndex l g = 12) (ha : X.get (g,i) = some ⟨2145,.wait a qa true pa sa⟩)
    (hb : X.get (g,j) = some ⟨2145,.wait b qb true pb sb⟩) : i = j := by
  have hRank := (firstKeyPollRank hp hX hw ha).trans (firstKeyPollRank hp hX hw hb).symm
  unfold readyCount at hRank
  rw [List.length_filterMap_eq_countP,List.length_filterMap_eq_countP] at hRank
  have hHead : (List.finRange 4).any (fun i => readyHead i == 2145) = true := by decide
  exact eq_of_count_eq _ (X.tr g) ha (by simp [readyEvent,hHead])
    hb (by simp [readyEvent,hHead]) hRank

omit hp hX in
/-- The startup K release matches the actual successful startup acquisition. -/
theorem EmptyReleaseAt.firstKeyAcquireDecoded {l : Launch} {X : Execution}
    {owner g position : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g position)
    (hForm : release.form = .firstKey) :
    X.get (g,release.matched.wait) = some ⟨2145,
      .wait (readyObject l g release.matched.slot) release.matched.parity true true .cta⟩ := by
  let kind := Kind.wait (readyObject l g release.matched.slot)
    release.matched.parity true true .cta
  have hSite := congrArg (fun form => (slotWait (releaseIndex form)).pc) hForm
  have hEvent := congrArg (fun site => some (Event.mk site kind)) hSite
  exact release.matched.readyForm.trans hEvent

/-- The delivered startup K release is for logical use zero on the cache ring. -/
theorem EmptyReleaseAt.firstKeyUse {owner g position : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g position)
    (hForm : release.form = .firstKey) :
    3 * release.ordinal + slot.val = 0 := by
  have hw := release.issue.issuerWarp hp hX
  have hRank := release.matched.ready.exactOccurrence hp hX hw
  have hZero := firstKeyPollRank hp hX hw (release.firstKeyAcquireDecoded hForm)
  have hThread := event_thread_lt hX release.issue
  have hCount := readyUsesAtPrefix hp hX hThread hw release.matched.wait
  change readyCount X g release.matched.wait = _ at hCount
  rw [hZero] at hCount
  change release.matched.slot.val = _ % 3 ∧ release.ordinal = _ / 3 ∧ _ at hRank
  rw [← hCount,release.matchedSlot] at hRank
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
