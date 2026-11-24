-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyFacts
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyGuard
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
public import Lemmas.Protocol.CountNth

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy
open Mma.Observation (emptyObject)
open PTX.Kernels.TmlFa4Fwd.Loader (namesReady readyOrdinal emptySlot emptySlot_address)

noncomputable section

/-- The consumer and producer observations name the same initialized ready slot. -/
theorem acquireOfMmaPoll {l : Launch} {X : Execution} {g index parity : Nat} {slot : Fin 3}
    (h : Mma.ReadyPoll l X g index slot parity true .cta) :
    ReadyAcquire l X (g, index) slot := by
  obtain ⟨e, he, hk⟩ := h
  exact ⟨e, parity, he, hk⟩

/-- The producer's abstract slot count is the log origin's per-slot ordinal. -/
theorem publicationOrdinalAtObject {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {issue : EvId} {slot : Fin 3}
    (h : X.AsyncArrive issue (readyObject l g slot) true) :
    ((atPrefix l X issue.1 issue.2).published.countP (fun pub => pub.slot == slot)) =
      PTX.Kernels.TmlFa4Fwd.Loader.readyOrdinal X (readyObject l g slot) issue := by
  obtain ⟨pc, he⟩ := h
  obtain ⟨pub, _, hl, _⟩ := readyObservation hp hX he rfl
  have hCta := congrArg Loc.cta hl
  have hObj : readyObject l issue.1 slot = readyObject l g slot := by
    change g / l.block = issue.1 / l.block at hCta
    unfold readyObject
    rw [hCta]
  simpa only [hObj] using publicationOrdinal hp hX issue.1 issue.2 slot

/-- A group copy guarded by the loader's successful empty wait transmits that wait's
dependency to every completed publication that tracks the copy. -/
theorem guardedCopyBeforePublication {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {wait copy publication : EvId}
    (hGuard : Resumes kernel X wait copy) (hTrack : TracksCpAsync X copy publication)
    (hDone : X.async.arrived publication = true) :
    Relation.TransGen (DepStep l kernel X) (.thread wait, true)
      (.async publication .arriveOn, false) :=
  PTX.Kernels.TmlFa4Fwd.Loader.loaderEmptyAcquireBeforeArriveOn hX hGuard hTrack hDone

/-- A successful acquire of the loader's empty barrier at the specified slot. -/
def EmptyAcquire (l : Launch) (X : Execution) (wait : EvId) (slot : Fin 3)
    (parity : Nat) : Prop :=
  ∃ ev, X.get wait = some ev ∧ ev.kind = .wait (emptyObject l wait.1 slot) parity true true .cta

/-- Two empty objects can be equal only if they name the same slot. -/
theorem emptyObjectSlotEq {l : Launch} {g h : Nat} {s t : Fin 3}
    (he : emptyObject l g s = emptyObject l h t) : s = t := by
  have hAddr := congrArg Loc.addr he
  change (Prologue.initObject l (g / l.block) (emptySlot s)).addr =
    (Prologue.initObject l (h / l.block) (emptySlot t)).addr at hAddr
  rw [emptySlot_address, emptySlot_address] at hAddr
  simp only at hAddr
  exact Fin.ext (by omega)

/-- Every lower publication ordinal on a given slot is realized earlier by that producer. -/
theorem earlierPublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g n : Nat} {publication : EvId} {slot : Fin 3}
    (hPub : X.AsyncArrive publication (readyObject l g slot) true)
    (hBefore : n < ((atPrefix l X publication.1 publication.2).published.countP
      (fun pub => pub.slot == slot))) :
    ∃ i < publication.2, X.AsyncArrive (publication.1, i) (readyObject l g slot) true ∧
      ((atPrefix l X publication.1 i).published.countP (fun pub => pub.slot == slot)) = n := by
  let loc := readyObject l g slot
  let es := (X.tr publication.1).take publication.2
  rw [publicationOrdinalAtObject hp hX hPub] at hBefore
  change n < es.countP (namesReady loc) at hBefore
  obtain ⟨i, ev, he, hm, hPrefix⟩ := Slot.exists_nth_countP (namesReady loc) hBefore
  have hI : i < publication.2 := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only [es, List.length_take] at this
    omega
  have hEvent : X.get (publication.1, i) = some ev := by
    change (X.tr publication.1)[i]? = some ev
    simpa only [es, List.getElem?_take_of_lt hI] using he
  have hMarked : ev.kind = .asyncArrive loc true := by
    cases hk : ev.kind <;> simp [namesReady, hk] at hm
    rename_i target noinc
    cases noinc <;> simp_all
  have hEarlier : X.AsyncArrive (publication.1, i) loc true := by
    refine ⟨ev.pc, ?_⟩
    simpa only [← hMarked] using hEvent
  refine ⟨i, hI, hEarlier, ?_⟩
  rw [show _ = readyOrdinal X loc (publication.1, i) from
    publicationOrdinalAtObject hp hX hEarlier]
  simpa only [readyOrdinal, es, List.take_take, Nat.min_eq_left hI.le] using hPrefix

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
