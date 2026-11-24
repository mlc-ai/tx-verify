-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxCreditReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Flow.NthEv
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow Thread Prologue

/-- A successful statistics-buffer acquire observed by the softmax lane. -/
abbrev CreditAcquired (X : Execution) (i : EvId) : Prop := Softmax.StatsCreditAcquired X i

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The credit observation gives the successful poll payload for the lane's stage. -/
theorem CreditAcquired.waits {i : EvId} (h : CreditAcquired X i) :
    ∃ site parity acquire scope, X.get i =
      some ⟨site, .wait
        ⟨.shared, i.1 / l.block, l.sharedBase + (192 + 8 * (warpIndex l i.1 / 4))⟩
        parity true acquire scope⟩ := by
  obtain ⟨⟨site, kind⟩, parity, acquire, scope, he, hKind⟩ := Softmax.creditAcquireObject hp hX h
  change kind = _ at hKind
  exact ⟨site, parity, acquire, scope, hKind ▸ he⟩

private theorem acquireBeforeEvent {g j n : Nat} {last : Event} (hLast : X.get (g,j) = some last)
    (hExtent : n < ((X.tr g).take j).countP creditAcquired) :
    ∃ k < j, CreditAcquired X (g,k) ∧ (before X (g,k)).credits = n ∧
      Resumes kernel X (g,k) (g,j) := by
  obtain ⟨k, hk, e, he, hm, hOrd⟩ := exists_nth Scores.creditAcquired (X.tr g)
    (n := n) (k := j) hExtent
  have hMarked := Softmax.creditAcquiredOfObservation (i := (g,k)) he hm
  obtain ⟨f, q, acq, sc, hf, hKind⟩ := Softmax.creditAcquireObject hp hX hMarked
  let loc : Loc := ⟨.shared, g/l.block, l.sharedBase + (192+8*(warpIndex l g/4))⟩
  have hEq : f = ⟨f.pc,.wait loc q true acq sc⟩ := by
    cases f
    exact congrArg (Event.mk _) hKind
  have hf' := hf.trans (congrArg some hEq)
  obtain ⟨pc, hSpin⟩ := actualCanonicalPoll hX hf'
  have hTrace : TraceBefore X (g,k) (g,j) :=
    ⟨rfl, hk, (List.getElem?_eq_some_iff.mp hLast).1⟩
  refine ⟨k, hk, hMarked, (Scores.beforeCredits X (g,k)).trans hOrd, hTrace, ?_⟩
  simp only [hf', Option.map_some, Kind.resume]
  exact ⟨f.pc, pc, loc, q, acq, sc, hf', hSpin, hTrace⟩

/-- A publication depends on the successful acquire of every earlier credit ordinal. -/
theorem acquireBeforePublication {g j n : Nat} {round : Scores.Round}
    (hPub : Scores.Publishes X (g,j) round) (hw : warpIndex l g < 8)
    (hN : n ≤ (Scores.before X (g,j)).barrier (3 + warpIndex l g)) :
    ∃ k < j, CreditAcquired X (g,k) ∧ (Scores.before X (g,k)).credits = n ∧
      Resumes kernel X (g,k) (g,j) := by
  have hCredits := Softmax.creditCursorBeforePublication hp hX hPub
  rw [Scores.notificationOrdinal hp hX hw, Scores.beforeCredits] at hCredits
  change (Scores.before X (g,j)).barrier (3+warpIndex l g) + 1 ≤
    ((X.tr g).take j).countP Scores.creditAcquired at hCredits
  obtain ⟨e, he, _⟩ := hPub
  exact acquireBeforeEvent hp hX he (by omega)

/-- A reached statistics store has already passed the acquire of its own and earlier uses. -/
theorem acquireBeforeStatisticsStore {g j n : Nat} {site : Fin 4} {a : Acc} {bytes : List Byte}
    (hStore : StatisticsStore X (g, j) site a bytes) (hBound : n ≤ (before X (g, j)).notices) :
    ∃ k < j, CreditAcquired X (g, k) ∧ (before X (g, k)).credits = n ∧
      Resumes kernel X (g, k) (g, j) := by
  have hCredits := Softmax.creditCursorBeforeStatisticsStore hp hX hStore
  rw [beforeCredits] at hCredits
  change (before X (g, j)).notices + 1 ≤
    ((X.tr g).take j).countP creditAcquired at hCredits
  exact acquireBeforeEvent hp hX hStore (by omega)

/-- Each publication increments the statistics rendezvous generation of its lane. -/
theorem publicationOrdinalIncreases {g i j : Nat} {a : Scores.Round}
    (hFirst : Scores.Publishes X (g,i) a) (h : i < j) :
    (Scores.before X (g,i)).barrier (3 + warpIndex l g) <
      (Scores.before X (g,j)).barrier (3 + warpIndex l g) := by
  obtain ⟨_, ⟨e,he,hKind,_,_⟩, _⟩ := Scores.publishes hp hX hFirst
  have he' : X.get (g,i) = some e := he
  have hm : Execution.isBarId (3 + warpIndex l g) e = true := by
    simp [Execution.isBarId, hKind]
  have hNext := countP_take_succ he' hm
  have hMono := countP_take_mono (Execution.isBarId (3+warpIndex l g)) (X.tr g) (i := i+1)
    (j := j) (by omega)
  rw [Scores.barrierOrdinal, Scores.barrierOrdinal]
  change ((X.tr g).take i).countP _ < ((X.tr g).take j).countP _
  omega

omit hp hX in
theorem observedOrdinal (X : Execution) (i : EvId) (id : Nat) :
    (before X i).barrier id = observedBarrierOrdinal X i id := barrierOrdinal X i id

/-- A reached publication cursor supplies each earlier actual publication and its generation. -/
theorem publicationAtOrdinal {g n : Nat} (hw : warpIndex l g < 8)
    (hN : n < (before X (g,(X.tr g).length)).notices) :
    ∃ j, BarrierArrival X (g,j) (3 + warpIndex l g) (some 64) .arrive ∧
      observedBarrierOrdinal X (g,j) (3 + warpIndex l g) = n := by
  rw [beforeNotices] at hN
  change n < ((X.tr g).take (X.tr g).length).countP publishesStats at hN
  rw [List.take_length] at hN
  obtain ⟨e, he, hm, hOrd⟩ := nthEv_spec hN
  obtain ⟨round, hr⟩ := Option.isSome_iff_exists.mp hm
  let j := nthEv X publishesStats g n
  have hPub : Publishes X (g,j) round := ⟨e, he, hr⟩
  obtain ⟨_, ⟨f, hf, hk, _, _⟩, _⟩ := publishes hp hX hPub
  refine ⟨j, ⟨f, hf, hk⟩, ?_⟩
  have hCursor := notificationOrdinal (j := j) hp hX hw
  rw [beforeNotices, barrierOrdinal] at hCursor
  exact hCursor.symm.trans hOrd

omit hp hX in
/-- A successful terminal acquire of the statistics buffer. -/
abbrev TerminalAcquire (X : Execution) (i : EvId) : Prop := Softmax.TerminalCredit X i

/-- The terminal acquire follows all publications of an exited softmax lane. -/
theorem terminalAcquireBeforeExit {g j : Nat} {e : Event} (hw : warpIndex l g < 8)
    (he : X.get (g,j) = some e) (hExit : e.kind = .exit) :
    ∃ k < j, TerminalAcquire X (g,k) ∧
      (before X (g,j)).notices ≤ (before X (g,k)).credits :=
  Softmax.terminalCreditBeforeExit hp hX hw he hExit

/-- An exit depends on the successful acquire at each ordinal through its last publication. -/
theorem acquireBeforeExit {g j n : Nat} {e : Event} (hw : warpIndex l g < 8)
    (he : X.get (g,j) = some e) (hExit : e.kind = .exit) (hOrd : n ≤ (before X (g,j)).notices) :
    ∃ k < j, CreditAcquired X (g,k) ∧ (before X (g,k)).credits = n ∧
      Resumes kernel X (g,k) (g,j) := by
  obtain ⟨k, hK, hTerminal, hCount⟩ := terminalAcquireBeforeExit hp hX hw he hExit
  obtain ⟨f, hf, hMark⟩ := Softmax.creditObservationOfAcquire hTerminal.acquired
  have hNext := countP_take_succ hf hMark
  have hMono := countP_take_mono creditAcquired (X.tr g) (i := k+1) (j := j) (by omega)
  rw [beforeCredits] at hCount
  change (before X (g,j)).notices ≤ ((X.tr g).take k).countP creditAcquired at hCount
  exact acquireBeforeEvent hp hX he (by omega)

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
