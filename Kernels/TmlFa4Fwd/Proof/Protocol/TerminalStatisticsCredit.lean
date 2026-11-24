-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningStatisticsCredit
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics
import Lemmas.Step.CtaBarNamed
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Protocol.UnitReachBlocker
import Lemmas.Protocol.MbarOneShot
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier PTX.MbarRing.Unit Correction Thread Epilogue

/-- All correction participants have published the credit of the terminal statistics
generation for this query tile. -/
def TerminalCorrectionCredits (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2)
    (blocks : Nat) : Prop :=
  ∀ lane : Fin 128, ∃ j event,
    let i := (statsCreditLane l cta lane,j)
    X.get i = some event ∧ correctionAction event = some (.statsCredit stage) ∧
      (correctionBefore X i).count (.statsCredit stage) = blocks

private theorem terminalCreditLaneCta {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (cta : Nat) (lane : Fin 128) : statsCreditLane l cta lane/l.block = cta := by
  rw [statsCreditLane,hp.block]
  have := lane.isLt
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- At any generation, actual returns from all 128 participants advance the
physical statistics object beyond that generation. -/
theorem statisticsPhaseAdvancedOfCredits (hDeps : CreditAcquireDependencies l X) {cta trips : Nat}
    (stage : Fin 2) (credits : TerminalCorrectionCredits l X cta stage trips) :
    let log := X.objects (statsCreditLoc l cta stage)
    ∃ state, stateBefore log log.length = some state ∧ trips+1 ≤ state.phase := by
  dsimp only
  let addr := statsCreditLoc l cta stage
  let log := X.objects addr
  let O := statsCreditObject hp hX cta stage
  have hEvents (lane : Fin 128) : ∃ i e,
      X.get (statsCreditLane l cta lane,i) = some e ∧ e.kind = .arrive addr 0 1 true .cta ∧
      arrivals addr ((X.tr (statsCreditLane l cta lane)).take i) = trips := by
    obtain ⟨i,e,he,hAction,hOrd⟩ := credits lane
    obtain ⟨target,units,hKind⟩ := correctionStatsCreditKind hAction
    have hm := (correctionStatsCreditMark_iff stage e).mpr
      ((correctionStatsCreditObservation stage hKind).mp hAction)
    have hKind' := correctionStatsCreditPayload hp hX stage he hm hKind
    have hLoc := terminalCreditLaneCta hp cta lane
    dsimp only at hKind' hOrd
    rw [hLoc] at hKind'
    refine ⟨i,e,he,hKind',?_⟩
    simpa only [hLoc,addr] using (statsCreditArrivalCursor hp hX stage he).trans hOrd
  obtain ⟨i,e,he,hKind,_⟩ := hEvents 0
  have hAct : objectAction X X.async addr (.thread (statsCreditLane l cta 0,i)) =
      some (.arrive 1 0) := by
    obtain ⟨pc,kind⟩ := e
    change kind = _ at hKind
    subst kind
    simp [objectAction,he]
  obtain ⟨k,record,hRecord,_,_⟩ := MbarOneShot.Hist.record_of_action hX hAct
  have hNonempty : log ≠ [] := by
    intro h
    change log[k]? = some record at hRecord
    rw [h] at hRecord
    simp at hRecord
  obtain ⟨state,hState⟩ := final_of_init hX O.init O.noInval hNonempty
  obtain ⟨lane,hShort⟩ := O.blocked hX hState
  obtain ⟨last,event,hLast,hLastKind,hPrev⟩ := hEvents lane
  have hAdvance : arrivals addr ((X.tr (statsCreditLane l cta lane)).take (last+1)) =
      trips+1 := by
    unfold arrivals at hPrev ⊢
    rw [countP_take_succ hLast (by simp [arrivesOn,sourceArrive,hLastKind]),hPrev]
  have hLower : trips+1 ≤ state.phase := by
    have hLen : last+1 ≤ (X.tr (statsCreditLane l cta lane)).length := len_of_get hLast
    have hm := countP_take_mono (arrivesOn addr) (X.tr (statsCreditLane l cta lane)) hLen
    rw [List.take_length] at hm
    exact hAdvance.symm.le.trans (hm.trans ((arrivals_le_unitRec (m := addr) hX
      (fun _ hr => creditHistoryClean hp hX hDeps (cta := cta) stage hr) _).trans hShort))
  exact ⟨state,hState,hLower⟩

/-- The complete cohort's terminal publications advance the statistics credit object to
the phase immediately after the tile's last score visit. -/
theorem terminalStatisticsPhaseOfCredits (hDeps : CreditAcquireDependencies l X) {cta batch : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads) (stage : Fin 2)
    (hFinal : TerminalCorrectionCredits l X cta stage
      (Mma.trips p batch (assignedCoordinates p batch cta).1)) :
    let log := X.objects (statsCreditLoc l cta stage)
    ∃ state, stateBefore log log.length = some state ∧
      state.phase = Mma.trips p batch (assignedCoordinates p batch cta).1+1 := by
  dsimp only
  let addr := statsCreditLoc l cta stage
  let log := X.objects addr
  let trips := Mma.trips p batch (assignedCoordinates p batch cta).1
  let O := statsCreditObject hp hX cta stage
  obtain ⟨state,hState,hLower⟩ := statisticsPhaseAdvancedOfCredits hp hX hDeps stage hFinal
  have hUse {q : Nat} {k : Nat} {r : Record Ref} {lane : Fin 128} {j c tx : Nat}
      (hk : log[k]? = some r) (hA : r.action = .arrive c tx)
      (hId : r.id = .thread (statsCreditLane l cta lane,j))
      (hPhase : phaseAt log k = some q) :
      arrivals addr ((X.tr (statsCreditLane l cta lane)).take j) = q := by
    have hRank := (creditArrivalPhase hp hX hDeps (cta := cta) stage hk hA).2
    rw [hPhase,hId] at hRank
    obtain ⟨pc,scope,hE⟩ := O.arrive_of_id hk hA hId
    have hAt := statsCreditArrivalCursor hp hX stage hE
    rw [terminalCreditLaneCta hp cta lane] at hAt
    exact hAt.trans (Option.some.inj hRank).symm
  have hUpper : state.phase ≤ trips+1 := by
    by_contra! hLarge
    obtain ⟨k,r,j,_,hk,_,hA,hId,hPhase,_⟩ :=
      O.phase_all hX le_rfl hState hLarge
        (fun k _ r a j c tx hK _ hA hI hRank => hUse hK hA hI hRank) 0
    cases statsCreditHistorySource hp hX stage (List.mem_of_getElem? hk) with
    | init hh => rw [hA] at hh; cases hh
    | poll hh => rw [hA] at hh; cases hh
    | @credit i e hi he _ hAction hCta _ _ _ =>
      have hWork : cta < tilePrefix p p.batch*p.heads :=
        hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
      obtain ⟨other,ho,hoLo,hoHi,hBound⟩ := correctionCreditsWithinTrips hp hX
        (hCta.symm ▸ hWork) (usedKProtected hp hX) stage he hAction
      have hSame := (tileBatch_existsUnique p hWork).unique
        ⟨ho,hCta ▸ hoLo,hCta ▸ hoHi⟩ ⟨hb,hLo,hHi⟩
      rw [hSame,hCta] at hBound
      have hRank := (creditArrivalPhase hp hX hDeps (cta := cta) stage hk hA).2
      rw [hPhase,hi] at hRank
      exact (Nat.not_succ_le_self trips) ((Option.some.inj hRank).le.trans hBound)
  exact ⟨state,hState,Nat.le_antisymm hUpper hLower⟩

/-- A completed named terminal generation releases its softmax producer's recorded
arrival. This is the release needed to resume the scheduler drain after publication. -/
theorem terminalProducerReleasedOfSynchronization {g j : Nat} (hg : g < l.threads)
    (hw : Prologue.warpIndex l g < 8) (hPub : Scores.Publishes X (g,j) .final)
    (hLast : j+1 = (X.tr g).length)
    (hDone : CtaBarrier.Released l.block (X.barriers (g/l.block))
      (3+Prologue.warpIndex l g)
      ((X.tr g).take j |>.countP (Execution.isBarId (3+Prologue.warpIndex l g)))) :
    Step.Released l X g := by
  let warp : Fin 8 := ⟨Prologue.warpIndex l g,hw⟩
  obtain ⟨_,⟨e,he,hKind,_,_⟩,_⟩ := Scores.publishes hp hX hPub
  have hGet : X.get (g,j) = some ⟨e.pc,.bar (3+warp.val) (some 64) .arrive⟩ := by
    rcases e with ⟨pc,kind⟩
    change kind = _ at hKind
    subst kind
    exact he
  have hk := (statsBarrierSources hp hX warp).key_of_released hX
    (statsBarrierShape hp warp) hGet hg hDone
  have hReady := NamedBar.ready_of_arrivalK hX.ctaBar hGet hk
  constructor
  intro pc kind hAt _
  have idx : (X.tr g).length-1 = j := by omega
  rwa [idx]

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
