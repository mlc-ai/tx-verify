-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.IdleCorrectionCredit
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuseClosure
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsCreditFaults
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Protocol.MbarPending

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Flow PTX.Proof PTX.MBarrier PTX.AsyncCopy Prologue Epilogue Correction

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem statisticsPhaseZeroOfNoCredit (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat} (hc : cta < l.grid) (stage : Fin 2)
    (hNoCredit : ∀ (issue : EvId) (e : Event), X.get issue = some e →
      Thread.correctionAction e = some (.statsCredit stage) → issue.1 / l.block = cta →
      8 ≤ warpIndex l issue.1 → warpIndex l issue.1 < 12 → False) :
    let log := X.objects (statsCreditLoc l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  dsimp only
  let loc := statsCreditLoc l cta stage
  let log := X.objects loc
  obtain ⟨r,hr,hInit⟩ := Thread.statisticsCreditInitialized hp hMax hc stage
  have hAll {r : Record Ref} (hr : r ∈ log) :
      (∃ n, r.action = .init n) ∨ ∃ parity ok, r.action = .pollParity parity ok := by
    cases statsCreditHistorySource hp hMax.1 stage hr with
    | init ha => exact .inl ⟨_,ha⟩
    | poll ha => exact .inr ⟨_,_,ha⟩
    | @credit issue e hId he hMark hAction hOwner hLo hHi hShape =>
      exact (hNoCredit issue e he hAction hOwner hLo hHi).elim
  have hUnits {xs : List (Record Ref)} (h : ∀ r ∈ xs, r ∈ log) : arrivalUnits xs = 0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hTail := ih (fun r hr => h r (List.mem_cons_of_mem x hr))
      rcases hAll (h x List.mem_cons_self) with ⟨n,ha⟩ | ⟨p,ok,ha⟩ <;>
        simp [arrivalUnits,ha,hTail]
  have hNo := objects_noInval hMax.1.tma.2.2.1 (fun _ _ => noMbarInval hMax.1) loc
  have hChecked := X.objects_checked hMax.1 loc
  obtain ⟨s,hs⟩ := stateBefore_length_some hChecked hNo hr hInit (by decide)
  refine ⟨s,hs,?_⟩
  have hExpected :=
    PairTmaRing.expected_of_init hMax.1 (statsCreditHistoryInit hp hMax.1 stage hr) hNo hs
  obtain ⟨hPend,hArr⟩ := (hChecked.accounted hNo (Nat.le_refl log.length)).2 s hs
  have hZero : unitsBefore log log.length = 0 := by
    rw [unitsBefore,List.take_length]
    exact hUnits (fun _ h => h)
  rw [hExpected] at hPend hArr
  change unitsBefore log log.length + s.pending = _ at hArr
  rw [hZero] at hArr
  omega

/-- Neither statistics object advances its phase in an idle CTA. All actual correction
credits require scheduler work, and maximal startup has initialized both objects. -/
theorem idleStatisticsPhaseZero (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (hc : cta < l.grid) (stage : Fin 2) (hIdle : tilePrefix p p.batch * p.heads ≤ cta) :
    let log := X.objects (statsCreditLoc l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  apply statisticsPhaseZeroOfNoCredit hp hMax hc stage
  rintro ⟨g, j⟩ e he hAction hOwner hLo hHi
  have hWork := Thread.statisticsCreditRequiresWork hp hMax.1 he ⟨hLo, hHi⟩ hAction
  rw [show g / l.block = cta from hOwner] at hWork
  exact (Nat.not_lt_of_ge hIdle) hWork

/-- A credit phase cannot advance past zero until each softmax lane of that stage has
acquired its initial buffer. A full phase includes the paired correction warp's credit. -/
theorem initialStatisticsPhaseZeroForPendingLane (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g < 8) (stage : Fin 2)
    (hStage : stage.val = warpIndex l g / 4)
    (hMissing : ¬ ∃ j, Thread.Scores.CreditAcquired X (g,j)) :
    let log := X.objects (statsCreditLoc l (g/l.block) stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  let cta := g / l.block
  let loc := statsCreditLoc l cta stage
  let log := X.objects loc
  have hMax' := hMax.1
  have hc : cta < l.grid := NamedBar.cta_lt hg
  obtain ⟨init, hInit, hAction⟩ := Thread.statisticsCreditInitialized hp hMax hc stage
  let O := statsCreditObject hp hMax' cta stage
  have hLog := X.objects_checked hMax' loc
  obtain ⟨st, hs⟩ := stateBefore_length_some hLog O.noInval hInit hAction (by decide)
  refine ⟨st, hs, ?_⟩
  by_contra! hPhase
  have hPositive : 0 < st.phase := Nat.pos_of_ne_zero hPhase
  let lane : Fin 128 := ⟨32 * (warpIndex l g % 4), by
    have hMod := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    omega⟩
  let peer := statsCreditLane l cta lane
  let inner := 256 + lane.val
  have hBound : inner < l.block := by
    rw [hp.block]
    have := lane.isLt
    dsimp only [inner]
    omega
  have hPeer : peer = cta * l.block + inner := by
    simp [peer, statsCreditLane, inner, Nat.add_assoc]
  obtain ⟨hCta, hLocal⟩ := NamedBar.lane_cta (c := cta)
    (NamedBar.block_pos_of_thread_lt hg) hBound
  have hSame : g / l.block = peer / l.block := by
    rw [hPeer, hCta]
  have hPair : Paired l g peer stage := by
    unfold Paired Correction.statsBarrierId
    have hWarp : warpIndex l peer = 8 + warpIndex l g % 4 := by
      change peer % l.block / 32 = 8 + warpIndex l g % 4
      rw [hPeer, hLocal]
      change (256 + 32 * (warpIndex l g % 4)) / 32 = _
      omega
    rw [hWarp, hStage]
    omega
  have hUsedK := usedKProtected hp hMax'
  have hDeps := creditDependenciesOfCountedExitBound hp hMax'
    (countedExitCreditBound hp hMax' hCuQ hUsedK)
  obtain ⟨pos, record, j, _, hRecord, _, hArrival, hId, _, _⟩ :=
    O.phase_all hMax' (j := log.length) (q := 0) le_rfl hs hPositive
      (fun k _ r a i c tx hr _ hArr hid hPh => by
        have hExact := (creditArrivalPhase hp hMax' hDeps stage hr hArr).2
        rw [hid, hPh, Option.some.injEq] at hExact
        obtain ⟨site, scope, he⟩ := O.arrive_of_id hr hArr hid
        have hOwner : statsCreditLane l cta a / l.block = cta := by
          have ha := a.isLt
          have hIn : 256 + a.val < l.block := by rw [hp.block]; omega
          simpa only [statsCreditLane, Nat.add_assoc] using (NamedBar.lane_cta (c := cta)
            (NamedBar.block_pos_of_thread_lt hg) hIn).1
        simpa only [hOwner] using (statsCreditArrivalCursor hp hMax' stage he).trans hExact.symm)
      lane
  obtain ⟨site, scope, he⟩ := O.arrive_of_id hRecord hArrival hId
  have hCredit := statsCreditArrivalAction hp hMax' stage he
  obtain ⟨j', hAcquired, _, _⟩ :=
    creditDependsOnSelectedProducer hp hMax' he hCredit hSame hPair
      (fun _ _ _ _ _ _ hGet hExit => by
        obtain ⟨w, _, hWait, _, _⟩ :=
          Thread.Scores.acquireBeforeExit hp hMax' hw hGet hExit (Nat.zero_le _)
        exact (hMissing ⟨w, hWait⟩).elim)
      (n := 0) (Nat.zero_le _)
  exact hMissing ⟨j', hAcquired⟩

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
