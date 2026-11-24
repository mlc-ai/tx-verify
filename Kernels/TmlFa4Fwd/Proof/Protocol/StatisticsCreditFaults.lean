-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuse
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.MbarPending
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing PTX.Flow Thread Correction Prologue

/-- Every actual correction arrival is clean and belongs to its exact credit generation. -/
theorem creditArrivalPhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDeps : CreditAcquireDependencies l X)
    {cta k c tx : Nat} (stage : Fin 2) {r : Record Ref}
    (hRecord : (X.objects (statsCreditLoc l cta stage))[k]? = some r)
    (hArrival : r.action = .arrive c tx) :
    r.fault = none ∧ phaseAt (X.objects (statsCreditLoc l cta stage)) k =
      some ((correctionBefore X r.id.issuer).count (.statsCredit stage)) := by
  have hr := List.mem_of_getElem? hRecord
  classical
  let loc := statsCreditLoc l cta stage
  let log := X.objects loc
  let lanes := (Finset.univ : Finset (Fin 128)).image (statsCreditLane l cta)
  let label (ref : Ref) := (ref.issuer.1,
    (correctionBefore X ref.issuer).count (.statsCredit stage))
  have hCard : lanes.card = 128 := by
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j h
    apply Fin.ext
    unfold statsCreditLane at h
    omega
  have hInit := statsCreditHistoryInit hp hX stage hr
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hSource (r : Record Ref) (hr : r ∈ log) := statsCreditHistorySource hp hX stage hr
  have hUnit (r : Record Ref) (hr : r ∈ log) (c tx : Nat) (ha : r.action = .arrive c tx) :
      c = 1 ∧ tx = 0 ∧ ∃ issue e, r.id = .thread issue ∧ X.get issue = some e ∧
        correctionStatsCreditMark stage e = true ∧ correctionAction e = some (.statsCredit stage) ∧
        issue.1 / l.block = cta ∧ 8 ≤ warpIndex l issue.1 ∧ warpIndex l issue.1 < 12 := by
    cases hSource r hr with
    | init hi | poll hi => rw [ha] at hi; cases hi
    | @credit issue e hId he hMarked hAction hOwner hLo hHi hActual =>
      obtain ⟨rfl, rfl⟩ := Action.arrive.inj (ha.symm.trans hActual)
      exact ⟨rfl, rfl, issue, e, hId, he, hMarked, hAction, hOwner, hLo, hHi⟩
  have hNoTx (r : Record Ref) (hr : r ∈ log) (n : Nat) : r.action ≠ .completeTx n := by
    intro h
    cases hSource r hr with
    | init ha | poll ha | credit _ _ _ _ _ _ _ ha => rw [h] at ha; cases ha
  have hNoIncr (r : Record Ref) (hr : r ∈ log) : r.action ≠ .increment := by
    intro h
    cases hSource r hr with
    | init ha | poll ha | credit _ _ _ _ _ _ _ ha => rw [h] at ha; cases ha
  have hState i st hLen (hs : stateBefore log i = some st) :
      st.expected = 128 ∧ st.tx = 0 :=
    ⟨PairTmaRing.expected_of_init hX hInit hNo hs,
      tx_zero_of hX hNo (fun r hr c tx ha => (hUnit r hr c tx ha).2.1) hNoTx hLen hs⟩
  have hGated := hChecked.gated_arrive hNo lanes label
    (fun i st hLen hs => ⟨hCard.symm ▸ (hState i st hLen hs).1, (hState i st hLen hs).2⟩)
    (fun k r c tx hk ha => by
      obtain ⟨_, st, hs, _⟩ := PairTmaRing.state_of_init hX hInit hNo hk
        (by intro n; rw [ha]; simp)
      exact ⟨st, hs⟩)
    (fun k r c tx hk ha => by
      obtain ⟨rfl, rfl, issue, _, hId, _, _, _, hOwner, hLo, hHi⟩ :=
        hUnit r (List.mem_of_getElem? hk) c tx ha
      refine ⟨rfl, rfl, ?_⟩
      rw [hId]
      change issue.1 ∈ lanes
      unfold warpIndex at hLo hHi
      let lane : Fin 128 := ⟨issue.1 % l.block - 256, by omega⟩
      have hPhys : statsCreditLane l cta lane = issue.1 := by
        have hDecomp := Nat.div_add_mod issue.1 l.block
        rw [hOwner, Nat.mul_comm] at hDecomp
        dsimp [statsCreditLane, lane]
        omega
      rw [← hPhys]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ lane))
    (fun k k' r r' c tx c' tx' hk hk' ha ha' hLabel => by
      obtain ⟨_, _, issue, _, hId, he, hm, _, _, _, _⟩ :=
        hUnit r (List.mem_of_getElem? hk) c tx ha
      obtain ⟨_, _, other, _, hOtherId, he', hm', _, _, _, _⟩ :=
        hUnit r' (List.mem_of_getElem? hk') c' tx' ha'
      rw [hId, hOtherId] at hLabel
      change (issue.1, (correctionBefore X issue).count (.statsCredit stage)) =
        (other.1, (correctionBefore X other).count (.statsCredit stage)) at hLabel
      obtain ⟨hThread, hUse⟩ := Prod.mk.inj hLabel
      rw [correctionCreditCursor hp hX stage he, correctionCreditCursor hp hX stage he'] at hUse
      have hIndex : issue.2 = other.2 := calc
        issue.2 = _ := (nthEv_eq he hm).symm
        _ = nthEv X (correctionStatsCreditMark stage) other.1
            (((X.tr other.1).take other.2).countP (correctionStatsCreditMark stage)) := by
          rw [hUse, hThread]
        _ = other.2 := nthEv_eq he' hm'
      apply ObjectInit.checked_record_index_eq hChecked hk hk'
      rw [hId, hOtherId, Prod.ext hThread hIndex])
    (fun k r c tx hk ha _ => by
      obtain ⟨_, _, issue, obs, hId, he, _, hc, hOwner, _, _⟩ :=
        hUnit r (List.mem_of_getElem? hk) c tx ha
      let n := (correctionBefore X issue).count (.statsCredit stage)
      obtain ⟨⟨g, wait⟩, hSame, hPair, hAcq, hOrdinal, hPath⟩ :=
        hDeps stage issue obs he hc n (Nat.le_refl _)
      have hStage : stage.val = warpIndex l g / 4 := by
        change 3 + warpIndex l g = warpIndex l issue.1 % 4 + 3 + 4 * stage.val at hPair
        have hMod := Nat.mod_lt (warpIndex l issue.1) (by decide : 0 < 4)
        omega
      obtain ⟨j, poll, hPoll, hPollId, hSuccess, hUnits⟩ :=
        statsCreditUnitsOfAcquire hp hX stage hStage hAcq
      change g / l.block = issue.1 / l.block at hSame
      dsimp only at hPoll hUnits
      rw [hSame, hOwner] at hPoll hUnits
      have hBefore : j < k := by
        rcases Nat.lt_trichotomy j k with hLt | hEq | hGt
        · exact hLt
        · obtain ⟨_, _, _, hPollAction, _, _⟩ := hChecked.okPoll hPoll hSuccess
          rw [hEq, hk] at hPoll
          have hEqual := Option.some.inj hPoll
          rw [← hEqual, ha] at hPollAction
          cases hPollAction
        · exact (MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hPath
            ⟨k, j, r, poll, hk, hId, hPoll, hPollId, hGt⟩).elim
      obtain ⟨st, _, hs, _, _, _⟩ := hChecked.okPoll hPoll hSuccess
      have hj := (List.getElem?_eq_some_iff.mp hPoll).1.le
      obtain ⟨hExpected, hTx⟩ := hState j st hj hs
      have hPending := stateBefore_pending_pos hChecked hs hTx
      obtain ⟨_, hCount⟩ := (hChecked.accounted hNo hj).2 st hs
      change unitsBefore log j + st.pending =
        st.expected * (st.phase + 1) + incrementsBefore log j at hCount
      have hIncr := incrementsBefore_eq_zero log (incrementsBefore_length_of log hNoIncr) j
      have hAccount : unitsBefore log j + st.pending = 128 * (st.phase + 1) := by
        simpa only [hExpected, hIncr, Nat.add_zero] using hCount
      have hEnough : 128 * n ≤ unitsBefore log j := hOrdinal ▸ hUnits
      rw [hId]
      change ∃ j poll st, j < k ∧ log[j]? = some poll ∧ poll.reply.waited = some true ∧
        stateBefore log j = some st ∧ n ≤ st.phase
      exact ⟨j, poll, st, hBefore, hPoll, hSuccess, hs, by omega⟩)
    (incrementsBefore_length_of log hNoIncr)
  exact hGated k r c tx hRecord hArrival

/-- All actual credits belong to their producer's acquired phase, even in prefixes that end
before the matching phase fills. -/
theorem creditHistoryClean {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDeps : CreditAcquireDependencies l X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (statsCreditLoc l cta stage)) : r.fault = none := by
  have hInit := statsCreditHistoryInit hp hX stage hr
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX)
    (statsCreditLoc l cta stage)
  cases statsCreditHistorySource hp hX stage hr with
  | init ha => exact PairTmaRing.init_clean hInit hr ha
  | poll ha => exact PairTmaRing.poll_clean hX hInit hNo r hr ⟨_, _, ha⟩
  | credit _ _ _ _ _ _ _ ha =>
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    exact (creditArrivalPhase hp hX hDeps stage hk ha).1

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
