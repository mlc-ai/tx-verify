-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityTailCredit
import Kernels.TmlFa4Fwd.Proof.Thread.InitialProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarPending

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Scores

/-- A full set of distinct, clean unit credits completes at least the opening phase. -/
theorem probabilityAdvancedOfCredits {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage packet : Fin 2)
    (credits : Fin (probabilityCredits packet) → EvId) (hDistinct : Function.Injective credits)
    (hCredit : ∀ w, ProbabilityCredit l X (credits w) cta stage packet)
    (hClean : ∀ r ∈ X.objects (probabilityObject l cta stage packet), r.fault = none) :
    let log := X.objects (probabilityObject l cta stage packet)
    ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  classical
  let n := probabilityCredits packet
  let addr := probabilityObject l cta stage packet
  have hn : 0 < n := by fin_cases packet <;> decide
  let first : Fin n := ⟨0,hn⟩
  let log := X.objects addr
  have hShape (r : Record Ref) (hr : r ∈ log) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 := (probabilityUpdate hp hX stage packet hr hu).elim fun _ h => h.2.2.2
  have hRecord (w : Fin n) : ∃ r ∈ log, r.id = .thread (credits w) ∧ r.action = .arrive 1 0 := by
    obtain ⟨_,r,he,hId,hUpdate⟩ := probabilityCreditRecord hX (hCredit w)
    have hr := List.mem_of_getElem? he
    exact ⟨r,hr,hId,hShape r hr hUpdate⟩
  choose record hMem hId hAct using hRecord
  let rows := log.filter countedArrive
  have hUnits : n ≤ arrivalUnits log := by
    rw [arrivalUnits_eq_length]
    · let members := rows.toFinset
      have hIn (w : Fin n) : record w ∈ members := by
        exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hMem w,countedArrive_iff.mpr
          ⟨hClean _ (hMem w),1,0,hAct w⟩⟩)
      let target (w : Fin n) : {r // r ∈ members} := ⟨record w,hIn w⟩
      have hInj : Function.Injective target := by
        intro a b hab
        have he := congrArg (fun r => Record.id r.val) hab
        change (record a).id = (record b).id at he
        rw [hId,hId] at he
        exact hDistinct (Ref.thread.inj he)
      have hCard := Fintype.card_le_of_injective target hInj
      simp only [Fintype.card_fin,Fintype.card_coe] at hCard
      exact hCard.trans (List.toFinset_card_le rows)
    · intro r hr c tx _ ha
      have hu : CounterUpdate r.action := by rw [ha]; trivial
      exact (Action.arrive.inj (ha.symm.trans (hShape r hr hu))).1
  have hInitial := probabilityInitialized hp hX stage packet (hMem first)
  obtain ⟨init,hInit,hAction,hClean,_⟩ := hInitial (record first) (hMem first)
  have hChecked := X.objects_checked hX addr
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) addr
  have hLen : 0 < log.length := (List.getElem?_eq_some_iff.mp hInit).1
  obtain ⟨s,hState,hExpected⟩ := ObjectInit.checked_expected_after_init hChecked hNo
    hInit hAction hClean hLen (Nat.le_refl _)
  change s.expected = n at hExpected
  refine ⟨s,hState,?_⟩
  have hZeroIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr ha
    have hu : CounterUpdate r.action := by rw [ha]; trivial
    have h := hShape r hr hu
    rw [ha] at h
    cases h
  have hBefore := ((hChecked.accounted hNo (Nat.le_refl _)).2 s hState).2
  change arrivalUnits (log.take log.length) + s.pending =
    s.expected*(s.phase+1) + incrementsBefore log log.length at hBefore
  rw [List.take_length,hExpected,hZeroIncr] at hBefore
  have hNoTx : s.tx = 0 := by
    apply MbarRing.tx_zero_of hX hNo _ _ (Nat.le_refl _) hState
    · intro r hr n tx ha
      have hu : CounterUpdate r.action := by rw [ha]; trivial
      exact (Action.arrive.inj (ha.symm.trans (hShape r hr hu))).2
    · intro r hr n ha
      have hu : CounterUpdate r.action := by rw [ha]; trivial
      have h := hShape r hr hu
      rw [ha] at h
      cases h
  have hpending := stateBefore_pending_pos hChecked hState hNoTx
  by_contra! hs
  have hzero : s.phase = 0 := by omega
  rw [hzero] at hBefore
  omega

/-- Four distinct tail-probability credits complete at least the opening phase. -/
theorem tailProbabilityAdvancedOfCredits {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) (credits : Fin 4 → EvId) (hDistinct : Function.Injective credits)
    (hCredit : ∀ w, ProbabilityCredit l X (credits w) cta stage 1) :
    let log := X.objects (probabilityObject l cta stage 1)
    ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase :=
  probabilityAdvancedOfCredits hp hX stage 1 credits hDistinct hCredit
    (fun _ => tailProbabilityHistoryNoFault hp hX stage)

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
