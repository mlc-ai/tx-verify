-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputFree
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.SingleUnitUpdate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Output

/-- The other 31 lanes can each have contributed at most one credit before this lane. -/
private theorem unitsBeforeFreeCredit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {i : Nat} {r : Record Ref}
    (hi : (X.objects (freeObject l cta stage))[i]? = some r)
    (hUpdate : CounterUpdate r.action) :
    unitsBefore (X.objects (freeObject l cta stage)) i < 32 := by
  classical
  let log := X.objects (freeObject l cta stage)
  have hChecked := X.objects_checked hX (freeObject l cta stage)
  obtain ⟨lane, pos, hId, hCredit, _⟩ := freeUpdate hp hX stage (List.mem_of_getElem? hi) hUpdate
  let selected (q : Record Ref) := decide (q.action = .arrive 1 0)
  let position (k : Fin 32) : Nat :=
    if h : ∃ j, FreeCredit l X cta stage (outputLane l cta k, j) then Classical.choose h else 0
  let other := (Finset.univ.erase lane).image (fun k => Ref.thread (outputLane l cta k, position k))
  have hBound : other.card ≤ 31 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ lane), Finset.card_univ, Fintype.card_fin]
  change unitsBefore log i < 32
  suffices hUnits : unitsBefore log i ≤ other.card by omega
  apply (arrivalUnits_le_countP selected ?_).trans
  · apply countP_take_le_card hChecked.1 selected other
    intro k hk q hq hSelect
    have hqUpdate : CounterUpdate q.action := by
      rw [show q.action = .arrive 1 0 from of_decide_eq_true hSelect]
      trivial
    obtain ⟨otherLane, j, hOtherId, hOtherCredit, _⟩ :=
      freeUpdate hp hX stage (List.mem_of_getElem? hq) hqUpdate
    have hDifferent : otherLane ≠ lane := by
      intro h
      subst otherLane
      have hPos := hOtherCredit.indexUnique hp hX hCredit
      have hSame : q.id = r.id := by rw [hOtherId, hId, hPos]
      exact (Nat.ne_of_lt hk) (ObjectInit.checked_record_index_eq hChecked hq hi hSame)
    have hEx : ∃ j, FreeCredit l X cta stage (outputLane l cta otherLane, j) :=
      ⟨j, hOtherCredit⟩
    have hPosition : j = position otherLane := by
      simpa only [position, dite_eq_left hEx] using
        hOtherCredit.indexUnique hp hX (Classical.choose_spec hEx)
    rw [hOtherId, hPosition]
    exact Finset.mem_image.mpr
      ⟨otherLane, Finset.mem_erase.mpr ⟨hDifferent, Finset.mem_univ _⟩, rfl⟩
  · intro q hq _ count tx ha
    obtain ⟨_, _, _, _, h⟩ := freeUpdate hp hX stage (List.mem_of_mem_take hq) (by rw [ha]; trivial)
    exact ⟨(Action.arrive.inj (ha.symm.trans h)).1, decide_eq_true h⟩

/-- The two output-free histories accept the epilogue's unit credits and all actual polls. -/
theorem outputFreeHistoryClean {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (freeObject l cta stage)) : r.fault = none := by
  let loc := freeObject l cta stage
  let log := X.objects loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hUpdate (ha : CounterUpdate r.action) : r.fault = none := by
    have hShape {q : Record Ref} (hq : q ∈ log) (h : CounterUpdate q.action) :
        q.action = .arrive 1 0 := by
      obtain ⟨_, _, _, _, hAct⟩ := freeUpdate hp hX stage hq h
      exact hAct
    have hInit := freeInitialized hp hX stage hr
    have hChecked := X.objects_checked hX loc
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_, _, hState, _⟩ := PairTmaRing.state_of_init hX hInit hNo hi
      (by intro n; rw [hShape hr ha]; simp)
    apply hChecked.zeroTxUpdateCleanOfUnits hNo hShape hi hState _ ha
    intro before hs
    rw [PairTmaRing.expected_of_init hX hInit hNo hs]
    exact unitsBeforeFreeCredit hp hX stage hi ha
  cases ha : r.action with
  | init count => exact actualInitOrPollClean hp hX hr (.inl ⟨count, ha⟩)
  | pollParity parity ok => exact actualInitOrPollClean hp hX hr (.inr ⟨parity, ok, ha⟩)
  | inval => exact (hNo r hr ha).elim
  | arrive | completeTx | increment => exact hUpdate (by rw [ha]; trivial)

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
