-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyHistory
public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
public import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.MBarrier PTX.MbarRing PTX.AsyncCopy Prologue

noncomputable section

def namesReady (loc : Loc) (e : Event) : Bool :=
  match e.kind with
  | .asyncArrive target true => decide (target = loc)
  | _ => false

/-- The producer's ordinal for a slot is the number of its own earlier
no-increment arrivals on that slot, measured in its actual thread trace. -/
def readyOrdinal (X : Execution) (loc : Loc) (i : EvId) : Nat :=
  ((X.tr i.1).take i.2).countP (namesReady loc)

def readyProducer (l : Launch) (cta : Nat) (lane : Fin 64) : Nat :=
  cta * l.block + 448 + lane.val

theorem readyArrivalProducer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 3) {i : EvId} {pc : Nat}
    (h : X.get i = some ⟨pc, .asyncArrive (initObject l cta (readySlot stage)) true⟩) :
    ∃ lane : Fin 64, i.1 = readyProducer l cta lane := by
  obtain ⟨⟨site, hSite⟩, _, _, hOwner⟩ := actualAsyncArrival hX h
  have hRange : 674 ≤ pc ∧ pc ≤ 1735 := by
    rw [hSite]
    fin_cases site <;> decide
  have hHint : pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hl : 14 ≤ warpIndex l i.1 := by
    have hLate : 173 < pc := by omega
    have hBody : roleBodyPc (warpIndex l i.1) pc := roleBodyPcOfEvent hp hX h hLate hHint
    unfold roleBodyPc at hBody
    rcases hBody with hc | hc
    · omega
    · split_ifs at hc <;> omega
  have hTid : i.1 % l.block < 512 := by rw [hp.block]; omega
  have hTidLo : 448 ≤ i.1 % l.block := by unfold warpIndex at hl; omega
  let lane : Fin 64 := ⟨i.1 % l.block - 448, by omega⟩
  have hDiv : i.1 / l.block = cta := hOwner.symm
  have hSplit := Nat.mod_add_div i.1 l.block
  rw [Nat.mul_comm l.block (i.1 / l.block), hDiv] at hSplit
  exact ⟨lane, by dsimp [readyProducer, lane]; omega⟩

private theorem readyOrdinalStep {X : Execution} {loc : Loc} {g i pc : Nat}
    (h : X.get (g, i) = some ⟨pc, .asyncArrive loc true⟩) :
    readyOrdinal X loc (g, i + 1) = readyOrdinal X loc (g, i) + 1 := by
  change (X.tr g)[i]? = _ at h
  simp only [readyOrdinal, List.take_add_one, h, Option.toList_some,
    List.countP_append, namesReady, List.countP_cons, List.countP_nil, decide_true,
    ↓reduceIte, Nat.zero_add]

/-- Two actual arrivals by one producer on a slot cannot have the same ordinal. -/
theorem readyOrdinalUnique {X : Execution} {loc : Loc} {g i j pc qc : Nat}
    (hi : X.get (g, i) = some ⟨pc, .asyncArrive loc true⟩)
    (hj : X.get (g, j) = some ⟨qc, .asyncArrive loc true⟩)
    (hn : readyOrdinal X loc (g, i) = readyOrdinal X loc (g, j)) : i = j := by
  have mono {a b : Nat} (h : a ≤ b) :
      readyOrdinal X loc (g, a) ≤ readyOrdinal X loc (g, b) :=
    (List.take_sublist_take_left h).countP_le
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hle := mono (Nat.succ_le_of_lt h)
    rw [readyOrdinalStep hi] at hle
    omega
  · have hle := mono (Nat.succ_le_of_lt h)
    rw [readyOrdinalStep hj] at hle
    omega

open Classical in
/-- The event at a given ordinal in a producer's actual arrivals to this ready slot. -/
def readyIssue (X : Execution) (loc : Loc) (g n : Nat) : EvId :=
  (g, if h : ∃ i pc, X.get (g, i) = some ⟨pc, .asyncArrive loc true⟩ ∧
      readyOrdinal X loc (g, i) = n then Classical.choose h else (X.tr g).length)

theorem readyIssueOfActual {X : Execution} {loc : Loc} {g i pc : Nat}
    (h : X.get (g, i) = some ⟨pc, .asyncArrive loc true⟩) :
    readyIssue X loc g (readyOrdinal X loc (g, i)) = (g, i) := by
  classical
  unfold readyIssue
  let present : ∃ j pc, X.get (g, j) = some ⟨pc, .asyncArrive loc true⟩ ∧
      readyOrdinal X loc (g, j) = readyOrdinal X loc (g, i) := ⟨i, pc, h, rfl⟩
  rw [dite_eq_left present]
  obtain ⟨pos, hp, ho⟩ := Classical.choose_spec present
  rw [readyOrdinalUnique hp h ho]

/-- When the ordinal resolves to a recorded event, that event has the requested count. -/
theorem ordinalOfReadyIssue {X : Execution} {loc : Loc} {g n : Nat} {e : Event}
    (h : X.get (readyIssue X loc g n) = some e) :
    readyOrdinal X loc (readyIssue X loc g n) = n := by
  classical
  unfold readyIssue at h ⊢
  split at h
  · rename_i existsIssue
    rw [dite_eq_left existsIssue]
    exact (Classical.choose_spec existsIssue).choose_spec.2
  · change (X.tr g)[(X.tr g).length]? = some e at h
    simp at h

set_option maxRecDepth 4000 in
/-- When later-use items are causally excluded from a ready poll's history prefix, each
remaining lane contributes at most one unit per earlier use or the poll's own use. -/
theorem readyUnitsBefore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j use : Nat} (stage : Fin 3)
    (hObj : NoIncObject X (initObject l cta (readySlot stage)) 64)
    (hEarlier : let loc := initObject l cta (readySlot stage)
      ∀ k < j, ∀ (r : Record Ref) issue, (X.objects loc)[k]? = some r →
        r.fault = none → r.action = .arrive 1 0 → r.id = .async issue .arriveOn →
        readyOrdinal X loc issue ≤ use) :
    unitsBefore (X.objects (initObject l cta (readySlot stage))) j ≤ 64 * (use + 1) := by
  classical
  let loc := initObject l cta (readySlot stage)
  let upd : Fin 64 × Nat → Ref := fun (lane, n) =>
    .async (readyIssue X loc (readyProducer l cta lane) n) .arriveOn
  let S := (Finset.univ : Finset (Fin 64)) ×ˢ Finset.range (use + 1)
  have hCount := Round.units_le_of_uses (X.objects_checked hX loc) upd S (i := j)
    (fun _ _ _ _ hGet _ ha => (hObj.arrive_source hGet ha).1)
    (fun k hk r count tx hGet hClean ha => by
      obtain ⟨rfl, rfl, issue, hId, ⟨pc, he⟩, _⟩ := hObj.arrive_source hGet ha
      obtain ⟨lane, hlane⟩ := readyArrivalProducer hp hX stage he
      have hUse := hEarlier k hk r issue hGet hClean ha hId
      have hMem : (lane, readyOrdinal X loc issue) ∈ S := by
        change (lane, readyOrdinal X loc issue) ∈
          (Finset.univ : Finset (Fin 64)) ×ˢ Finset.range (use + 1)
        rw [Finset.mem_product, Finset.mem_range]
        exact ⟨Finset.mem_univ _, Nat.lt_succ_of_le hUse⟩
      refine ⟨(lane, readyOrdinal X loc issue), hMem, ?_⟩
      have hActual : readyIssue X loc issue.1 (readyOrdinal X loc issue) = issue := by
        cases issue
        exact readyIssueOfActual he
      change r.id = .async (readyIssue X loc (readyProducer l cta lane)
        (readyOrdinal X loc issue)) .arriveOn
      rw [← hlane, hActual]
      exact hId)
  simpa [S] using hCount

/-- The causal reuse gate bounds the arrivals before a selected acquire. Its nonwrapping
phase is therefore the ordinal of that consumer's successful poll. -/
theorem readyPhaseOfCausalReuse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j : Nat} (stage : Fin 3) {wait : EvId} {poll : Record Ref} (selected : Ref → Bool)
    (hObj : NoIncObject X (initObject l cta (readySlot stage)) 64)
    (hRecord : (X.objects (initObject l cta (readySlot stage)))[j]? = some poll)
    (hPollId : poll.id = .thread wait) (hSuccess : poll.reply.waited = some true)
    (hSelected : selected poll.id = true)
    (hAlternates : SelectedAlternates selected (X.objects (initObject l cta (readySlot stage))) 0)
    (hReuse : let loc := initObject l cta (readySlot stage)
      ∀ (issue : EvId), X.AsyncArrive issue loc true → X.async.arrived issue = true →
        selectedBefore selected (X.objects loc) j < readyOrdinal X loc issue →
        Relation.TransGen (DepStep l kernel X) (.thread wait, true)
          (.async issue .arriveOn, false)) :
    let log := X.objects (initObject l cta (readySlot stage))
    observedAt log j = some (selectedBefore selected log j) := by
  dsimp only
  let loc := initObject l cta (readySlot stage)
  let use := selectedBefore selected (X.objects loc) j
  have hu : unitsBefore (X.objects loc) j ≤ 64 * (use + 1) :=
    readyUnitsBefore hp hX stage hObj (use := use) (fun k hk r issue hGet _ hAct hId => by
      by_contra! hLate
      obtain ⟨_, _, a, hRef, hArrive, hDone⟩ := hObj.arrive_source hGet hAct
      have hSame : a = issue := (Ref.async.inj (hRef.symm.trans hId)).1
      subst a
      exact Round.Slot.not_before_of_reach hX (hReuse issue hArrive hDone hLate)
        ⟨k, j, r, poll, hGet, hId, hRecord, hPollId, hk⟩)
  exact readyAcquireExactPhase hX hObj selected hAlternates hRecord hSelected hSuccess
    (lt_of_le_of_lt hu (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self (use + 1)) (by decide)))

end
end PTX.Kernels.TmlFa4Fwd.Loader
