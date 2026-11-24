-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduler
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWarpZero

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue

private theorem firstScheduleAfterRoleEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos j : Nat} {warp : Fin 8} {t : TState} {o : Option TState}
    {target : Event} (he : X.get (g,j) = some target) (hPc : 3103 < target.pc)
    (hPos : pos ≤ j) (ht : At t 3101 (dispatchOutput p l g warp))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) :
    ∃ u inst, X.get (g,pos) = some ⟨3102, .setMaxReg true 184 inst⟩ ∧
      X.get (g,pos+1) = some ⟨3103, .bar 2 (some 416) .sync⟩ ∧
      At u 3104 (schedulerEntry p l g warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+2)) o ∧ pos+2 ≤ j := by
  have nonempty {n : Nat} (hn : n ≤ j) : (X.tr g).drop n ≠ [] := by
    intro h
    exact (Nat.not_le_of_lt ((List.getElem?_eq_some_iff.mp he).1))
      ((List.drop_eq_nil_iff.mp h).trans hn)
  have later {n : Nat} {e : Event} (hn : n ≤ j) (hGet : X.get (g,n) = some e)
      (hSite : e.pc ≤ 3103) : n < j := by
    apply Nat.lt_of_le_of_ne hn
    rintro rfl
    rw [hGet] at he
    obtain rfl := Option.some.inj he
    omega
  obtain ⟨s, hs, hAt⟩ := batchRun hp g warp t ht
  have hHint : Next kernel Assumptions.all l g t s (.setMaxReg true 184 (next s)) :=
    ⟨run_rtg hs, firstHint hAt⟩
  obtain ⟨_, _, hSet, ⟨inst, rfl, hState⟩, hTail⟩ := hHint.continuing_at_nonempty (by
    rintro e ⟨_, _, hBad⟩
    cases hBad) hr (nonempty hPos)
  obtain rfl := Option.some.inj hState
  rw [hAt.1] at hSet
  have hNext : pos+1 ≤ j := later hPos hSet (by change 3102 ≤ 3103; decide)
  have hb : Next kernel Assumptions.all l g (next s) (next s)
      (.bar 2 (next (next s)) (some 416) .sync) := ⟨.refl, entryBarrier hp.block hAt.next⟩
  obtain ⟨_, _, hSync, ⟨rfl, hLast⟩, hRest⟩ := hb.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hTail (nonempty hNext)
  obtain rfl := Option.some.inj hLast
  rw [hAt.next.1] at hSync
  exact ⟨_, inst, hSet, hSync, hAt.next.next, hRest, later hNext hSync (by decide)⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {target : Event}
    (he : X.get (g,j) = some target)
include hp hX he

private theorem nonzeroDispatchCollectives (hPc : 173 < target.pc) (hPos : 0 < warpIndex l g) :
    beforeFirstScan X g 5 := by
  have hg := event_thread_lt hX he
  obtain ⟨hJ, hBar, _⟩ := nonzeroStartupBar hp hX hg hPos he hPc
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hStart : 3 ≤ (X.tr g).length := by omega
  obtain ⟨_, _, _, heq⟩ := broadcastTraceSplit hStart
  obtain ⟨t, o, ht, hf, hs, hw, _, _, _, hr⟩ := broadcastPrefix hp hX g hg heq
  obtain ⟨s, hRun, hsPc, hsF, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    nonzeroWarpWith (A := Assumptions.all) hp g (warpIndex l g) t hPos
      (warpIndex_lt hp g) ht hf hw hs
  have hOut : out kernel [] l g s = .ev (.fenceMbarInit (next s)) := by
    unfold out
    rw [hsPc, hsF, Flow.code_172]
    rfl
  have hNext : Next kernel Assumptions.all l g t s (.fenceMbarInit (next s)) :=
    ⟨run_rtg hRun, startupOut (.inl (by rw [hsPc]; decide)) hOut⟩
  have hNonempty : (X.tr g).drop 3 ≠ [] := by
    intro h
    have h := List.drop_eq_nil_iff.mp h
    omega
  obtain ⟨_, _, hFence, ⟨rfl, _⟩, _⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hr hNonempty
  exact beforeFirstScan_advance
    (beforeFirstScan_advance (beforeFirstScan_three hp hX hg hStart) hFence rfl rfl) hBar rfl rfl

/-- An observed nonzero softmax lane reaches the scheduler with its actual CTA and ABI
registers. The trace can end at any scheduler event or later. -/
theorem nonzeroSchedulerEntryAfterBarrier (hPc : 3103 < target.pc) (hPos : 0 < warpIndex l g)
    (hWarp : warpIndex l g < 8) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    ∃ u o inst, X.get (g,5) = some ⟨3102, .setMaxReg true 184 inst⟩ ∧
      X.get (g,6) = some ⟨3103, .bar 2 (some 416) .sync⟩ ∧
      At u 3104 (schedulerEntry p l g warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop 7) o ∧ 7 ≤ j ∧
      beforeFirstScan X g 7 := by
  dsimp only
  have hg := event_thread_lt hX he
  obtain ⟨_, _, hIndex, _, _⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hPos he (by omega)
  have hj := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨t, o, ht, hr⟩ := nonzeroRoleEntryPrefix hp hX hg hPos (by omega)
  have hRole : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 3101 := by
    unfold dispatchParamPc
    simp [hWarp, show ¬ 14 ≤ warpIndex l g by omega, show warpIndex l g ≠ 13 by omega,
      show warpIndex l g ≠ 12 by omega]
  rw [hRole] at ht
  have ht' : At t 3101 (dispatchOutput p l g ⟨warpIndex l g, hWarp⟩) := by
    apply ht.mono
    simp only [dispatchOutput, dispatchInput]
    refine ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ?_, ?_, ?_, trivial⟩
    all_goals exact holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts])
  obtain ⟨u, inst, hSet, hSync, hu, hSuffix, hJ⟩ :=
    firstScheduleAfterRoleEntry hp he hPc hIndex ht' hr
  have hBefore := nonzeroDispatchCollectives hp hX he (by omega) hPos
  exact ⟨u, o, inst, hSet, hSync, hu, hSuffix, hJ,
    beforeFirstScan_advance (beforeFirstScan_advance hBefore hSet rfl rfl) hSync rfl rfl⟩

/-- An observed nonzero softmax lane has supplied its scheduler ABI arguments. -/
theorem nonzeroSchedulerEntryOfEvent (hPc : 3110 < target.pc) (hPos : 0 < warpIndex l g)
    (hWarp : warpIndex l g < 8) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    ∃ u o inst, X.get (g,5) = some ⟨3102, .setMaxReg true 184 inst⟩ ∧
      X.get (g,6) = some ⟨3103, .bar 2 (some 416) .sync⟩ ∧
      At u 3104 (schedulerEntry p l g warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop 7) o ∧ 7 ≤ j ∧
      beforeFirstScan X g 7 :=
  nonzeroSchedulerEntryAfterBarrier hp hX he (by omega) hPos hWarp

omit hp hX he in
private theorem firstOperandForObservedScheduler {p : Params} {l : Launch} {m : Mem0}
    {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g entry j : Nat} {target : Event} {warp : Fin 8} {t : TState} {o : Option TState}
    (he : X.get (g,j) = some target) (hPc : 3110 < target.pc)
    (ht : At t 3104 (schedulerEntry p l g warp)) (hIndex : entry ≤ j)
    (hBefore : beforeFirstScan X g entry)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop entry) o)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((laneCuQAcc p l g).loc.at k)) :
    let q := if laneOf l g ≤ p.batch then p.qOffset (laneOf l g) else 0
    let pos := if laneOf l g ≤ p.batch then entry+1 else entry
    ∃ u, At u 3111 (schedulerLane p l g warp q) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) o ∧ pos ≤ j ∧
      beforeFirstScan X g pos := by
  dsimp only
  have hNonempty : (X.tr g).drop entry ≠ [] := by
    intro h
    exact (Nat.not_le_of_lt ((List.getElem?_eq_some_iff.mp he).1))
      ((List.drop_eq_nil_iff.mp h).trans hIndex)
  obtain ⟨u, hu, hRead, hRun⟩ := schedulerFirstOperandPrefix hp hX ht hr hNonempty hProtected
  by_cases hLane : laneOf l g ≤ p.batch
  · simp only [ite_eq_left hLane] at hu hRun ⊢
    refine ⟨u, hu, hRun, ?_, beforeFirstScan_advance hBefore (hRead hLane) rfl rfl⟩
    by_contra! hj
    have hSame : j = entry := by omega
    subst entry
    rw [hRead hLane] at he
    cases Option.some.inj he
    exact (by decide : ¬ 3110 < 3110) hPc
  · simp only [ite_eq_right hLane] at hu hRun ⊢
    exact ⟨u, hu, hRun, hIndex, hBefore⟩

/-- A real nonzero softmax prefix has supplied its protected cuQ word by the first shuffle.
The cursor counts the optional input read at the decoded lane gate. -/
theorem nonzeroFirstSchedulerOperandOfEvent (hPc : 3110 < target.pc) (hPos : 0 < warpIndex l g)
    (hWarp : warpIndex l g < 8)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((laneCuQAcc p l g).loc.at k)) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    let q := if laneOf l g ≤ p.batch then p.qOffset (laneOf l g) else 0
    let pos := if laneOf l g ≤ p.batch then 8 else 7
    ∃ u o, At u 3111 (schedulerLane p l g warp q) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) o ∧ pos ≤ j ∧
      beforeFirstScan X g pos := by
  dsimp only
  obtain ⟨t, o, _, _, _, ht, hr, hIndex, hBefore⟩ :=
    nonzeroSchedulerEntryOfEvent hp hX he hPc hPos hWarp
  obtain ⟨u, hu, hRun, hj, hCount⟩ :=
    firstOperandForObservedScheduler hp hX he hPc ht hIndex hBefore hr hProtected
  exact ⟨u, o, hu, hRun, hj, hCount⟩

/-- An observed warp-zero prefix reaches the scheduler with the real ABI register frame
after the variable-length initializer path. -/
theorem zeroSchedulerEntryAfterBarrier (hPc : 3103 < target.pc) (hZero : warpIndex l g = 0) :
    ∃ pos u o, pos ≤ j ∧ beforeFirstScan X g pos ∧ At u 3104 (schedulerEntry p l g 0) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) o := by
  obtain ⟨n, t, o, hn, hBefore, ht, hr⟩ := zeroDispatchOfEvent hp hX he (by omega) hZero
  obtain ⟨u, _, hSet, hSync, hu, hRest, hJ⟩ := firstScheduleAfterRoleEntry hp he hPc hn ht hr
  exact ⟨n+2, u, o, hJ, beforeFirstScan_advance
    (beforeFirstScan_advance hBefore hSet rfl rfl) hSync rfl rfl, hu, hRest⟩

/-- An observed warp-zero lane has supplied its scheduler ABI arguments. -/
theorem zeroSchedulerEntryOfEvent (hPc : 3110 < target.pc) (hZero : warpIndex l g = 0) :
    ∃ pos u o, pos ≤ j ∧ beforeFirstScan X g pos ∧ At u 3104 (schedulerEntry p l g 0) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) o :=
  zeroSchedulerEntryAfterBarrier hp hX he (by omega) hZero

/-- Every observed softmax warp supplies its first protected cuQ shuffle operand, including
warp zero after its physical initializer events. -/
theorem firstSchedulerOperandOfEvent (hPc : 3110 < target.pc) (hWarp : warpIndex l g < 8)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((laneCuQAcc p l g).loc.at k)) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    let q := if laneOf l g ≤ p.batch then p.qOffset (laneOf l g) else 0
    ∃ pos u o, pos ≤ j ∧ beforeFirstScan X g pos ∧ At u 3111 (schedulerLane p l g warp q) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) o := by
  dsimp only
  rcases Nat.eq_zero_or_pos (warpIndex l g) with hz | hn
  · obtain ⟨entry, t, o, hJ, hBefore, ht, hRun⟩ := zeroSchedulerEntryOfEvent hp hX he hPc hz
    obtain ⟨u, hu, hRest, hBound, hCount⟩ :=
      firstOperandForObservedScheduler hp hX he hPc ht hJ hBefore hRun hProtected
    have hW : (0 : Fin 8) = ⟨warpIndex l g, hWarp⟩ := Fin.ext hz.symm
    exact ⟨_, u, o, hBound, hCount, hW ▸ hu, hRest⟩
  · obtain ⟨u, o, hu, hRun, hBound, hCount⟩ :=
      nonzeroFirstSchedulerOperandOfEvent hp hX he hPc hn hWarp hProtected
    exact ⟨_, u, o, hBound, hCount, hu, hRun⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
