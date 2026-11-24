-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.AllocationBarrierControl
public import Kernels.TmlFa4Fwd.Proof.PrologueGenerationZero
public import Kernels.TmlFa4Fwd.Proof.MmaStartup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

private theorem nonemptyAt {X : Execution} {g j : Nat}
    (h : j < (X.tr g).length) : (X.tr g).drop j ≠ [] :=
  fun he => (Nat.not_le_of_lt h) (List.drop_eq_nil_iff.mp he)

private theorem laterThanKnown {X : Execution} {g j k : Nat} {e q : Event}
    (hj : X.get (g,j) = some e) (hk : X.get (g,k) = some q)
    (hle : j ≤ k) (hne : e ≠ q) : j < k := by
  rcases Nat.eq_or_lt_of_le hle with rfl | h
  · exact (hne (Option.some.inj (hj.symm.trans hk))).elim
  · exact h

private theorem advanceAllocationBar {l : Launch} {X : Execution} {g j : Nat} {s : TState}
    {o : Option TState} (hb : l.block = 512) (hPc : s.pc ∈ allocationEntrySites)
    (hf : s.fault = none) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop j) o)
    (hLen : j < (X.tr g).length) :
    X.IsBarrier (g,j) 2 (some 416) s.pc ∧
      Run kernel Assumptions.all l g (next s) ((X.tr g).drop (j+1)) o := by
  have hNext : Next kernel Assumptions.all l g s s (.bar 2 (next s) (some 416) .sync) :=
    ⟨.refl, allocationEntryTemplate hb hPc hf⟩
  obtain ⟨_, _, he, ⟨rfl, hu⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro _ ⟨_, h⟩
    cases h) hr (nonemptyAt hLen)
  obtain rfl := Option.some.inj hu
  exact ⟨he, hTail⟩

private theorem firstSite (w : Fin 16) (h : w.val < 12) :
    registerHintPc w+1 = if w.val < 8 then 3103 else 7747 := by
  simp only [registerHintPc, dispatchParamPc]
  split_ifs <;> omega

private theorem exactAllocatorPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g n j : Nat} {u : TState} {o : Option TState}
    (hu : At u 1908 [(1062,b32 12), (2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g u ((X.tr g).drop n) o)
    {e : Event} (he : X.get (g,j) = some e) (hIndex : n ≤ j)
    (hDemand : e.kind = .exit ∨ e.pc = 1910 ∨ e.pc = 1911) :
    ∃ k ≤ j, X.IsBarrier (g,k) 2 (some 416) 1910 ∧
      X.get (g,n) = some ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩ ∧
      (laneOf l g = 0 → ∃ col < 2^16, n+1 < k ∧
        X.get (g,n+1) =
          some ⟨1909, .wr {loc := allocationSlot l g, size := 4} (b32 col).toBytes⟩) := by
  let t := next (setReg u 2451 (b32 512))
  have hStep : run kernel [] l g 1 u = some t := by
    exact run_local Flow.code_1908 rfl hu rfl
  have ht := hu.set (v := b32 512) (r := 2451) (by
    intro pair hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp)
  change At t 1909 _ at ht
  have hLoc := schedulerLocalTransport (A := Assumptions.all) (lo := 1908) (len := 1)
    rfl (fun hlo hhi => startupOut_eq_nil (by omega) (by omega)) hStep
    (by rw [hu.1]) (by rw [hu.1])
  let eAlloc : Event := ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩
  have hBase : t.regs 2535 = some (b32 l.sharedBase) := ht.2.2.2.2.2.2.1
  have hCols : t.regs 2451 = some (b32 512) := ht.2.2.2.2.1
  let after := if laneOf l g = 0 then {t with sub := 1} else next t
  have hAlloc : Next kernel Assumptions.all l g u t
      (.tc (.resource .one (some (allocationSlot l g)) (.alloc 512)) after) := by
    refine ⟨run_rtg hLoc, ?_⟩
    rw [allocationTemplate hp ht.1 ht.2.2.2.1 hBase hCols, ht.2.1]
    rfl
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨_, _, hGet, ⟨rfl, hAfter⟩, hRest⟩ := hAlloc.continuing_at_nonempty (by
    rintro _ ⟨_, h⟩
    cases h) hr (nonemptyAt (lt_of_le_of_lt hIndex hLen))
  obtain rfl := Option.some.inj hAfter
  have hFirst : X.get (g,n) = some eAlloc := by simpa only [ht.1, eAlloc] using hGet
  have hLt := laterThanKnown hFirst he hIndex (fun h => by
    subst e
    rcases hDemand with h | h | h <;> cases h)
  have hBar : (next t).pc ∈ allocationEntrySites := by rw [ht.next.1]; decide
  by_cases hLane : laneOf l g = 0
  · obtain ⟨col, hCol, hStore, hTail⟩ :=
      allocationStorePrefix hp hLane ht hBase hCols hRest (nonemptyAt (by omega))
    have hStoreLt := laterThanKnown hStore he (by omega) (fun h => by
      subst e
      rcases hDemand with h | h | h <;> cases h)
    obtain ⟨hSeen, _⟩ := advanceAllocationBar hp.block hBar ht.2.2.2.1 hTail (by omega)
    have hAt : X.IsBarrier (g,n+2) 2 (some 416) 1910 := by simpa only [ht.next.1] using hSeen
    exact ⟨n+2, by omega, hAt, hFirst, fun _ => ⟨col, hCol, by omega, hStore⟩⟩
  · have hTail : Run kernel Assumptions.all l g (next t) ((X.tr g).drop (n+1)) o := by
      simpa only [after, hLane, ↓reduceIte] using hRest
    obtain ⟨hSeen, _⟩ := advanceAllocationBar hp.block hBar ht.2.2.2.1 hTail (by omega)
    have hAt : X.IsBarrier (g,n+1) 2 (some 416) 1910 := by simpa only [ht.next.1] using hSeen
    exact ⟨n+1, by omega, hAt, hFirst, fun h => (hLane h).elim⟩

/-- An observed warp-12 rendezvous, allocation read or exit proves the allocation has issued
and lane zero has stored the shared address before the warp's first rendezvous. -/
theorem allocationPrefixAtBarrierReadOrExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {e : Event} (he : X.get (g,j) = some e) (hDemand : e.kind = .exit ∨ e.pc = 1910 ∨ e.pc = 1911) :
    ∃ n k, k ≤ j ∧ X.IsBarrier (g,k) 2 (some 416) 1910 ∧
      X.get (g,n) = some ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩ ∧
      (laneOf l g = 0 → ∃ col < 2^16, n+1 < k ∧
        X.get (g,n+1) =
          some ⟨1909, .wr {loc := allocationSlot l g, size := 4} (b32 col).toBytes⟩) := by
  have hLate : 173 < e.pc := by
    rcases hDemand with h | h | h
    · rcases e with ⟨pc, kind⟩
      cases h
      exact exitIsAfterStartup hX he
    · omega
    · omega
  obtain ⟨n, t, o, hLe, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg he hLate
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨u, inst, hHint, hu, hTail⟩ := firstRegisterHintFromCommon hp hg ⟨12, by decide⟩
    (by simpa only [hw] using ht) hr (nonemptyAt (lt_of_le_of_lt hLe hLen))
  have hHint' : X.get (g,n) = some ⟨1907, .setMaxReg false 80 inst⟩ := hHint
  have hLt := laterThanKnown hHint' he hLe (fun h => by
    subst e
    rcases hDemand with h | h | h <;> cases h)
  obtain ⟨k, hk, hSync, hAlloc, hStore⟩ :=
    exactAllocatorPrefix hp hu hTail he hLt hDemand
  exact ⟨n+1, k, hk, hSync, hAlloc, hStore⟩

/-- A participant exiting its role has already arrived at the role's allocation rendezvous. -/
theorem allocationBeforeParticipantExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc : Nat} (hg : g < l.threads) (hw : warpIndex l g < 13)
    (he : X.get (g,j) = some ⟨pc, .exit⟩) :
    ∃ i < j, ∃ pc ∈ allocationEntrySites, X.IsBarrier (g,i) 2 (some 416) pc := by
  by_cases hM : warpIndex l g = 12
  · obtain ⟨_, i, hi, hBar, _, _⟩ := allocationPrefixAtBarrierReadOrExit hp hX hg hM he (.inl rfl)
    have hPast := laterThanKnown (e := ⟨1910, .bar 2 (some 416) .sync⟩) hBar he hi
      (fun h => Kind.noConfusion (congrArg Event.kind h))
    exact ⟨i, hPast, 1910, by decide, hBar⟩
  let w : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  obtain ⟨n, t, o, hLe, ht, hr⟩ :=
    commonDispatchOfLateEvent hp hX hg he (exitIsAfterStartup hX he)
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨u, inst, hHint, hu, hTail⟩ := firstRegisterHintFromCommon hp hg w ht hr
    (nonemptyAt (lt_of_le_of_lt hLe hLen))
  have hLt := laterThanKnown hHint he hLe (fun h =>
    Kind.noConfusion (congrArg Event.kind h))
  have hSite : u.pc ∈ allocationEntrySites := by
    rw [hu.1, firstSite w (by change warpIndex l g < 12; omega)]
    split <;> decide
  obtain ⟨hBefore, _⟩ := advanceAllocationBar hp.block hSite hu.2.2.2.1 hTail (by omega)
  have hBefore' : X.get (g,n+1) = some ⟨u.pc, .bar 2 (some 416) .sync⟩ := hBefore
  have hPast := laterThanKnown hBefore' he hLt (fun h =>
    Kind.noConfusion (congrArg Event.kind h))
  exact ⟨n+1, hPast, u.pc, hSite, hBefore⟩

end PTX.Kernels.TmlFa4Fwd.Mma
