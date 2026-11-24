-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorProgress
public import Kernels.TmlFa4Fwd.Proof.MmaQRegisters
import Kernels.TmlFa4Fwd.Proof.MmaDescriptorStartup
import Kernels.TmlFa4Fwd.Proof.MmaAllocationRead
import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

private theorem extendRecordedPrefix {l : Launch} {X : Execution} {g pos : Nat}
    {t u v : TState} {e : Event}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (he : X.get (g,pos) = some e)
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hStep : EStep kernel Assumptions.all l g u e (some v)) :
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some v) := by
  have hLen : pos < (X.tr g).length := len_of_get he
  rw [List.take_succ_eq_append_getElem hLen]
  have hAt : (X.tr g)[pos] = e := by
    change (X.tr g)[pos]? = some e at he
    rwa [List.getElem?_eq_getElem hLen, Option.some.injEq] at he
  rw [hAt]
  exact hPrefix.snoc hl hStep

private theorem roleEntryOnPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hLen : 5 < (X.tr g).length) :
    ∃ u o, At u 1908 (entryFacts p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 6) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop 6) o := by
  obtain ⟨t, o, ht, _, hPrefix, hr⟩ := nonzeroCommonPrefix hp hX hg (by omega) (by omega)
  have hReg : (1062, b32 12) ∈ nonzeroBarrierFacts p l g := by
    simp [nonzeroBarrierFacts, hw]
  have hAt : At t 174 (startupFacts p l) := ht.mono ⟨holds_mem ht.2.2.2.2 hReg,
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts]), trivial⟩
  obtain ⟨s, hs, hS⟩ := dispatchWarp12 hp hg hAt
  have hOut : out kernel [] l g s = .ev (.setMaxReg false 80 (next s)) := by
    unfold out
    rw [hS.1, hS.2.2.2.1, Flow.code_1907]
    rfl
  have hn : Next kernel Assumptions.all l g t s (.setMaxReg false 80 (next s)) :=
    ⟨run_rtg hs, (startupOut_eq_nil (by rw [hS.1]; decide) (by rw [hS.1]; decide)).trans hOut⟩
  obtain ⟨_, _, he, ⟨label, hKind, ha⟩, hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, _, he⟩; cases he) hr
    (fun h => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj ha
  exact ⟨_, o, hS.next, extendRecordedPrefix hPrefix he hn.steps
    ⟨_, hn.stop, label, hKind, rfl⟩, hTail⟩

private theorem allocAbiAfterRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hLen : allocationBarrierPos l g + 1 < (X.tr g).length) :
    ∃ u o, At u 1912 ((1179, b32 0) :: entryFacts p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (allocationBarrierPos l g + 2)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (allocationBarrierPos l g + 2)) o := by
  have hPos : 7 ≤ allocationBarrierPos l g := by unfold allocationBarrierPos; split <;> decide
  have hNonempty (pos : Nat) (h : pos ≤ allocationBarrierPos l g + 1) :
      (X.tr g).drop pos ≠ [] :=
    fun he => (Nat.not_le_of_lt hLen) ((List.drop_eq_nil_iff.mp he).trans h)
  obtain ⟨u, o, hu, hPrefix, hr⟩ := roleEntryOnPrefix hp hMax.1 hg hw (by omega)
  obtain ⟨t, htRun, ht⟩ := beforeAllocation (g := g) hu
  let after := if laneOf l g = 0 then {t with sub := 1} else next t
  have hBase : t.regs 2535 = some (b32 l.sharedBase) :=
    holds_mem ht.2.2.2.2 (by simp [entryFacts, startupFacts])
  have hCols : t.regs 2451 = some (b32 512) := ht.2.2.2.2.1
  have hAlloc : Next kernel Assumptions.all l g u t
      (.tc (.resource .one (some (allocationSlot l g)) (.alloc 512)) after) := by
    refine ⟨run_rtg htRun, ?_⟩
    rw [allocationTemplate hp ht.1 ht.2.2.2.1 hBase hCols, ht.2.1]
    rfl
  obtain ⟨_, _, hGet, ⟨rfl, hx⟩, hAfter⟩ := hAlloc.continuing_at_nonempty
    (by rintro _ ⟨_, he⟩; cases he) hr (hNonempty 6 (by omega))
  obtain rfl := Option.some.inj hx
  have hPast := extendRecordedPrefix hPrefix hGet hAlloc.steps ⟨_, hAlloc.stop, rfl, rfl⟩
  have hBarBoth :
      Run kernel Assumptions.all l g {} ((X.tr g).take (allocationBarrierPos l g)) (some (next t)) ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (allocationBarrierPos l g)) o := by
    by_cases hLane : laneOf l g = 0
    · have ht' : At t 1909 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)] :=
        ht.mono ⟨hCols,
          holds_mem ht.2.2.2.2 (by simp [entryFacts, startupFacts]), hBase, trivial⟩
      have hAllocGet : X.get (g,6) = some
          ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩ := ht.1 ▸ hGet
      simp only [after, hLane, ↓reduceIte] at hPast hAfter
      obtain ⟨_, _, _, _, hStorePast, hSuffix⟩ :=
        Thread.Allocation.allocatorStores hp hMax hg hw hLane ht' hAllocGet hPast hAfter
      simpa [allocationBarrierPos, hLane] using And.intro hStorePast hSuffix
    · simpa [allocationBarrierPos, hLane, after] using And.intro hPast hAfter
  have hAt : At (next t) 1910 (entryFacts p l g) := ht.next.mono ht.2.2.2.2.2
  have hBar : Next kernel Assumptions.all l g (next t) (next t)
      (.bar 2 (next (next t)) (some 416) .sync) :=
    ⟨.refl, allocationEntryTemplate hp.block (by rw [hAt.1]; decide) hAt.2.2.2.1⟩
  obtain ⟨_, _, hBarGet, ⟨rfl, hv⟩, hReadSuffix⟩ := hBar.continuing_at_nonempty
    (by rintro _ ⟨_, he⟩; cases he) hBarBoth.2 (hNonempty _ (by omega))
  obtain rfl := Option.some.inj hv
  have hBarPast := extendRecordedPrefix hBarBoth.1 hBarGet .refl ⟨_, hBar.stop, rfl, rfl⟩
  have hRead : Next kernel Assumptions.all l g (next (next t)) (next (next t))
      (.read {loc := allocationSlot l g, size := 4} (afterLoad (next (next t)) [1179])) :=
    ⟨.refl, allocationReadTemplate hp hAt.next⟩
  obtain ⟨_, _, he, ⟨bs, hBytes, rfl, hValue⟩, hRest⟩ := hRead.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hReadSuffix (hNonempty _ (by omega))
  obtain rfl := Option.some.inj hValue
  have hReadPast := extendRecordedPrefix hBarPast he .refl ⟨_, hRead.stop, bs, hBytes, rfl, rfl⟩
  have hEvent : X.get (g, allocationBarrierPos l g + 1) =
      some ⟨1911, .rd {loc := allocationSlot l g, size := 4} bs⟩ := by
    simpa only [hAt.next.1] using he
  obtain rfl := Thread.mmaAllocationReadZero hp hMax.1 hEvent
  exact ⟨_, o, allocationReadValue (col := 0) hAt.next, hReadPast, hRest⟩

/-- The scheduler startup prefix retains its launch arguments and shuffle ordinal. -/
theorem schedulerAbiAtDescriptorWithOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ∃ u o flag,
      X.get (g, descriptorShufflePos (laneOf l g)) =
        some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 (b32 (startupQLow l)) flag⟩ ∧
      X.ShflK (g, descriptorShufflePos (laneOf l g)) 3 ∧
      At u 1917 ((2450, b32 (startupQLow l)) :: entryFacts p l g) ∧
      Run kernel Assumptions.all l g {}
        ((X.tr g).take (descriptorShufflePos (laneOf l g) + 1)) (some u) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o := by
  have hPos : allocationBarrierPos l g + 2 = descriptorShufflePos (laneOf l g) := by
    unfold allocationBarrierPos descriptorShufflePos
    split <;> decide
  obtain ⟨j, e, value, ok, he, hKind, hK⟩ := Thread.Allocation.initialDescriptorShuffled hp hMax
    hg hw
  have hLate : 1911 < e.pc := by
    obtain ⟨⟨site, mode, w, x, y, v, valid, hEvent⟩, _⟩ := id hK
    have hEq := Option.some.inj (he.symm.trans hEvent)
    subst e
    exact shuffleAfterAllocation hp hMax.1 hw hEvent hK
  have hNotUb : ∀ f, e.kind ≠ .ub f := by rw [hKind]; intro f h; cases h
  obtain ⟨_, recv, valid, _, _, hShfl, hFourth, _, _⟩ :=
    descriptorSendBeforeEvent hp hMax.1 he hw hLate hNotUb
  have hLen : descriptorShufflePos (laneOf l g) < (X.tr g).length := len_of_get hShfl
  obtain ⟨t, o, ht, hPrefix, hSuffix⟩ :=
    allocAbiAfterRead hp hMax hg hw (by omega)
  have ht' : At t 1912 [(2535, b32 l.sharedBase)] :=
    ht.mono ⟨holds_mem ht.2.2.2.2 (by simp [entryFacts, startupFacts]), trivial⟩
  obtain ⟨u, hRun, hu⟩ := startupQWord hp g t ht'
  have hLocal := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hRun
  have hNext : Next kernel Assumptions.all l g t u
      (.shfl .idx (b32 (startupQLow l)) 0 31 (fun v _ => next (setReg u 2450 v))) :=
    ⟨run_rtg hLocal, startupQShuffle hp hu⟩
  rw [hPos] at hPrefix hSuffix
  obtain ⟨_, _, hGet, ⟨res, flag, rfl, hAfter⟩, hTail⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hSuffix
    (fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hAfter
  have hGet' : X.get (g, descriptorShufflePos (laneOf l g)) =
      some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 res flag⟩ := hu.1 ▸ hGet
  have hWarp := (Step.sameWarp_lane (by rw [hp.block]) hg (lane := 0) (by decide)).1
  have hw' : warpIndex l (warpLane l g 0) = 12 := hWarp.2.symm.trans hw
  obtain ⟨k, q, peer, okPeer, hpGet, hpKind, hpK⟩ :=
    Thread.Allocation.initialDescriptorShuffled hp hMax hWarp.1.2.1 hw'
  obtain ⟨pcPeer, kindPeer⟩ := q
  cases hpKind
  have hSrc : (shflSource .idx (laneOf l g) 0 31).1 = 0 := by
    rw [shflSource_idx _ (show 0 < 32 by decide)]
  have hReceived : res = b32 (startupQLow l) := by
    apply (shfl_source_value hMax.1 hGet' hFourth
      (show X.get (g - laneOf l g + (shflSource .idx (laneOf l g) 0 31).1, k) = _
        by rw [hSrc]; exact hpGet)
      (show X.ShflK (g - laneOf l g + (shflSource .idx (laneOf l g) 0 31).1, k) 3
        by rw [hSrc]; exact hpK)
      (by rw [hSrc]; exact ShflK.not_exited hMax.1 hWarp.1.2.1 hpK)).1
  subst res
  let regs := [7203, 1178, 1072, 1062, 2535, 6495, 7502, 7506, 7503]
  have hFrame {r : Nat} (h : r ∈ regs) : u.regs r = t.regs r :=
    schedulerLocalFrame (lo := 1912) (len := 4) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hRun ht.1.ge (by rw [ht.1]) h
  have hFacts : ∀ pair ∈ entryFacts p l g, pair.1 ∈ regs := by
    intro pair hm
    simp only [entryFacts, startupFacts, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  have hHold := holdsSchedulerFrame ht.2.2.2.2.2 (fun r h => hFrame h) hFacts
  have hU : At u 1916 (entryFacts p l g) := hu.mono hHold
  have hReturn := hU.set (r := 2450) (v := b32 (startupQLow l))
    (fun pair h => by have := hFacts pair h; simp [regs] at this; omega)
  exact ⟨_, o, flag, hGet', hFourth, hReturn, extendRecordedPrefix hPrefix hGet hNext.steps
    ⟨_, hNext.stop, _, flag, rfl, rfl⟩, hTail⟩

/-- All launch arguments used by the MMA scheduler survive the maximal startup prefix. -/
theorem schedulerAbiAtDescriptor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ∃ u o flag,
      X.get (g, descriptorShufflePos (laneOf l g)) =
        some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 (b32 (startupQLow l)) flag⟩ ∧
      At u 1917 ((2450, b32 (startupQLow l)) :: entryFacts p l g) ∧
      Run kernel Assumptions.all l g {}
        ((X.tr g).take (descriptorShufflePos (laneOf l g) + 1)) (some u) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o := by
  obtain ⟨u, o, flag, he, _, hu, hPrefix, hTail⟩ :=
    schedulerAbiAtDescriptorWithOrdinal hp hMax hg hw
  exact ⟨u, o, flag, he, hu, hPrefix, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
