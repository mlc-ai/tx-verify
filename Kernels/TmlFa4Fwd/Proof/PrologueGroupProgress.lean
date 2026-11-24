-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- An actual warp-zero cursor at the join after an entire initialization group. -/
structure InitJoinCursor (l : Launch) (X : Execution) (g n : Nat) (j : Fin 16)
    (t : TState) : Prop where
  cursor : InitCursor l X g n t
  state : At t (electSite j).skipPc (initFacts l j.val)
  earlier : EarlierEvents X g n t.pc
  released : n = (X.tr g).length → Step.Released l X g

section
variable {l : Launch} {X : Execution} {g n : Nat} {j : Fin 16} {t : TState} {Available : Nat → Prop}

/-- The selected lane emits only the group's decoded initializer records. Followers take
the branch to the same join without an object event. -/
theorem initGroupPrefixUsing {count : Nat} (hCount : count ≤ (initGroup j).length)
    (issuer : InitIssuerOn l X g Available (· ∈ (initGroup j).take count))
    (hAvailable : ∀ k ≤ n + 1 + count, Available k) (hLoc : InitElectCursor l X g n j t)
    (hAt : At t (electSite j).pc (initFacts l j.val)) (hLt : n < (X.tr g).length) :
    ∃ inst leader u,
      X.Elect (g, n) (electSite j).pc (2 ^ 32 - 1) inst leader ∧
      let stop := n + 1 + if laneOf l g = leader then count else 0
      InitCursor l X g stop u ∧
      At u (if laneOf l g = leader then (electSite j).pc + 4 + count else (electSite j).skipPc)
        (initFacts l j.val) ∧ EarlierEvents X g stop u.pc ∧
      (stop = (X.tr g).length → Step.Released l X g) ∧
      (laneOf l g = leader →
        ∀ k < count, ∀ i, (initGroup j)[k]? = some i →
          X.get (g, n + 1 + k) = some (initEvent l g i)) := by
  obtain ⟨inst, leader, he, hAfter⟩ := electionAtCursor hLoc hLt
  let s := electSite j
  let q := electedState l g t s leader
  have hPc : q.pc = s.pc + 1 := by change t.pc + 1 = s.pc + 1; rw [hLoc.pc]
  have hReady : n + 1 = (X.tr g).length → Step.Released l X g :=
    releasedIfLast he (by intro h; cases h)
  have hPrev : EarlierEvents X g (n + 1) (s.pc + 1) :=
    EarlierEvents.succ hLoc.earlier he rfl
  have hKeep (r : Nat) (hn : r ∉ [s.laneReg, s.chosenReg, s.skipReg, s.countReg]) :
      r ≠ s.laneReg ∧ r ≠ s.chosenReg ∧ r ≠ s.skipReg ∧ r ≠ s.countReg := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hn
  by_cases hLeader : laneOf l g = leader
  · let a := next (setReg q s.skipReg (.pred false))
    let v := next (setReg (next a) s.countReg (b32 s.count))
    have hChosen : q.regs s.chosenReg = some (.pred true) := by
      simp [q, electedState, next, setReg, hLeader]
    have hLocal : run kernel Assumptions.all l g 3 q = some v :=
      electRouteWith (A := Assumptions.all) (g := g) j true hPc hLoc.fault
        hAt.2.1 hAt.2.2.1 hChosen
    have hV : v.pc = s.pc + 4 := by change t.pc + 1 + 1 + 1 + 1 = _; rw [hLoc.pc]
    have hFacts : Holds v.regs (initFacts l j.val) := by
      apply electionInitFacts hAt.2.2.2.2
      intro r hn
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hKeep r hn
      simp [v, a, q, electedState, next, setReg, h₁, h₂, h₃, h₄]
    have hAddr (i : Fin 34) (hi : i ∈ initGroup j) :
        v.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)) ∧
        v.regs (initSite i).countReg = some (b32 (initSite i).count) := by
      obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hi
      have hh := groupCode j k i (List.getElem?_eq_some_iff.mpr ⟨hk, hki⟩)
      exact ⟨initGroupBases hFacts i hi, by simp [v, s, next, setReg, hh.2.1, hh.2.2.1]⟩
    have hAtPc (k : Nat) (i : Fin 34) (hi : (initGroup j)[k]? = some i) :
        (initSite i).pc = v.pc + k := by
      rw [hV]
      exact (groupCode j k i hi).1
    have hEarlier : EarlierEvents X g (n + 1) v.pc := hPrev.mono (by rw [hV]; omega)
    have hLength : ((initGroup j).take count).length = count := by
      simp [List.length_take, Nat.min_eq_left hCount]
    obtain ⟨hCur, hOld, hRel, hRecord⟩ :=
      initRecordsUsingOn issuer ((initGroup j).take count) (n + 1) v
        (fun _ h => h) (by omega) (hAfter.localStep (run_rtg hLocal)) hEarlier hReady hLoc.fault
        (by rwa [hLength]) (fun k i hi => by
          have hk := (List.getElem?_eq_some_iff.mp hi).1
          rw [hLength] at hk
          rw [List.getElem?_take_of_lt hk] at hi
          exact hAtPc k i hi)
        (fun i hi => hAddr i (List.mem_of_mem_take hi))
    rw [hLength] at hCur hOld hRel
    let u := { v with pc := v.pc + count }
    have hStop : u.pc = s.pc + 4 + count := by change v.pc + count = _; rw [hV]
    refine ⟨inst, leader, u, he, ?_⟩
    simp only [hLeader, ↓reduceIte]
    exact ⟨hCur, ⟨hStop, hAt.2.1, hAt.2.2.1, hLoc.fault, hFacts⟩, hOld, hRel,
      fun _ k hk i hi => hRecord k i (by rwa [List.getElem?_take_of_lt hk])⟩
  · have hChosen : q.regs s.chosenReg = some (.pred false) := by
      simp [q, electedState, next, setReg, hLeader]
    obtain ⟨u, hu, hSkip, hf, hs, ha, hRegs⟩ :=
      followerInitGroupWith (A := Assumptions.all) (g := g) j hPc hLoc.fault
        hAt.2.1 hAt.2.2.1 hChosen
    have hFacts : Holds u.regs (initFacts l j.val) := by
      apply electionInitFacts hAt.2.2.2.2
      intro r hn
      obtain ⟨h₁, h₂, h₃, _⟩ := hKeep r hn
      exact (hRegs r h₃).trans (by simp [q, electedState, next, setReg, h₁, h₂])
    have hLe : s.pc + 1 ≤ u.pc := by
      rw [hSkip, groupExit]
      change s.pc + 1 ≤ s.pc + 4 + _
      omega
    refine ⟨inst, leader, u, he, ?_⟩
    simp only [hLeader, ↓reduceIte, Nat.add_zero]
    exact ⟨hAfter.localStep (run_rtg hu), ⟨hSkip, hs, ha, hf, hFacts⟩,
      hPrev.mono hLe, hReady, fun h => h.elim⟩

/-- The selected lane emits only the group's decoded initializer records. Followers take
the branch to the same join without an object event. -/
theorem initGroupUsingOn (issuer : InitIssuerOn l X g Available (· ∈ initGroup j))
    (hAvailable : ∀ k ≤ n + 1 + (initGroup j).length, Available k)
    (hLoc : InitElectCursor l X g n j t) (hAt : At t (electSite j).pc (initFacts l j.val))
    (hLt : n < (X.tr g).length) :
    ∃ inst leader u,
      X.Elect (g, n) (electSite j).pc (2 ^ 32 - 1) inst leader ∧
      InitJoinCursor l X g (n + 1 + if laneOf l g = leader then (initGroup j).length else 0) j u ∧
      (laneOf l g = leader →
        ∀ k i, (initGroup j)[k]? = some i → X.get (g, n + 1 + k) = some (initEvent l g i)) := by
  obtain ⟨inst, leader, u, he, hCur, hu, hOld, hReady, hGet⟩ :=
    initGroupPrefixUsing (count := (initGroup j).length) (Nat.le_refl _)
      (fun i {n} {t} hi => issuer i (n := n) (t := t) (List.mem_of_mem_take hi))
      hAvailable hLoc hAt hLt
  have hSkip : (if laneOf l g = leader then (electSite j).pc + 4 + (initGroup j).length
      else (electSite j).skipPc) = (electSite j).skipPc := by
    split
    · exact (groupExit j).symm
    · rfl
  rw [hSkip] at hu
  exact ⟨inst, leader, u, he, ⟨hCur, hu, hOld, hReady⟩,
    fun h k i hi => hGet h k (List.getElem?_eq_some_iff.mp hi).1 i hi⟩

/-- The selected lane emits only the group's decoded initializer records. Followers take
the branch to the same join without an object event. -/
theorem initGroupUsing (issuer : InitIssuer l X g Available)
    (hAvailable : ∀ k ≤ n + 1 + (initGroup j).length, Available k)
    (hLoc : InitElectCursor l X g n j t) (hAt : At t (electSite j).pc (initFacts l j.val))
    (hLt : n < (X.tr g).length) :
    ∃ inst leader u,
      X.Elect (g, n) (electSite j).pc (2 ^ 32 - 1) inst leader ∧
      InitJoinCursor l X g (n + 1 + if laneOf l g = leader then (initGroup j).length else 0) j u ∧
      (laneOf l g = leader →
        ∀ k i, (initGroup j)[k]? = some i → X.get (g, n + 1 + k) = some (initEvent l g i)) := by
  exact initGroupUsingOn (fun i {n} {t} _ => issuer i (n := n) (t := t)) hAvailable hLoc hAt hLt
end

/-- The selected lane emits only the group's decoded initializer records. Followers take
the branch to the same join without an object event. -/
theorem initGroupProgress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g n : Nat} (hg : g < l.threads) {j : Fin 16} {t : TState}
    (hLoc : InitElectCursor l X g n j t)
    (hAt : At t (electSite j).pc (initFacts l j.val)) (hLt : n < (X.tr g).length) :
    ∃ inst leader u,
      X.Elect (g, n) (electSite j).pc (2 ^ 32 - 1) inst leader ∧
      InitJoinCursor l X g (n + 1 + if laneOf l g = leader then (initGroup j).length else 0) j u ∧
      (laneOf l g = leader →
        ∀ k i, (initGroup j)[k]? = some i → X.get (g, n + 1 + k) = some (initEvent l g i)) := by
  exact initGroupUsing (Available := fun _ => True)
    (fun i _ _ hN hC _ _ hR hP hF hA hK =>
      initializerProgress hp hMax i hg hN hC hR hP hF hA hK)
    (by simp) hLoc hAt hLt

end
end PTX.Kernels.TmlFa4Fwd.Prologue
