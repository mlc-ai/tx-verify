-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueGroupProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

def initRoundPc (j : Nat) : Nat :=
  if h : j < 16 then (electSite ⟨j, h⟩).pc else 172

/-- Each earlier election and each selected initialization occurs in the same thread prefix. -/
def InitHistory (l : Launch) (X : Execution) (g n j : Nat) : Prop :=
  ∀ k : Fin 16, k.val < j →
    ∃ ix inst leader, ix < n ∧ X.Elect (g, ix) (electSite k).pc (2 ^ 32 - 1) inst leader ∧
      (laneOf l g = leader → ∀ a i, (initGroup k)[a]? = some i →
        ix + 1 + a < n ∧ X.get (g, ix + 1 + a) = some (initEvent l g i))

/-- All warp-zero lanes are at the same round, with their own actual trace positions. -/
def InitFrontier (l : Launch) (X : Execution) (g j : Nat) : Prop :=
  ∀ h, SameWarp l g h → ∃ n t, 0 < n ∧ InitCursor l X h n t ∧
    At t (initRoundPc j) (initFacts l j) ∧ EarlierEvents X h n (initRoundPc j) ∧
    (n = (X.tr h).length → Step.Released l X h) ∧ InitHistory l X h n j

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem startInitFrontier {g : Nat} (hw : warpIndex l g = 0) : InitFrontier l X g 0 := by
  intro h hh
  have hTid := hh.1.2.1
  have hLen := startupBroadcastsProgress hp hMax h hTid
  obtain ⟨t, u, o, hRun, hRest, hAt, hn⟩ :=
    warp0FirstElection hp hMax.1 hTid (hh.2.symm.trans hw) hLen
  have hAt' : At u (initRoundPc 0) (initFacts l 0) := by
    exact hAt
  refine ⟨3, u, by decide, ⟨hLen, t, hRun, hn.steps, o, hRest⟩, hAt', ?_, ?_, ?_⟩
  · intro k hk e he
    interval_cases k
    · rw [firstSharedValue hp hMax.1 h hTid he]
      exact (show 25 < 46 by decide)
    · rw [secondWarpValue hp hMax.1 h hTid he]
      exact (show 34 < 46 by decide)
    · rw [thirdWarpValue hp hMax.1 h hTid he]
      exact (show 35 < 46 by decide)
  · intro hEq
    apply Step.Released.of_get
    intro e he
    rw [← hEq] at he
    change X.get (h, 2) = some e at he
    rw [thirdWarpValue hp hMax.1 h hTid he]
    intro hBlock
    cases hBlock

  · intro k hk
    omega

omit hp hMax in
theorem roundSkipLe (k : Fin 16) :
    (electSite k).skipPc ≤ initRoundPc (k.val + 1) := by
  fin_cases k <;> decide

private theorem advanceInitFrontier {g j : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0)
    (hj : j < 16) (hFront : InitFrontier l X g j) : InitFrontier l X g (j + 1) := by
  classical
  let k : Fin 16 := ⟨j, hj⟩
  have hPc : initRoundPc j = (electSite k).pc := dite_eq_left hj
  let hData (h : Nat) : Nat × TState :=
    if hh : SameWarp l g h then
      ((hFront h hh).choose, (hFront h hh).choose_spec.choose)
    else (0, {})
  let idx (h : Nat) : Nat := (hData h).1
  let st (h : Nat) : TState := (hData h).2
  have hEntry (h : Nat) (hh : SameWarp l g h) :
      0 < idx h ∧ InitElectCursor l X h (idx h) k (st h) ∧
        At (st h) (electSite k).pc (initFacts l j) := by
    have hn := (hFront h hh).choose_spec.choose_spec
    have hIndex : idx h = (hFront h hh).choose := by simp [idx, hData, hh]
    have hState : st h = (hFront h hh).choose_spec.choose := by simp [st, hData, hh]
    rw [hIndex, hState]
    obtain ⟨hn, hc, ha, he, hr, _⟩ := hn
    have hpc' := ha.1.trans hPc
    have he' : EarlierEvents X h (hFront h hh).choose (electSite k).pc := he.mono hPc.le
    exact ⟨hn, ⟨hc, hpc', ha.2.2.2.1, he', hr⟩, ⟨hpc', ha.2⟩⟩
  have hAll := initElectionProgress hp hMax hg hw idx st
    (fun h hh => (hEntry h hh).1) (fun h hh => (hEntry h hh).2.1)
  intro h hh
  obtain ⟨inst, leader, u, hElect, hjn, hRecord⟩ := initGroupProgress hp hMax hh.1.2.1
    (hEntry h hh).2.1 (hEntry h hh).2.2 (hAll h hh)
  obtain ⟨v, hv, ha⟩ := initNext (A := Assumptions.all) (g := h) hp k hjn.state
  have hAt : At v (initRoundPc (j + 1)) (initFacts l (j + 1)) := ha
  have hLe : (electSite k).skipPc ≤ initRoundPc (j + 1) := roundSkipLe k
  refine ⟨_, v, by omega, hjn.cursor.localStep hv, hAt, ?_, hjn.released, ?_⟩
  · exact hjn.earlier.mono (hjn.state.1.symm ▸ hLe)
  · intro group hGroup
    by_cases hCurrent : group = k
    · subst group
      refine ⟨idx h, inst, leader, by omega, hElect, ?_⟩
      intro hLead a i ha
      have hLen : a < (initGroup k).length := (List.getElem?_eq_some_iff.mp ha).1
      exact ⟨by simp only [hLead, ↓reduceIte]; omega, hRecord hLead a i ha⟩
    · have hValue : group.val < j := by
        by_contra hBad
        apply hCurrent
        apply Fin.ext
        change group.val = j
        omega
      have hHistory := (hFront h hh).choose_spec.choose_spec.2.2.2.2.2
      have hIdx : idx h = (hFront h hh).choose := by simp [idx, hData, hh]
      obtain ⟨a, ii, ll, hIx, he, hInit⟩ := hHistory group hValue
      refine ⟨a, ii, ll, by omega, he, ?_⟩
      intro hLead b i hi
      obtain ⟨hPosition, hGet⟩ := hInit hLead b i hi
      exact ⟨by omega, hGet⟩

theorem initFrontierProgress {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0) :
    ∀ j ≤ 16, InitFrontier l X g j := by
  intro j
  induction j with
  | zero => intro _; exact startInitFrontier hp hMax hw
  | succ j ih =>
    intro hj
    exact advanceInitFrontier hp hMax hg hw (by omega) (ih (by omega))

/-- At the initialization fence every one of the sixteen groups is recorded in the warp, with
the selected lane's consecutive initialization records before the fence. -/
theorem warp0InitHistoryAtFence {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0) :
    ∃ n t, 0 < n ∧ InitCursor l X g n t ∧ At t 172 (initFacts l 16) ∧ EarlierEvents X g n 172 ∧
      (n = (X.tr g).length → Step.Released l X g) ∧ InitHistory l X g n 16 := by
  have hSame : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  exact initFrontierProgress hp hMax hg hw 16 (by decide) g hSame

end
end PTX.Kernels.TmlFa4Fwd.Prologue
