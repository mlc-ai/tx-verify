-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Rounds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Traverse whole initialization rounds up to a witnessed instruction address. -/
theorem prefixInitRound {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0)
    (hThree : 3 ≤ (X.tr g).length) {bound : Nat}
    (hAvailable : ∀ n ≤ 68, ∀ pc ≤ bound, EarlierEvents X g n pc → n < (X.tr g).length) :
    ∀ j ≤ 16, initRoundPc j ≤ bound → ∃ n t, 0 < n ∧ n ≤ 3 + 4 * j ∧ InitCursor l X g n t ∧
      At t (initRoundPc j) (initFacts l j) ∧ EarlierEvents X g n (initRoundPc j) ∧
      InitHistory l X g n j := by
  intro j
  induction j with
  | zero =>
    intro _ _
    obtain ⟨t, u, o, hr, hTail, hAt, hNext⟩ := warp0FirstElection hp hX hg hw hThree
    refine ⟨3, u, by decide, by decide, ⟨hThree, t, hr, hNext.steps, o, hTail⟩, hAt, ?_, ?_⟩
    · intro k hk ev he
      interval_cases k
      · rw [firstSharedValue hp hX g hg he]
        exact (show 25 < 46 by decide)
      · rw [secondWarpValue hp hX g hg he]
        exact (show 34 < 46 by decide)
      · rw [thirdWarpValue hp hX g hg he]
        exact (show 35 < 46 by decide)
    · intro k hk
      omega
  | succ j ih =>
    intro hj hBound
    have hJ : j < 16 := by omega
    let i : Fin 16 := ⟨j, hJ⟩
    have hPc : initRoundPc j = (electSite i).pc := dite_eq_left hJ
    have hLe := roundSkipLe i
    rw [groupExit] at hLe
    have hElectPc : (electSite i).pc ≤ bound := by
      change _ ≤ initRoundPc (j+1) at hLe
      omega
    obtain ⟨n, t, hn, hN, hCur, hAt, hEarlier, hHistory⟩ :=
      ih (by omega) (hPc.symm ▸ hElectPc)
    rw [hPc] at hAt hEarlier
    have hGroup : (initGroup i).length ≤ 3 := by
      have hSmall : ∀ k : Fin 16, (initGroup k).length ≤ 3 := by intro k; fin_cases k <;> decide
      exact hSmall i
    have hElectLen := hAvailable n (by omega) _ hElectPc hEarlier
    have hElect : InitElectCursor l X g n i t :=
      ⟨hCur, hAt.1, hAt.2.2.2.1, hEarlier, fun h => (by omega : False).elim⟩
    have hIssuer : InitIssuerOn l X g (· ≤ 69) (· ∈ initGroup i) := by
      intro site ix state hSite _ hC hBudget hPrev _ hPc hf hAddr hCount
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hSite
      have hPos := (List.getElem?_eq_some_iff.mp hk).1
      have hSitePc := (groupCode i k site hk).1
      have hSiteBound : (initSite site).pc ≤ bound := by
        change _ ≤ initRoundPc (j+1) at hLe
        omega
      have hLen := hAvailable ix (by omega) state.pc (hPc.symm ▸ hSiteBound) hPrev
      exact initializerAtCursor hp site hC hLen hPc hf hAddr hCount
    obtain ⟨inst, leader, u, hElection, hJoin, hInit⟩ :=
      initGroupUsingOn hIssuer (fun k hk => by omega) hElect hAt hElectLen
    obtain ⟨v, hPath, hv⟩ := initNext (A := Assumptions.all) (g := g) hp i hJoin.state
    have hLe := roundSkipLe i
    have hOld : EarlierEvents X g _ (initRoundPc (j + 1)) :=
      hJoin.earlier.mono (hJoin.state.1.symm ▸ hLe)
    have hCost : (if laneOf l g = leader then (initGroup i).length else 0) ≤ 3 := by
      split <;> omega
    refine ⟨_, v, by omega, by omega, hJoin.cursor.localStep hPath, hv, hOld, ?_⟩
    intro group hGroup
    by_cases hThis : group = i
    · subst group
      refine ⟨n, inst, leader, by omega, hElection, ?_⟩
      intro hLeader k site hSite
      have hK := (List.getElem?_eq_some_iff.mp hSite).1
      exact ⟨by simp only [hLeader, ↓reduceIte]; omega, hInit hLeader k site hSite⟩
    · have hPrior : group.val < j := by
        by_contra hBad
        apply hThis
        apply Fin.ext
        change group.val = j
        omega
      obtain ⟨k, ii, ll, hK, he, hs⟩ := hHistory group hPrior
      exact ⟨k, ii, ll, by omega, he, fun hLead a site ha =>
        let ⟨hI, hGet⟩ := hs hLead a site ha
        ⟨by omega, hGet⟩⟩

omit hp hX in
private theorem fixedEventAtCursor {l : Launch} {X : Execution} {g n : Nat}
    {t u : TState} {tmpl : Tmpl} {e : Event}
    (hCur : InitCursor l X g n t) (hLen : n < (X.tr g).length)
    (hOut : out kernel Assumptions.all l g t = .ev tmpl)
    (hOnly : ∀ a o, Fires t.pc tmpl a o → a = e ∧ o = some u) :
    X.get (g, n) = some e ∧ InitCursor l X g (n + 1) u ∧
      ∃ o, Run kernel Assumptions.all l g {} ((X.tr g).take (n + 1)) (some u) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop (n + 1)) o := by
  obtain ⟨_, s, hPrefix, hTau, o, hTail⟩ := hCur
  have hNext : Next kernel Assumptions.all l g s t tmpl := ⟨hTau, hOut⟩
  rw [List.drop_eq_getElem_cons hLen] at hTail
  obtain ⟨v, he, hr⟩ := hNext.continuing_event (by
    intro h
    have hBad := (hOnly _ _ h).2
    cases hBad) hTail
  obtain ⟨hE, hV⟩ := hOnly _ _ he
  have hU : v = u := Option.some.inj hV
  subst v
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (n + 1)) (some u) := by
    rw [List.take_succ_eq_append_getElem hLen]
    exact hPrefix.snoc hTau ⟨_, hOut, he⟩
  refine ⟨?_, ⟨Nat.succ_le_of_lt hLen, u, hPast, .refl, o, hr⟩, o, hPast, hr⟩
  change (X.tr g)[n]? = _
  rw [List.getElem?_eq_getElem hLen, hE]

private theorem warp0CommonPrefixUsing {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0)
    (hThree : 3 ≤ (X.tr g).length)
    (hAvailable : ∀ n ≤ 68, ∀ pc ≤ 173, EarlierEvents X g n pc → n < (X.tr g).length) :
    ∃ n t o, n + 2 ≤ 69 ∧ At t 174 (initFacts l 16) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (n + 2)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (n + 2)) o ∧
      X.get (g, n) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, n + 1) = some ⟨173, .bar 0 none .sync⟩ ∧
      EarlierEvents X g (n + 1) 173 ∧ InitHistory l X g n 16 := by
  obtain ⟨n, t, _, hN, hCur, hAt, hEarlier, hHistory⟩ :=
    prefixInitRound hp hX hg hw hThree hAvailable 16 (by decide) (by decide)
  have hp' : t.pc = 172 := hAt.1
  have hf : t.fault = none := hAt.2.2.2.1
  have hFenceCore : out kernel [] l g t = .ev (.fenceMbarInit (next t)) := by
    unfold out
    rw [hp', hf, Flow.code_172]
    rfl
  have hFence := startupOut (A := Assumptions.all) (.inl (by rw [hp']; decide)) hFenceCore
  have hFlen := hAvailable n (by omega) 172 (by decide) hEarlier
  obtain ⟨hF, hAfter, _⟩ := fixedEventAtCursor (e := ⟨172, .fenceMbarInit⟩) hCur hFlen hFence
    (fun a o h => ⟨by rw [h.1, hp'], h.2⟩)
  have hp'' : (next t).pc = 173 := by change t.pc + 1 = 173; rw [hp']
  have hBarCore : out kernel [] l g (next t) = .ev (.bar 0 (next (next t)) none .sync) := by
    have hFault : (next t).fault = none := hf
    unfold out
    rw [hp'', hFault, Flow.code_173]
    rfl
  have hBar := startupOut (A := Assumptions.all) (.inl (by rw [hp'']; decide)) hBarCore
  have hEarlier' : EarlierEvents X g (n + 1) 173 := hEarlier.succ hF rfl
  have hBlen := hAvailable (n + 1) (by omega) 173 (by decide) hEarlier'
  obtain ⟨hB, _, o, hPrefix, hTail⟩ := fixedEventAtCursor (e := ⟨173, .bar 0 none .sync⟩)
    hAfter hBlen hBar (fun a o h => ⟨by rw [h.1, hp''], h.2⟩)
  have hAt' : At (next (next t)) 174 (initFacts l 16) :=
    ⟨by change (next t).pc + 1 = 174; rw [hp''], hAt.2⟩
  exact ⟨n, next (next t), o, by omega, hAt', hPrefix, hTail, hF, hB, hEarlier', hHistory⟩

/-- An actual common barrier record suffices to recover the returning startup state. -/
theorem warp0CommonPrefixOfRendezvous {g index : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0)
    (he : X.get (g,index) = some ⟨173,.bar 0 none .sync⟩) :
    ∃ n t o, n + 1 ≤ index ∧ At t 174 (initFacts l 16) ∧
      X.get (g,n+1) = some ⟨173,.bar 0 none .sync⟩ ∧ EarlierEvents X g (n+2) 174 ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (n+2)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (n+2)) o := by
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hThree : 3 ≤ (X.tr g).length := by
    suffices hi : 3 ≤ index by omega
    by_contra! hi
    interval_cases index
    · cases firstSharedValue hp hX g hg he
    · cases secondWarpValue hp hX g hg he
    · cases thirdWarpValue hp hX g hg he
  have hAvailable (n : Nat) (_ : n ≤ 68) (pc : Nat) (hPc : pc ≤ 173)
      (hEarlier : EarlierEvents X g n pc) : n < (X.tr g).length := by
    have hLe : n ≤ index := by
      by_contra! h
      have hOld := hEarlier index h _ he
      simp only at hOld
      omega
    omega
  obtain ⟨n,t,o,_,ht,hRun,hTail,_,hBar,hEarlier,_⟩ :=
    warp0CommonPrefixUsing hp hX hg hw hThree hAvailable
  have hLe : n + 1 ≤ index := by
    by_contra! h
    have hOld := hEarlier index h _ he
    exact (Nat.lt_irrefl 173) hOld
  exact ⟨n,t,o,hLe,ht,hBar,hEarlier.succ hBar (by decide),hRun,hTail⟩

/-- A long enough consistent warp-zero trace has traversed the prologue. -/
theorem warp0CommonPrefix {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0)
    (hLen : 69 ≤ (X.tr g).length) :
    ∃ n t o, n ≤ 69 ∧ At t 174 (initFacts l 16) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take n) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop n) o := by
  obtain ⟨n, t, o, hN, hAt, hPre, hTail, _⟩ :=
    warp0CommonPrefixUsing hp hX hg hw (by omega) (fun _ h _ _ _ => by omega)
  exact ⟨n + 2, t, o, hN, hAt, hPre, hTail⟩

/-- Any observed startup barrier or later instruction establishes the actual initializer prefix.
The warp can still be waiting at the common barrier. -/
theorem warp0InitializerPrefix {g index : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0)
    {e : Event} (he : X.get (g, index) = some e) (hPc : 173 ≤ e.pc) :
    ∃ n ≤ index, X.get (g, n) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, n + 1) = some ⟨173, .bar 0 none .sync⟩ ∧
      EarlierEvents X g (n + 1) 173 ∧ InitHistory l X g n 16 := by
  have hLen := (List.getElem?_eq_some_iff.mp he).1
  change index < (X.tr g).length at hLen
  have hFirst : 3 ≤ index := by
    by_contra h
    have hi : index < 3 := by omega
    interval_cases index
    · rw [firstSharedValue hp hX g hg he] at hPc
      exact (by decide : ¬ 173 ≤ 25) hPc
    · rw [secondWarpValue hp hX g hg he] at hPc
      exact (by decide : ¬ 173 ≤ 34) hPc
    · rw [thirdWarpValue hp hX g hg he] at hPc
      exact (by decide : ¬ 173 ≤ 35) hPc
  have hAvailable (n : Nat) (_ : n ≤ 68) (pc : Nat) (hPc' : pc ≤ 173)
      (hEarlier : EarlierEvents X g n pc) : n < (X.tr g).length := by
    have hLe : n ≤ index := by
      by_contra h
      have hOld := hEarlier index (by omega) e he
      omega
    omega
  obtain ⟨n, _, _, _, _, _, _, hF, hB, hEarlier, hHistory⟩ :=
    warp0CommonPrefixUsing hp hX hg hw (by omega) hAvailable
  have hn : n ≤ index := by
    by_contra h
    have hOld := hEarlier index (by omega) e he
    omega
  exact ⟨n, hn, hF, hB, hEarlier, hHistory⟩

/-- A warp-zero event past the startup barrier has traversed the actual common prefix. -/
theorem warp0CommonPrefixOfLateEventWithEarlier {g index : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 0) {e : Event} (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    ∃ n t o, n ≤ index ∧ At t 174 (initFacts l 16) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop n) o ∧ EarlierEvents X g n 174 := by
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hFirst : 3 ≤ index := by
    by_contra h
    have hi : index < 3 := by omega
    interval_cases index
    · rw [firstSharedValue hp hX g hg he] at hPc
      exact (by decide : ¬ 173 < 25) hPc
    · rw [secondWarpValue hp hX g hg he] at hPc
      exact (by decide : ¬ 173 < 34) hPc
    · rw [thirdWarpValue hp hX g hg he] at hPc
      exact (by decide : ¬ 173 < 35) hPc
  have hAvailable (n : Nat) (_ : n ≤ 68) (pc : Nat) (hPc' : pc ≤ 173)
      (hEarlier : EarlierEvents X g n pc) : n < (X.tr g).length := by
    have hLe : n ≤ index := by
      by_contra h
      have hOld := hEarlier index (by omega) e he
      omega
    omega
  obtain ⟨n, t, o, _, ht, _, hr, _, hB, hEarlier, _⟩ :=
    warp0CommonPrefixUsing hp hX hg hw (by omega) hAvailable
  have hPrior : EarlierEvents X g (n + 2) 174 := hEarlier.succ hB rfl
  have hAfter : n + 2 ≤ index := by
    by_contra h
    exact (Nat.not_lt_of_ge (by omega : 174 ≤ e.pc)) (hPrior index (by omega) e he)
  exact ⟨n + 2, t, o, hAfter, ht, hr, hPrior⟩

/-- A warp-zero event past the startup barrier has traversed the actual common prefix. -/
theorem warp0CommonPrefixOfLateEvent {g index : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0)
    {e : Event} (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    ∃ n t o, n ≤ index ∧ At t 174 (initFacts l 16) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop n) o := by
  obtain ⟨n, t, o, hn, ht, hr, _⟩ := warp0CommonPrefixOfLateEventWithEarlier hp hX hg hw he hPc
  exact ⟨n, t, o, hn, ht, hr⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue
