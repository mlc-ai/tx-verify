-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Export.BeforePv
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Mma.Export.PvPrev
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The order of the PV MMAs of a stage

The PV MMAs of a tile are in the order of their steps (`pv_order`): they are of one block, whose
place and round give the lane's elections (`pv_elections`), and step 0 directly follows an election.
A step follows the one before, with polls between (`pv_prev`), and an MMA or a commit after a step
follows the next one or is it (`pv_next`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A PV MMA is of one step. -/
theorem pv_eq {k st u st' u' : Nat} {j j' : Fin 8} (h : Tm.Pv L X g k st u j)
    (h' : Tm.Pv L X g k st' u' j') : st = st' ∧ u = u' ∧ j = j' := by
  obtain ⟨_, _, e⟩ := h.issue
  obtain ⟨_, _, e'⟩ := h'.issue
  rw [e] at e'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq,
    TcMma.OperandSpec.mk.injEq] at e'
  obtain ⟨-, h1, ⟨-, -, -, -, -, h2, -⟩, -⟩ := e'
  obtain rfl : st = st' := by omega
  have hp := h.p
  have hp' := h'.p
  exact ⟨rfl, by omega, Fin.ext (by omega)⟩

/-- The elections before a PV MMA of tile `u` of stage `st`, in a tile of `R` rounds. -/
def pvElections (R st u : Nat) : Nat :=
  5 + 8 * u + (if u < R then (if st = 0 then 1 else 4) else (if st = 0 then 3 else 4))

private theorem electAll_lin (q r : Nat) : electAll q r = electAll q 0 + 8 * r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [electAll_succ, ih]; omega

private theorem electAll_pv : ∀ (b : Fin 4) (j : Fin 8), electAll (Site.pv b j).ord 0 =
    5 + if b.val < 2 then (if b.val % 2 = 0 then 1 else 4)
      else (if b.val % 2 = 0 then 3 else 4) := by decide

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hw

/-- **The state of a PV MMA.** -/
private theorem pv_state {k st u : Nat} {j : Fin 8} (hq : Tm.Pv L X g k st u j) :
    ∃ d n b, Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)) ∧
      d.site = .pv b j ∧ b.val % 2 = st ∧ n (.mma .lost) = 0 ∧ n .ub = 0 ∧
      ∃ R, MmaRounds p L g R ∧ elections X g k = pvElections R st u := by
  obtain ⟨pc, db, he⟩ := hq.issue
  obtain ⟨d, n, hσ, hJ, hws, hlost, hub, hev⟩ := win_state hp hX hFw hw he
    (.inl ⟨_, _, _, _, rfl⟩)
  obtain ⟨hqk, hpv⟩ := mma_at_site hp hX hw he hσ hJ
  obtain ⟨b, j1, hs⟩ : ∃ b j1, d.site = .pv b j1 := by
    rcases mma_site hev with ⟨b, j', h⟩ | h
    · obtain ⟨u', h'⟩ := hqk b j' h
      obtain ⟨_, _, _, he'⟩ := h'.issue
      rw [he] at he'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq,
        TcMma.OperandSpec.mk.injEq] at he'
      obtain ⟨-, -, ⟨-, -, -, -, -, ha, -⟩, -⟩ := he'
      exact absurd ha (by simp)
    · exact h
  obtain ⟨u1, h1⟩ := hpv b j1 hs
  obtain ⟨rfl, rfl, rfl⟩ := pv_eq hq h1
  refine ⟨d, n, b, hσ, hs, rfl, hlost, hub, ?_⟩
  -- the round and the place
  rcases mma_counts hp hX hFw hw he (fun f h => by cases h) with ⟨s', n', hS, hev', hx⟩ | hev' |
    ⟨d', n', r, w, hσ', hQ, hcm, hF, hev'⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s'
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev'
    all_goals simp [Startup.Ev] at hev'
  · rcases hev' with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> cases hk'
  have hEq := hσ.symm.trans hσ'
  simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
    true_and] at hEq
  obtain ⟨rfl, rfl⟩ := hEq
  obtain ⟨R, bal, hC, hB⟩ := bs_ref (pmid_of (by rw [hs]; rfl)) hF
  refine ⟨_, ⟨R, bal, hC.1, rfl⟩, ?_⟩
  rw [mma_elections hX hσ hQ, hs]
  -- the commits give the round
  have hcom := hq.com
  have hcc : Tm.sCommits L X g (b.val % 2) k =
      if w then commitAt d.site.ord r (80 + 8 * (b.val % 2)) else 0 := by
    unfold Tm.sCommits
    have : Tm.sFull L (g / L.block) (b.val % 2) = obj L g (80 + 8 * (b.val % 2)) := rfl
    rw [this, mma_commits, count hσ]
    exact hQ.com _
  rw [hcc, hs] at hcom
  have hw1 : w = true := by
    cases w
    · simp at hcom
    · rfl
  subst hw1
  simp only [↓reduceIte] at hcom
  have hru : r = u := by
    clear hpv hqk hs hcc hq h1 he hev hev' hcm hQ hws
    fin_cases b <;> fin_cases j <;> simp [Site.ord, commitAt, pq] at hcom <;> omega
  subst hru
  have hl := hQ.loop
  have ht := hQ.tail
  rw [hs, hB] at hl ht
  change _ → (r : Int) + 1 < Bs p L g (mmaRef p L g R bal) ∧ _ at hl
  change _ → (r : Int) + 1 = Bs p L g (mmaRef p L g R bal) ∨
    (r = 0 ∧ Bs p L g (mmaRef p L g R bal) < 2) at ht
  generalize Bs p L g (mmaRef p L g R bal) = B at *
  rw [electAll_lin]
  have hR : (b.val < 2 → r < B.toNat - 1) ∧ (2 ≤ b.val → ¬ r < B.toNat - 1) := by
    constructor
    · intro hb
      have := (hl (by
        have : ∀ (b : Fin 4) (j : Fin 8), b.val < 2 → 20 ≤ (Site.pv b j).ord ∧
          (Site.pv b j).ord < 60 := by decide
        exact this b j hb)).1
      omega
    · intro hb
      have := ht (by
        have : ∀ (b : Fin 4) (j : Fin 8), 2 ≤ b.val → 60 ≤ (Site.pv b j).ord ∧
          (Site.pv b j).ord < 100 := by decide
        exact this b j hb)
      omega
  rw [electAll_pv]
  unfold pvElections
  by_cases hb : b.val < 2
  · rw [ite_eq_left hb, ite_eq_left (hR.1 hb)]; omega
  · rw [ite_eq_right hb, ite_eq_right (hR.2 (by omega))]; omega

/-- **The elections before a PV MMA.** -/
theorem pv_elections {k st u : Nat} {j : Fin 8} (hq : Tm.Pv L X g k st u j) :
    ∃ R, MmaRounds p L g R ∧ elections X g k = pvElections R st u := by
  obtain ⟨_, _, _, -, -, -, -, -, h⟩ := pv_state hp hX hFw hw hq
  exact h

/-- The PV MMA at a PV site's state, when the lane reaches a later state without a stop. -/
private theorem pv_of_site {K i : Nat} {e : Event} {σ : (glued p L g).D} {n' : Cls → Nat}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0) (hi : i < K)
    {d : D} {n : Cls → Nat} {b : Fin 4} {j : Fin 8}
    (hσ : Frame.stateAt (thread p L) X g i = some (some (minj p L g d n)))
    (he : X.get (g, i) = some e) (hs : d.site = .pv b j) :
    ∃ u, Tm.Pv L X g i (b.val % 2) u j := by
  have hev := (mfired hp hX he hσ).1
  simp only [Ev, hs] at hev
  obtain ⟨pc, kd⟩ := e
  rcases hev with ⟨a, s, acc, ms, rfl⟩ | ⟨f, rfl⟩
  · obtain ⟨d', m', hσ', hJ, -⟩ := win_state hp hX hFw hw he (.inl ⟨_, _, _, _, rfl⟩)
    have hEq := hσ.symm.trans hσ'
    simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    exact (mma_at_site hp hX hw he hσ hJ).2 b j hs
  · exfalso
    have hc := count hσK .ub
    rw [hub, List.countP_eq_zero] at hc
    have hmem : (⟨pc, .ub f⟩ : Event) ∈ (X.tr g).take K := by
      have : ((X.tr g).take K)[i]? = some ⟨pc, .ub f⟩ := by
        rw [List.getElem?_take, ite_eq_left hi]; exact he
      exact List.mem_of_getElem? this
    exact hc _ hmem (by simp [Proof.cls])

omit hp hX hw hFw in
/-- The state before a PV site, with its event. -/
private theorem back {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hl : k ≤ (X.tr g).length) (hs : pvSite d.site = true)
    (hs0 : d ≠ (code p L g (ent p L)).init) : ∃ i, k = i + 1 ∧
      ∃ e d0 n0, X.get (g, i) = some e ∧
      Frame.stateAt (thread p L) X g i = some (some (minj p L g d0 n0)) ∧
      PvPrevOf d0 e d.site := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.counted, Code.glue, Code.enter, exit, Startup.code, minj] at hσ
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have he : (X.tr g)[i]? = some ((X.tr g)[i]) := List.getElem?_eq_getElem (by omega)
  obtain ⟨d0, n0, h0, h1⟩ := mma_pred he hσ hs0
  exact ⟨i, rfl, _, d0, n0, he, h0, pred_pv h1 hs⟩

/-- **A PV MMA's predecessor**: an election before step 0, else the step before, with polls
between. -/
theorem pv_prev {k st u : Nat} {j : Fin 8} (hq : Tm.Pv L X g k st u j) :
    (j = 0 ∧ ∃ i pc mk inst ld, k = i + 1 ∧ X.get (g, i) = some ⟨pc, .elect mk inst ld⟩) ∨
      ∃ i j', i < k ∧ j'.val + 1 = j.val ∧ Tm.Pv L X g i st u j' ∧
        ∀ i', i < i' → i' < k → ∃ pc l q ok acq sc, X.get (g, i') = some ⟨pc, .wait l q ok acq sc⟩
    := by
  obtain ⟨d, n, b, hσ, hs, rfl, hlost, hub, -⟩ := pv_state hp hX hFw hw hq
  obtain ⟨pc, db, he⟩ := hq.issue
  have hl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1
  -- a step of the block before, with polls between
  have key : ∀ {i : Nat} {d0 : D} {n0 : Cls → Nat} {j' : Fin 8} {e : Event}, i < k →
      X.get (g, i) = some e → Frame.stateAt (thread p L) X g i = some (some (minj p L g d0 n0)) →
      d0.site = .pv b j' → j'.val + 1 = j.val →
      (∀ i', i < i' → i' < k → ∃ pc l q ok acq sc,
        X.get (g, i') = some ⟨pc, .wait l q ok acq sc⟩) →
      ∃ i j', i < k ∧ j'.val + 1 = j.val ∧ Tm.Pv L X g i (b.val % 2) u j' ∧
        ∀ i', i < i' → i' < k → ∃ pc l q ok acq sc,
          X.get (g, i') = some ⟨pc, .wait l q ok acq sc⟩ := by
    intro i d0 n0 j' e hi hei hσi hsi hj' hbt
    obtain ⟨u', hu'⟩ := pv_of_site hp hX hFw hw hσ hub hi hσi hei hsi
    refine ⟨i, j', hi, hj', ?_, hbt⟩
    -- no commit between, so one tile
    have hsame : Tm.sCommits L X g (b.val % 2) k = Tm.sCommits L X g (b.val % 2) i := by
      unfold Tm.sCommits
      have h : ∀ t, i ≤ t → t ≤ k →
          ((X.tr g).take t).countP (commitsTo (Tm.sFull L (g / L.block) (b.val % 2))) =
            ((X.tr g).take i).countP (commitsTo (Tm.sFull L (g / L.block) (b.val % 2))) := by
        intro t ht
        induction t, ht using Nat.le_induction with
        | base => exact fun _ => rfl
        | succ t ht ih =>
          intro htk
          rw [← ih (by omega)]
          rcases Nat.lt_or_eq_of_le ht with h1 | rfl
          · obtain ⟨pc', l, q, ok, acq, sc, hw'⟩ := hbt t h1 (by omega)
            have hw'' : (X.tr g)[t]? = _ := hw'
            rw [List.take_add_one, hw'', Option.toList_some, List.countP_append]
            simp [commitsTo]
          · obtain ⟨_, _, e'⟩ := hu'.issue
            have e'' : (X.tr g)[i]? = _ := e'
            rw [List.take_add_one, e'', Option.toList_some, List.countP_append]
            simp [commitsTo]
      exact h k (by omega) le_rfl
    have h1 := hq.com
    have h2 := hu'.com
    obtain rfl : u' = u := by omega
    exact hu'
  -- the polls of the second P-full barrier
  have hmw : ∀ t, t ≤ k → ∀ d0 n0,
      Frame.stateAt (thread p L) X g t = some (some (minj p L g d0 n0)) → d0.site = .mw b true →
      (∀ i', t ≤ i' → i' < k → ∃ pc l q ok acq sc,
        X.get (g, i') = some ⟨pc, .wait l q ok acq sc⟩) →
      ∃ i d1 n1 e, i < t ∧ X.get (g, i) = some e ∧
        Frame.stateAt (thread p L) X g i = some (some (minj p L g d1 n1)) ∧ d1.site = .pv b 5 ∧
        ∀ i', i < i' → i' < k → ∃ pc l q ok acq sc,
          X.get (g, i') = some ⟨pc, .wait l q ok acq sc⟩ := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht d0 n0 hσ0 hs0 hbt
      obtain ⟨i, rfl, e, d1, n1, hei, hσ1, hpr⟩ := back hσ0 (by omega)
        (by rw [hs0]; rfl) (by rintro rfl; simp [code] at hs0)
      rw [hs0] at hpr
      rcases hpr with h | ⟨h, l, q, ok, acq, sc, hk⟩
      · exact ⟨i, d1, n1, e, by omega, hei, hσ1, h, fun i' h1 h2 => hbt i' (by omega) h2⟩
      · obtain ⟨i2, d2, n2, e2, h1, h2, h3, h4, h5⟩ := ih i (by omega) (by omega) d1 n1 hσ1 h
          (fun i' h1 h2 => by
            rcases Nat.lt_or_eq_of_le h1 with h1 | rfl
            · exact hbt i' (by omega) h2
            · obtain ⟨pc', kd⟩ := e
              simp only at hk
              subst hk
              exact ⟨_, _, _, _, _, _, hei⟩)
        exact ⟨i2, d2, n2, e2, by omega, h2, h3, h4, h5⟩
  obtain ⟨i, rfl, e, d0, n0, hei, hσ0, hpr⟩ := back hσ (by omega)
    (by rw [hs]; rfl) (by rintro rfl; simp [code] at hs)
  rw [hs] at hpr
  rcases hpr with ⟨hj, -, mk, inst, ld, hk⟩ | ⟨rfl, hs0, l, q, ok, acq, sc, hk⟩ |
    ⟨j', hj', -, hs0⟩
  · obtain ⟨pc', kd⟩ := e
    simp only at hk
    subst hk
    exact .inl ⟨hj, i, _, _, _, _, rfl, hei⟩
  · right
    obtain ⟨i2, d2, n2, e2, h1, h2, h3, h4, h5⟩ := hmw i (by omega) d0 n0 hσ0 hs0
      (fun i' h1 h2 => by
        obtain rfl : i' = i := by omega
        obtain ⟨pc', kd⟩ := e
        simp only at hk
        subst hk
        exact ⟨_, _, _, _, _, _, hei⟩)
    exact key (by omega) h2 h3 h4 rfl h5
  · right
    exact key (by omega) hei hσ0 hs0 hj' (fun i' h1 h2 => by omega)

/-- **The PV MMAs of a tile are in the order of their steps.** -/
theorem pv_order {st u : Nat} : ∀ (n : Nat) {k k' : Nat} {j j' : Fin 8}, j'.val = n →
    Tm.Pv L X g k st u j → Tm.Pv L X g k' st u j' → k < k' → j.val < j'.val := by
  intro n
  induction n with
  | zero =>
    intro k k' j j' hj hq hq' hlt
    exfalso
    rcases pv_prev hp hX hFw hw hq' with ⟨-, i, pc, mk, inst, ld, rfl, he⟩ | ⟨i, j1, -, h1, -⟩
    · obtain ⟨R, hR, hE⟩ := pv_elections hp hX hFw hw hq
      obtain ⟨R', hR', hE'⟩ := pv_elections hp hX hFw hw hq'
      obtain rfl := hR.unique hR'
      have hne : k ≠ i := by
        rintro rfl
        obtain ⟨_, _, e⟩ := hq.issue
        rw [he] at e
        cases e
      have hmono := (List.take_sublist_take_left (l := X.tr g)
        (show k ≤ i by omega)).countP_le (p := isElectEv)
      have h1 : elections X g (i + 1) = elections X g i + 1 := by
        unfold elections
        have he' : (X.tr g)[i]? = _ := he
        rw [List.take_add_one, he', Option.toList_some, List.countP_append]
        simp [isElectEv]
      unfold elections at *
      omega
    · omega
  | succ n ih =>
    intro k k' j j' hj hq hq' hlt
    rcases pv_prev hp hX hFw hw hq' with ⟨h0, -⟩ | ⟨i, j1, hi, hj1, hq1, hbt⟩
    · rw [h0] at hj; cases hj
    · rcases Nat.lt_trichotomy k i with h | rfl | h
      · have := ih (by omega) hq hq1 h
        omega
      · obtain ⟨-, -, rfl⟩ := pv_eq hq hq1
        omega
      · exfalso
        obtain ⟨pc, l, q, ok, acq, sc, he⟩ := hbt k h hlt
        obtain ⟨_, _, e⟩ := hq.issue
        rw [he] at e
        cases e

/-- A step of a tile is one MMA. -/
theorem pv_unique {st u k k' : Nat} {j : Fin 8} (hq : Tm.Pv L X g k st u j)
    (hq' : Tm.Pv L X g k' st u j) : k = k' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have := pv_order hp hX hFw hw _ rfl hq hq' h
    omega
  · exact h
  · have := pv_order hp hX hFw hw _ rfl hq' hq h
    omega

omit hp hX hFw hw in
/-- A stopped event is not before a state. -/
private theorem no_ub {K t : Nat} {σ : (glued p L g).D} {n' : Cls → Nat} {pc : Nat} {f : Fault}
    (hσK : Frame.stateAt (thread p L) X g K = some (some (σ, n'))) (hub : n' .ub = 0) (ht : t < K)
    (he : X.get (g, t) = some ⟨pc, .ub f⟩) : False := by
  have hc := count hσK .ub
  rw [hub, List.countP_eq_zero] at hc
  have hmem : (⟨pc, .ub f⟩ : Event) ∈ (X.tr g).take K := by
    have : ((X.tr g).take K)[t]? = some ⟨pc, .ub f⟩ := by
      rw [List.getElem?_take, ite_eq_left ht]; exact he
    exact List.mem_of_getElem? this
  exact hc _ hmem (by simp [Proof.cls])

/-- **A step's successor**: an MMA or a commit after step `j` follows step `j + 1` or is it. -/
theorem pv_next {i K pcK st u : Nat} {kK : TcKind} {j j' : Fin 8} (hq : Tm.Pv L X g i st u j)
    (hj : j.val + 1 = j'.val) (hi : i < K) (heK : X.get (g, K) = some ⟨pcK, .tc kK⟩)
    (hk : (∃ d s acc mask, kK = .mma d s acc mask) ∨ ∃ s, kK = .commit s) :
    ∃ i', i < i' ∧ i' ≤ K ∧ Tm.Pv L X g i' st u j' := by
  obtain ⟨d, n, b, hσ, hs, rfl, -⟩ := pv_state hp hX hFw hw hq
  obtain ⟨pc, db, he⟩ := hq.issue
  obtain ⟨dK, nK, hσK, -, hwsK, -, hubK, hevK⟩ := win_state hp hX hFw hw heK hk
  have hlK := (List.getElem?_eq_some_iff.mp (show (X.tr g)[K]? = _ from heK)).1
  -- the site after a step is the next one's, after polls
  have hsite : ∃ i' d' n', i < i' ∧ i' ≤ K ∧ d'.site = .pv b j' ∧
      Frame.stateAt (thread p L) X g i' = some (some (minj p L g d' n')) ∧
      ∀ t, i < t → t < i' → ∃ pc l q ok acq sc, X.get (g, t) = some ⟨pc, .wait l q ok acq sc⟩ := by
    obtain ⟨d1, hd1, hσ1⟩ := mma_fwd hσ he hi hσK
    obtain ⟨site, v⟩ := d
    simp only at hs
    subst hs
    simp only [succ, Option.some.injEq] at hd1
    subst hd1
    by_cases h5 : j.val = 5
    · simp only [h5, ↓reduceIte] at hσ1
      have hj6 : j' = 6 := Fin.ext (by rw [← hj, h5]; rfl)
      subst hj6
      -- the polls
      have key : ∀ (f t : Nat) (d2 : D) (n2 : Cls → Nat), K - t = f → i < t → t ≤ K →
          d2.site = .mw b true → Frame.stateAt (thread p L) X g t =
            some (some (minj p L g d2 n2)) →
          (∀ t', i < t' → t' < t → ∃ pc l q ok acq sc,
            X.get (g, t') = some ⟨pc, .wait l q ok acq sc⟩) →
          ∃ i' d' n', i < i' ∧ i' ≤ K ∧ d'.site = .pv b 6 ∧
            Frame.stateAt (thread p L) X g i' = some (some (minj p L g d' n')) ∧
            ∀ t, i < t → t < i' → ∃ pc l q ok acq sc,
              X.get (g, t) = some ⟨pc, .wait l q ok acq sc⟩ := by
        intro f
        induction f with
        | zero =>
          intro t d2 n2 hf hit htK hs2 hσ2 hbt
          exfalso
          obtain rfl : t = K := by omega
          have hEq := hσ2.symm.trans hσK
          simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq,
            heq_eq_eq, true_and] at hEq
          obtain ⟨rfl, -⟩ := hEq
          simp only [Ev, hs2] at hevK
          rcases hevK with ⟨ok, h⟩ | ⟨f, h⟩ <;> cases h
        | succ f ih =>
          intro t d2 n2 hf hit htK hs2 hσ2 hbt
          have htlt : t < K := by omega
          obtain ⟨e, het⟩ : ∃ e, X.get (g, t) = some e :=
            ⟨_, List.getElem?_eq_getElem (show t < (X.tr g).length by omega)⟩
          obtain ⟨d3, hd3, hσ3⟩ := mma_fwd hσ2 het htlt hσK
          have hev := (mfired hp hX het hσ2).1
          obtain ⟨pce, kd⟩ := e
          obtain ⟨site2, v2⟩ := d2
          simp only at hs2
          subst hs2
          simp only [Ev] at hev
          rcases hev with ⟨ok, rfl⟩ | ⟨f', rfl⟩
          · have hbt' : ∀ t', i < t' → t' < t + 1 → ∃ pc l q ok acq sc,
                X.get (g, t') = some ⟨pc, .wait l q ok acq sc⟩ := fun t' h1 h2 => by
              rcases Nat.lt_or_eq_of_le (show t' ≤ t by omega) with h3 | rfl
              · exact hbt t' h1 h3
              · exact ⟨_, _, _, _, _, _, het⟩
            simp only [succ, ↓reduceIte, Option.some.injEq] at hd3
            subst hd3
            cases ok
            · exact ih (t + 1) _ _ (by omega) (by omega) htlt rfl hσ3 hbt'
            · exact ⟨t + 1, _, _, by omega, htlt, rfl, hσ3, hbt'⟩
          · exact (no_ub hσK hubK htlt het).elim
      exact key _ (i + 1) _ _ rfl (by omega) hi rfl hσ1 (fun t' h1 h2 => by omega)
    · have h7 : j.val ≠ 7 := by have := j'.isLt; omega
      simp only [h5, h7, ↓reduceIte] at hσ1
      refine ⟨i + 1, _, _, by omega, hi, ?_, hσ1, fun t h1 h2 => by omega⟩
      have : j + 1 = j' := by
        apply Fin.ext
        rw [← hj]
        have key : ∀ j : Fin 8, j.val ≠ 7 → (j + 1).val = j.val + 1 := by decide
        exact key j h7
      rw [this]
  obtain ⟨i', d', n', hii, hiK, hs', hσ', hbt⟩ := hsite
  obtain ⟨u', hu'⟩ : ∃ u', Tm.Pv L X g i' (b.val % 2) u' j' := by
    rcases Nat.lt_or_eq_of_le hiK with hlt | rfl
    · obtain ⟨e, hei⟩ : ∃ e, X.get (g, i') = some e :=
        ⟨_, List.getElem?_eq_getElem (show i' < (X.tr g).length by omega)⟩
      exact pv_of_site hp hX hFw hw hσK hubK hlt hσ' hei hs'
    · obtain ⟨d2, n2, hσ2, hJ2, -⟩ := win_state hp hX hFw hw heK hk
      have hEq := hσ'.symm.trans hσ2
      simp only [minj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
        true_and] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      exact (mma_at_site hp hX hw heK hσ2 hJ2).2 b j' hs'
  refine ⟨i', hii, hiK, ?_⟩
  rcases pv_prev hp hX hFw hw hu' with ⟨h0, -⟩ | ⟨i2, j2, h1, h2, h3, h4⟩
  · rw [h0] at hj; cases hj
  · obtain rfl : i2 = i := by
      rcases Nat.lt_trichotomy i2 i with h | h | h
      · obtain ⟨_, _, _, _, _, _, he2⟩ := h4 i h hii
        rw [he] at he2; cases he2
      · exact h
      · obtain ⟨_, _, _, _, _, _, he2⟩ := hbt i2 h h1
        obtain ⟨_, _, he3⟩ := h3.issue
        rw [he3] at he2; cases he2
    obtain ⟨-, rfl, -⟩ := pv_eq hq h3
    exact hu'

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
