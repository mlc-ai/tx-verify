-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiPart2
public import Kernels.InklingRelDecode.Proof.Thread.EpiStores

@[expose] public section

/-! # The poll of `o_final`

Every thread of the epilogue polls the `o_final` barrier first (`mbarrier.try_wait.parity`,
pc 2565 and its poll branch `@!complete bra.uni` back to the poll, pc 2566), also the thread
with `num_iters < 1` (the second kernel fix: the poll no longer sits inside `if num_iters > 0`).
A failed poll polls again. After a successful poll the code runs the 33 local instructions of
pcs 2567-2599 (`p2_run`: the zero pair, the zero test, the 31 copies) and the branch on `%p173`
(pc 2600):

* for `num_iters >= 1` (`sk = false`) the selection and the reciprocal (`wait_ok_steps`) lead to
  the broadcast (pc 2603);
* for `num_iters < 1` (`sk = true`) the branch goes to pc 2674 and the local code of the stores
  (`seg_w4`, `seg_skipLse`, `seg_skip_from`) to the first store site `D.stores`
  (`skip_to_stores`).

A thread whose zero test faults, or (for `num_iters >= 1`) whose reciprocal faults, is dead. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {t u : TState} {e : Event} {ins : Instr}

/-! ### The state of the `num_iters < 1` path at the first store -/

/-- The invariant at the first store site of the `num_iters < 1` path. -/
theorem inv_stores (d : D) (hi : Inv d) (hsk : d.sk = true) : Inv { d with site := d.stores } := by
  have ho : d.o = [] := hi.sk hsk
  obtain ⟨s, pr, o, sk⟩ := d
  simp only at hsk ho
  subst hsk ho
  have hpre : ∀ s : Site, (s = .stLse ∨ s = .stO 0 ∨ s = .bar1) →
      (s = .shfl ∨ s = .ld ∨ s = .waitLd → true = false) := by
    intro s hs h
    rcases hs with rfl | rfl | rfl <;> rcases h with h | h | h <;> cases h
  have hok := hi.ok
  have hla := hi.lane
  by_cases hrv : pr.rv = true
  · by_cases hl : pr.lead = true
    · have e : D.stores ⟨s, pr, [], true⟩ = .stLse := by simp [D.stores, hrv, hl]
      rw [e]
      exact ⟨hok, (fun _ h => absurd h (by simp)), (fun _ => rfl),
        hpre _ (Or.inl rfl), (fun _ => hrv), (fun _ => hl), (fun h => by cases h), hla⟩
    · have e : D.stores ⟨s, pr, [], true⟩ = .stO 0 := by simp [D.stores, hrv, hl]
      rw [e]
      exact ⟨hok, (fun _ h => absurd h (by simp)), (fun _ => rfl),
        hpre _ (Or.inr (Or.inl rfl)), (fun _ => hrv), (fun h => by cases h),
        (fun h => by cases h), hla⟩
  · have e : D.stores ⟨s, pr, [], true⟩ = .bar1 := by simp [D.stores, hrv]
    rw [e]
    exact ⟨hok, (fun h => absurd h (by simp [LoadedSite])), (fun _ => rfl),
      hpre _ (Or.inr (Or.inr rfl)), (fun h => absurd h (by simp [StoreSite])),
      (fun h => by cases h), (fun h => by cases h), hla⟩

/-- **From pc 2674 to the first store site** of the `num_iters < 1` path: the row, the addresses
and the `LsePart` word, then the skipped stores. -/
theorem skip_to_stores (d : D) (hi : Inv d) {t : TState}
    (h : At t 2674 (factsAt 2674 d)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' (d.stores).pc (facts { d with site := d.stores }) := by
  have hok := hi.ok
  obtain ⟨t2, hr2, ht2⟩ := (seg_w4 (L := L) (g := g) d hok).rtg h
  cases hrv : d.pr.rv with
  | false =>
    obtain ⟨t3, hr3, ht3⟩ := (seg_skipLse (L := L) (g := g) d hok (by simp [hrv])).rtg ht2
    obtain ⟨t4, hr4, ht4⟩ := (seg_skip_from (L := L) (g := g) d hrv 31 (by omega)).rtg ht3
    have e : d.stores = .bar1 := by simp [D.stores, hrv]
    rw [e]
    exact ⟨t4, hr2.trans (hr3.trans hr4), ht4⟩
  | true =>
    cases hl : d.pr.lead with
    | false =>
      obtain ⟨t3, hr3, ht3⟩ := (seg_skipLse (L := L) (g := g) d hok (by simp [hl])).rtg ht2
      have e : d.stores = .stO 0 := by simp [D.stores, hrv, hl]
      rw [e]
      exact ⟨t3, hr2.trans hr3, ht3⟩
    | true =>
      have e : d.stores = .stLse := by simp [D.stores, hrv, hl]
      rw [e]
      exact ⟨t2, hr2, ht2⟩

/-! ### The facts across the part-2 run -/

theorem live2674_sub : ∀ r ∈ Flow.live 2674, r ∈ Flow.live 2600 := by decide +kernel

/-- The run's facts at the branch give the state's facts at pc 2674 for `num_iters < 1`. -/
theorem facts_skip {R : Nat → Option Value} (d : D) (hsk : d.sk = true)
    (h : Holds R (facts2 2600 d)) : Holds R (factsAt 2674 d) := by
  refine Flow.holds_of_pointwise fun r hr => ?_
  have h1 := holds_mem h (Flow.mem_factsFrom (val := valueP d) (live2674_sub r hr))
  rw [h1, valueP_sk d hsk]

theorem shfl_live : ∀ r ∈ Flow.live 2603, r = 1761 ∨
    (r ∈ Flow.live 2600 ∧ ¬ (2479 ≤ r ∧ r < 2511)) := by decide +kernel

/-- The facts at the broadcast after the selection and the reciprocal. -/
theorem holds_shfl {R : Nat → Option Value} (d : D)
    (h : Holds R ((1761, d.pr.inv) :: (1762, if d.pr.eq0 then one32 else d.pr.l) ::
      facts2 2600 d)) : Holds R (factsAt 2603 d) := by
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases shfl_live r hr with rfl | ⟨hv, hn⟩
  · exact h.1
  · have h1 := holds_mem h.2.2 (Flow.mem_factsFrom (val := valueP d) hv)
    rw [h1]
    rw [valueP_of_not hn]

/-! ### The poll -/

/-- **The poll of `o_final`**: a failed poll polls again; a successful one continues, after the
local code of pcs 2567-2600, to the first store site (`num_iters < 1`) or to the broadcast (after
the selection and the reciprocal); the thread is dead where the zero test, or for
`num_iters >= 1` the reciprocal, faults. -/
theorem step_wait (pr : Prm) (o : List Value) (sk : Bool) (hi : Inv ⟨.wait, pr, o, sk⟩)
    (h : At t (Site.wait).pc (facts ⟨.wait, pr, o, sk⟩))
    (hc : kernel.code[(Site.wait).pc]? = some ins)
    (hf : Fires (Site.wait).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g ⟨.wait, pr, o, sk⟩ e u := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_5)
  rw [← h.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  have hp : 2612 ∉ Flow.live Flow.mbarWait_5 := by table_decide
  have h1 := At.set (r := 2612) (v := .pred ok) h (facts_ne hp)
  rw [h.1]
  cases ok with
  | false =>
    obtain ⟨w, hr, hw⟩ := run_nbra (L := L) (g := g) Flow.code_2566 false h1
      (holds_mem h1.2.2.2.2 (List.mem_cons_self ..)) asms_bra (segFree (by omega))
    simp only [Bool.false_eq_true, ↓reduceIte] at hw
    exact .inl (.inr ⟨⟨.wait, pr, o, sk⟩, w, by simp [next], run_rtg hr, hw.mono hw.2.2.2.2.2, hi⟩)
  | true =>
    obtain ⟨w, hr, hw⟩ := run_nbra (L := L) (g := g) Flow.code_2566 true h1
      (holds_mem h1.2.2.2.2 (List.mem_cons_self ..)) asms_bra (segFree (by omega))
    simp only [↓reduceIte] at hw
    have hw2 : At w 2567 (facts2 2567 ⟨.wait, pr, o, sk⟩) :=
      hw.mono (facts2_of_wait ⟨.wait, pr, o, sk⟩ hw.2.2.2.2.2)
    obtain ⟨hs1, hs2⟩ := p2_run (L := L) (g := g) (⟨.wait, pr, o, sk⟩ : D) w hw2
    cases hsp : pr.setpOk with
    | false => exact .inr ⟨by simp [next, hsp], dead_of_run hr (hs2 (by simp [hsp]))⟩
    | true =>
      obtain ⟨t1, hr1, ht1⟩ := hs1 hsp
      obtain ⟨t2, hr2, ht2⟩ := seg_p2_bra (L := L) (g := g) (⟨.wait, pr, o, sk⟩ : D) t1 ht1
      have hrt : Relation.ReflTransGen (Tau kernel asms L g) _ t2 :=
        (run_rtg hr).trans ((run_rtg hr1).trans (run_rtg hr2))
      by_cases hsk : sk = true
      · subst hsk
        simp only [↓reduceIte] at ht2
        have ht3 : At t2 2674 (factsAt 2674 (⟨.wait, pr, o, true⟩ : D)) :=
          ht2.mono (facts_skip (⟨.wait, pr, o, true⟩ : D) rfl ht2.2.2.2.2)
        obtain ⟨t', hr', ht'⟩ := skip_to_stores (L := L) (g := g) (⟨.wait, pr, o, true⟩ : D)
          hi ht3
        exact .inl (.inr ⟨⟨D.stores ⟨.wait, pr, o, true⟩, pr, o, true⟩, t',
          by simp [next, hsp], hrt.trans hr', ht', inv_stores _ hi rfl⟩)
      · have hsk' : sk = false := by simpa using hsk
        subst hsk'
        simp only [Bool.false_eq_true, ↓reduceIte] at ht2
        have hl4 := hi.ok.l
        have hm : ∀ r, r ∈ Flow.live 2600 →
            (r, valueP ⟨.wait, pr, o, false⟩ r) ∈ facts2 2600 ⟨.wait, pr, o, false⟩ :=
          fun r hr => Flow.mem_factsFrom hr
        obtain ⟨hw1, hw2'⟩ := wait_ok_steps (L := L) (g := g) (u := t2)
          (F := facts2 2600 ⟨.wait, pr, o, false⟩) ⟨.wait, pr, o, false⟩ hl4 ht2
          (hm 178 (by decide +kernel)) (hm 1915 (by decide +kernel))
          (facts2_ne (by decide +kernel)) (facts2_ne (by decide +kernel))
        cases hok : pr.rcpOk with
        | true =>
          obtain ⟨t', hr', ht'⟩ := hw1 hok
          exact .inl (.inr ⟨⟨.shfl, pr, o, false⟩, t', by simp [next, hsp, hok],
            hrt.trans (run_rtg hr'),
            ht'.mono (holds_shfl ⟨.wait, pr, o, false⟩ ht'.2.2.2.2),
            inv_site hi _ (fun h => absurd h (by simp [LoadedSite]))
              (fun _ => rfl) (fun h => absurd h (by simp [StoreSite]))
              (fun h => absurd h (by simp))⟩)
        | false =>
          exact .inr ⟨by simp [next, hsp, hok],
            dead_of_run hr (dead_of_run hr1 (dead_of_run hr2 (hw2' hok)))⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
