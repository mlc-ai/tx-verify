-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Bar12Ph

@[expose] public section

/-! # Barrier 12 of warps 4–11 on the time table

The phase of a state (`ph`, `Common/Bar12Ph.lean`): `1` at a role's closing `barrier.sync 12`
(the MMA and TMA lanes' `outBar`, the index warp's, warpgroup 2's and the idle code's `bar`), `2`
after it (the exit, the idle code's `ret`), `0` elsewhere. For a lane of warps 4–11:

* `ph_time`, `ph_ev` (`Common/Bar12Ph.lean`): a state of phase `0` is before `endSlot`, of phase
  `1` at it, of phase `2` after it; a barrier-12 event is fired at phase `1`, an `exit` at `2`;
* `ph_step`: a step from phase `0` stays at most at phase `1` (the early returns of a CTA beyond
  the batch do not happen), from phase `1` or `2` it reaches phase `2`;
* `ph_cnt`: so a prefix has no barrier-12 event and its state is of phase at most `1`, or it has
  one and its state is of phase `2`.

Hence `bar12_at`: a barrier-12 event is at `endSlot` with none before it, and `bar12_lag`: a lane
without a barrier-12 event has not exited and is no later than `endSlot`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The phase along a step -/

theorem idle_first (hp : Pre P L m) : idleFirst P L g ≠ .ret := by
  unfold idleFirst idleAfterA
  simp only [batch_in hp g, Bool.false_eq_true, ite_false]
  split_ifs <;> simp

/-- The head's entry into a sub-role (or its own state) is of phase at most `1`. -/
theorem head_enter_ph (hp : Pre P L m) (s : Wg1.Site) (n : Cls → Nat) :
    ph P L g (.inr ⟨.inl .wg1, Code.enter (wg1HeadCode P L g)
      (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g))
      (Code.gatedExit (wg1Enter P L g) (subSel P L g)) s⟩, n) ≤ 1 := by
  unfold Code.enter
  split
  · next x _ =>
    rcases x with j | r
    · cases j with
      | mma => simp [ph, fragPh, wg1Ph, subPh, mmaPh, Mma.init]
      | tma => simp [ph, fragPh, wg1Ph, subPh, tmaPh, Tma.init]
      | index =>
        have h := ix_first (P := P) (L := L) (g := g) hp
        show ixPh (Index.ofC (ixFirst P L g)).site ≤ 1
        unfold ixPh
        split <;> simp_all
      | idle =>
        have h := idle_first (P := P) (L := L) (g := g) hp
        show idlePh (idleFirst P L g) ≤ 1
        unfold idlePh
        split <;> simp_all
    · simp [ph, fragPh, wg1Ph]
  · simp [ph, fragPh, wg1Ph]

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **The phase along a step**: from `0` at most `1`, from `1` or `2` exactly `2`. -/
theorem ph_step (hp : Pre P L m) {σ σ' : (thread P L g).D} {e : Event}
    (hn : (thread P L g).next σ e = some (some σ')) :
    (ph P L g σ = 0 → ph P L g σ' ≤ 1) ∧ (1 ≤ ph P L g σ → ph P L g σ' = 2) := by
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · rw [next_startup] at hn
    obtain ⟨d', -, rfl⟩ := map_some hn
    refine ⟨fun _ => ?_, fun h => by simp [ph] at h⟩
    unfold Code.enter
    split
    · next x _ => rcases x with i | r <;> [cases i; skip] <;> simp [ph, fragPh, wg1Ph, Code.enter,
        Code.gatedExit, wg1Enter, Wg1.exitOf, deqPh]
    · simp [ph]
  · cases i with
    | wg0 =>
      rw [next_frag] at hn
      obtain ⟨d', -, rfl⟩ := map_some hn
      simp [ph, fragPh]
    | dequant =>
      rw [next_frag] at hn
      obtain ⟨d', hs, rfl⟩ := map_some hn
      have hs' : Dequant.Control.succ P L g d e = some (some d') := hs
      show (deqPh d.site = 0 → deqPh d'.site ≤ 1) ∧ (1 ≤ deqPh d.site → deqPh d'.site = 2)
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · have hb : d.site ≠ .bar := fun h => by simp [deqPh, h] at h0
        have hx : d.site ≠ .exit := fun h => by simp [deqPh, h] at h0
        have := deq_noExit hp hs' hb hx
        unfold deqPh; split <;> simp_all
      · obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
        cases site <;> simp [deqPh] at h1 <;> simp [Dequant.Control.succ] at hs' <;>
          subst hs' <;> rfl
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · rw [next_head] at hn
        obtain ⟨s', -, rfl⟩ := map_some hn
        exact ⟨fun _ => head_enter_ph hp s' _, fun h => by simp [ph, fragPh, wg1Ph] at h⟩
      · rw [next_sub] at hn
        obtain ⟨d', hs, rfl⟩ := map_some hn
        cases j with
        | mma =>
          have hs' : Mma.succ P L g d e = some (some d') := hs
          cases hb : subBack P L g .mma d' with
          | some p =>
            have hp' : p = .idle := by
              simp only [subBack] at hb; split_ifs at hb; exact (Option.some.inj hb).symm
            have hl : ∃ i, d'.site = .leave i := by
              simp only [subBack] at hb; split_ifs at hb with h; exact ⟨_, h⟩
            simp only [Code.backEnter, hb]
            refine ⟨fun _ => head_enter_ph hp p _, fun h1 => ?_⟩
            obtain ⟨i, hi⟩ := hl
            obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
            cases site <;> simp [ph, fragPh, wg1Ph, subPh, mmaPh] at h1 <;>
              simp [Mma.succ] at hs' <;> subst hs' <;> simp at hi
          | none =>
            simp only [Code.backEnter, hb]
            show (mmaPh d.site = 0 → mmaPh d'.site ≤ 1) ∧ (1 ≤ mmaPh d.site → mmaPh d'.site = 2)
            refine ⟨fun h0 => ?_, fun h1 => ?_⟩
            · have hb : d.site ≠ .outBar := fun h => by simp [mmaPh, h] at h0
              have hx : d.site ≠ .exit := fun h => by simp [mmaPh, h] at h0
              have := mma_noExit hp hs' hb hx
              unfold mmaPh; split <;> simp_all
            · obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
              cases site <;> simp [mmaPh] at h1 <;> simp [Mma.succ] at hs' <;> subst hs' <;> rfl
        | tma =>
          have hs' : Tma.succ P L g d e = some (some d') := hs
          cases hb : subBack P L g .tma d' with
          | some p =>
            have hl : ∃ i, d'.site = .leave i := by
              simp only [subBack] at hb; split_ifs at hb with h; exact ⟨_, h⟩
            simp only [Code.backEnter, hb]
            refine ⟨fun _ => head_enter_ph hp p _, fun h1 => ?_⟩
            obtain ⟨i, hi⟩ := hl
            obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
            cases site <;> simp [ph, fragPh, wg1Ph, subPh, tmaPh] at h1 <;>
              simp [Tma.succ] at hs' <;> subst hs' <;> simp at hi
          | none =>
            simp only [Code.backEnter, hb]
            show (tmaPh d.site = 0 → tmaPh d'.site ≤ 1) ∧ (1 ≤ tmaPh d.site → tmaPh d'.site = 2)
            refine ⟨fun h0 => ?_, fun h1 => ?_⟩
            · have hb : d.site ≠ .outBar := fun h => by simp [tmaPh, h] at h0
              have hx : d.site ≠ .exit := fun h => by simp [tmaPh, h] at h0
              have := tma_noExit hp hs' hb hx
              unfold tmaPh; split <;> simp_all
            · obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
              cases site <;> simp [tmaPh] at h1 <;> simp [Tma.succ] at hs' <;> subst hs' <;> rfl
        | index =>
          have hs' : Index.succ P L g d e = some (some d') := hs
          simp only [Code.backEnter, subBack]
          show (ixPh d.site = 0 → ixPh d'.site ≤ 1) ∧ (1 ≤ ixPh d.site → ixPh d'.site = 2)
          refine ⟨fun h0 => ?_, fun h1 => ?_⟩
          · have hb : d.site ≠ .bar := fun h => by simp [ixPh, h] at h0
            have hx : d.site ≠ .exit := fun h => by simp [ixPh, h] at h0
            have := ix_noExit hs' hb hx
            unfold ixPh; split <;> simp_all
          · obtain ⟨site, el, ac, c⟩ := d
            cases site <;> simp [ixPh] at h1 <;> simp [Index.succ] at hs' <;> subst hs' <;> rfl
        | idle =>
          have hs' : Wg1.isucc P d e = some (some d') := hs
          simp only [Code.backEnter, subBack]
          show (idlePh d = 0 → idlePh d' ≤ 1) ∧ (1 ≤ idlePh d → idlePh d' = 2)
          cases d <;> simp only [Wg1.isucc, Wg1.afterNc] at hs' <;> (repeat' split at hs') <;>
            simp only [Option.some.injEq, reduceCtorEq] at hs' <;> subst hs' <;>
            simp [idlePh, idleAfterA] <;> split_ifs <;> simp
      · rw [next_frag] at hn
        simp [frag, wg1Code, Code.roleLoop, Code.loopGlue, Code.withStubsAt, Code.stopAt] at hn
  · simp [thread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, Code.stop] at hn

/-! ### Along the trace -/

theorem barId12_kind {e : Event} (h : Execution.isBarId 12 e = true) :
    ∃ c md, e.kind = .bar 12 c md := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar id c md =>
    simp only [Execution.isBarId, beq_iff_eq] at h
    subst h
    exact ⟨c, md, rfl⟩
  | _ => simp [Execution.isBarId] at h

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X) (hw : 4 ≤ warp L g)
include hp hX hFw hnu hw

/-- **A prefix has no barrier-12 event and a state of phase at most `1`, or one and a state of
phase `2`.** -/
theorem ph_cnt : ∀ i, i ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread P L) X g i = some (some σ) →
    (((X.tr g).take i).countP (Execution.isBarId 12) = 0 ∧ ph P L g σ ≤ 1) ∨
      (0 < ((X.tr g).take i).countP (Execution.isBarId 12) ∧ ph P L g σ = 2) := by
  intro i
  induction i with
  | zero =>
    intro _ σ h
    rw [Frame.stateAt_zero] at h
    cases h
    left
    simp [ph, Code.enter, Code.gatedExit, startupEnter, Startup.exitOf]
  | succ i ih =>
    intro hl σ' h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨σ, hσ, hn⟩ := prev_state he h
    obtain ⟨σ0, hσ0, hJ, hi, hev, -⟩ := ev_at hp hX hFw he (noUb_kind hnu he)
    rw [hσ] at hσ0
    cases hσ0
    have hc : ((X.tr g).take (i + 1)).countP (Execution.isBarId 12) =
        ((X.tr g).take i).countP (Execution.isBarId 12) +
          if Execution.isBarId 12 e = true then 1 else 0 := by
      rw [List.take_add_one, he, Option.toList_some, List.countP_append]
      split_ifs with hb <;> simp [hb]
    obtain ⟨hE1, hE2⟩ := ph_ev hw hJ hi hev
    obtain ⟨hS0, hS1⟩ := ph_step hp hn
    rw [hc]
    rcases ih (by omega) σ hσ with ⟨h0, hph⟩ | ⟨h0, hph⟩
    · by_cases hb : Execution.isBarId 12 e = true
      · obtain ⟨c, md, hk⟩ := barId12_kind hb
        have h1 : ph P L g σ = 1 := by
          rcases hE1 (.inr ⟨c, md, hk⟩) with ⟨-, hx⟩ | h
          · rw [hk] at hx; cases hx
          · exact h
        exact .inr ⟨by simp [hb], hS1 (by omega)⟩
      · have h1 : ph P L g σ = 0 := by
          by_contra hne
          have := hE2 (by omega)
          simp [Execution.isBarId, this] at hb
        exact .inl ⟨by simp [hb, h0], hS0 h1⟩
    · exact .inr ⟨by omega, hS1 (by omega)⟩

/-- **A barrier-12 event of a lane of warps 4–11** is at `endSlot`, with none before it. -/
theorem bar12_at {j pc : Nat} {c : Option Nat} {md : BarMode} {σ : (thread P L g).D}
    (he : X.get (g, j) = some ⟨pc, .bar 12 c md⟩)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ)) :
    time P L g σ = endSlot ∧ ((X.tr g).take j).countP (Execution.isBarId 12) = 0 := by
  obtain ⟨σ0, hσ0, hJ, hi, hev, -⟩ := ev_at hp hX hFw he (noUb_kind hnu he)
  rw [hσ] at hσ0
  cases hσ0
  have h1 : ph P L g σ = 1 := by
    rcases (ph_ev hw hJ hi hev).1 (.inr ⟨c, md, rfl⟩) with ⟨-, hx⟩ | h
    · cases hx
    · exact h
  have hjl : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  refine ⟨(ph_time hnu hw hσ hJ).2.1 h1, ?_⟩
  rcases ph_cnt hp hX hFw hnu hw j hjl σ hσ with ⟨h0, -⟩ | ⟨-, h2⟩
  · exact h0
  · omega

/-- **After a barrier-12 event of a lane of warps 4–11** the state is later. -/
theorem bar12_after (hg : g < L.threads) {j pc : Nat} {c : Option Nat} {md : BarMode}
    {σ σ' : (thread P L g).D}
    (he : X.get (g, j) = some ⟨pc, .bar 12 c md⟩)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ))
    (hσ' : Frame.stateAt (thread P L) X g (j + 1) = some (some σ')) :
    time P L g σ < time P L g σ' := by
  obtain ⟨σ0, hσ0, hJ, hi, hev, -⟩ := ev_at hp hX hFw he (noUb_kind hnu he)
  rw [hσ] at hσ0
  cases hσ0
  have h1 : ph P L g σ = 1 := by
    rcases (ph_ev hw hJ hi hev).1 (.inr ⟨c, md, rfl⟩) with ⟨-, hx⟩ | h
    · cases hx
    · exact h
  obtain ⟨σm, hσm, hn⟩ := prev_state he hσ'
  rw [hσ] at hσm
  cases hσm
  have h2 := (ph_step hp hn).2 (by rw [h1])
  have hJ' := (follow_iff.mp hFw g hg (j + 1)).2 σ' hσ'
  have := (ph_time hnu hw hσ' hJ').2.2 h2
  rw [(ph_time hnu hw hσ hJ).2.1 h1]
  exact this

/-- **A lane of warps 4–11 without a barrier-12 event** has not exited and is no later than
`endSlot`. -/
theorem bar12_lag (hg : g < L.threads) (h0 : (X.tr g).countP (Execution.isBarId 12) = 0) :
    (∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (timed P L) X g ≤ endSlot := by
  have hle : ∀ i, ((X.tr g).take i).countP (Execution.isBarId 12) = 0 := fun i => by
    have := (List.take_sublist i (X.tr g)).countP_le (p := Execution.isBarId 12)
    omega
  have hcnt := ph_cnt hp hX hFw hnu hw
  refine ⟨fun k pc hx => ?_, ?_⟩
  · obtain ⟨σ, hσ, hJ, hi, hev, -⟩ := ev_at hp hX hFw hx (noUb_kind hnu hx)
    have hkl : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1.le
    have h2 : ph P L g σ = 2 := by
      rcases (ph_ev hw hJ hi hev).1 (.inl rfl) with ⟨h, -⟩ | h
      · exact h
      · have := (ph_ev hw hJ hi hev).2 h
        cases this
    rcases hcnt k hkl σ hσ with ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · rw [hle k] at h
      omega
  refine time_last (Q := fun t => t ≤ endSlot) (Nat.zero_le _) (fun σ hs => ?_)
    (fun σ f hs hf _ => ?_)
  · have hJ := (follow_iff.mp hFw g hg _).2 σ hs
    rcases hcnt _ (Nat.le_refl _) σ hs with ⟨-, h⟩ | ⟨h, -⟩
    · have ht := ph_time hnu hw hs hJ
      rcases Nat.lt_or_ge (ph P L g σ) 1 with h' | h'
      · have := ht.1 (by omega); omega
      · have := ht.2.1 (by omega); omega
    · rw [hle] at h
      omega
  · have hget : X.get (g, (X.tr g).length - 1) = some f := hf
    obtain ⟨σ0, hσ0, hJ, hi, hev, -⟩ := ev_at hp hX hFw hget (noUb_kind hnu hget)
    rw [hs] at hσ0
    cases hσ0
    have hfl : (X.tr g).length - 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).1
    rcases hcnt _ hfl.le σ hs with ⟨-, h⟩ | ⟨h, -⟩
    · have h0' : ph P L g σ = 0 := by
        by_contra hne
        have hk := (ph_ev hw hJ hi hev).2 (by omega)
        have hpos : 0 < (X.tr g).countP (Execution.isBarId 12) :=
          List.countP_pos_iff.mpr ⟨f, List.mem_of_getElem? hf, by
            obtain ⟨pc, kd⟩ := f
            simp only at hk
            subst hk
            rfl⟩
        omega
      have := (ph_time hnu hw hs hJ).1 h0'
      omega
    · rw [hle] at h
      omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
