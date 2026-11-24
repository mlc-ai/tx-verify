-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5BCount
public import Kernels.InklingRelDecode.Proof.Thread.Lk5BAux

@[expose] public section

/-!
# The `bar24` states of a default-partition thread, from the CTA's decisions

`Dc Q L X c j` is the decision of iteration `j` of CTA `c` (some default thread of the CTA keeps
the maximum at `shfl12` of `j`). With `DecAgree c j` every default thread of the CTA at `shfl12`
of `j` goes to `bar20` exactly when `Dc c j` (`dec_iff`). Then the number of `bar24` states of a
thread before a state is `Lk5B.Rval` of the state:

* `rinv_all`: exactly, at every state, when every iteration's decision agrees;
* `rlow`: when the decisions of the iterations below `I` agree, exactly at the states of the
  iterations below `I` and of iteration `I` before its decision (`Bnd I`), and at least the number
  of rescale iterations below `I` at the other states.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)
open Classical

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The decision of an iteration -/

/-- **The decision of iteration `j` of CTA `c`**: some default thread of the CTA keeps the
maximum at `shfl12` of `j`. -/
def Dc (Q : Params) (L : Launch) (X : Execution) (c j : Nat) : Prop :=
  ∃ (g k : Nat) (d : Sm.D) (r : Value) (o : Bool), g < L.threads ∧ g / L.block = c ∧
    X.get (g, k) = some ⟨d.site.pc, .shfl .bfly d.stg.m2 1 31 r o⟩ ∧
    St Q L X g k = some (some (.d (.sm d))) ∧ d.site = .shfl12 ∧ d.i = j ∧ d.p170 r = .ok true

theorem shfl12_site {g : Nat} {d t : Sm.D} {pc : Nat} {a r : Value} {o : Bool}
    (hs : d.site = .shfl12) (h : Sm.next L g d ⟨pc, .shfl .bfly a 1 31 r o⟩ = some (some t)) :
    t.site = .bar20 ↔ d.p170 r = .ok true := by
  simp only [Sm.next, hs] at h
  cases hp : d.p170 r with
  | error x => simp [hp] at h
  | ok p =>
    simp only [hp] at h
    cases p with
    | true =>
      simp only [↓reduceIte, toBar20_iff] at h
      obtain ⟨-, rfl⟩ := h
      simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp

/-- **With `DecAgree c j`, a default thread of `c` at `shfl12` of `j` goes to `bar20` exactly when
`Dc c j`.** -/
theorem dec_iff {c j : Nat} (hDA : DecAgree Q L X c j) {g k : Nat} {d t : Sm.D} {e : Event}
    (hg : g < L.threads) (hc : g / L.block = c) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .shfl12) (hi : d.i = j)
    (hn : Sm.next L g d e = some (some t)) : t.site = .bar20 ↔ Dc Q L X c j := by
  obtain ⟨r, -, o, -, hE, -, -⟩ := hDA hg hg hc hc he he hσ hσ hs hs hi hi
  subst hE
  rw [shfl12_site hs hn]
  constructor
  · intro hp
    exact ⟨g, k, d, r, o, hg, hc, he, hσ, hs, hi, hp⟩
  · rintro ⟨g2, k2, d2, r2, o2, hg2, hc2, he2, hσ2, hs2, hi2, hp2⟩
    obtain ⟨r1, r1', o1, o1', h1, h2, hp⟩ := hDA hg hg2 hc hc2 he he2 hσ hσ2 hs hs2 hi hi2
    simp only [Event.mk.injEq, Kind.shfl.injEq, true_and] at h1 h2
    obtain ⟨rfl, -⟩ := h1
    obtain ⟨rfl, -⟩ := h2
    rw [hp]
    exact hp2

/-! ### The bound -/

/-- The states of the iterations below `I` and of iteration `I` before its decision. -/
def Bnd (I : Nat) : DComp.St → Prop
  | .sm d => d.i < I ∨ (d.i = I ∧ late d.site = false)
  | .epi _ => False
  | _ => True

theorem bnd_prev {g : Nat} {I : Nat} {d0 d : Sm.D} {e : Event}
    (hn : Sm.next L g d0 e = some (some d)) (hb : Bnd I (.sm d)) : Bnd I (.sm d0) := by
  simp only [Bnd] at hb ⊢
  rcases Interface.next_iter hn with hi | ⟨hi, -, -⟩
  · rcases hb with hb | ⟨hb1, hb2⟩
    · left; omega
    · by_cases hl : late d0.site = true
      · have := late_next hn hl hi
        rw [hb2] at this
        exact absurd this (by decide)
      · right; exact ⟨by omega, by simpa using hl⟩
  · left
    rcases hb with hb | ⟨hb1, -⟩ <;> omega

/-! ### The invariants -/

/-- The fact about the `bar24` states before a state, below the bound `I`. -/
def RLow (I : Nat) (Dc : Nat → Prop) (n : Nat) (s : DComp.St) (nb : Nat) : Prop :=
  match s with
  | .sm d => (Bnd I (.sm d) → JS Dc d ∧ nb = RD Dc d) ∧ (¬ Bnd I (.sm d) → nResc Dc I ≤ nb)
  | .epi _ => nResc Dc (min n I) ≤ nb
  | _ => nb = 0

theorem init_state {g : Nat} (hd : g % L.block < 128) {s : DComp.St}
    (hs : St Q L X g 0 = some (some (.d s))) : s = .dstart (DStart.D.start L g) := by
  have hs' : Frame.stateAt (code L Q) X g 0 = some (some (.d s)) := hs
  rw [Frame.stateAt_zero] at hs'
  have h1 := Option.some.inj (Option.some.inj hs')
  change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else TSt.w (WComp.code L g Q).init) = TSt.d s at h1
  simp only [hd, ↓reduceIte] at h1
  cases h1
  rfl

/-- The step of a default thread's trace: the state before, its event and the step. -/
theorem trace_step {g k : Nat} (hg : g < L.threads) (hk : k + 1 ≤ (X.tr g).length)
    (ht : Frame.Tracked (code L Q) X) {s' : DComp.St}
    (hs' : St Q L X g (k + 1) = some (some (.d s'))) :
    ∃ (e : Event) (s : DComp.St), (X.tr g)[k]? = some e ∧
      St Q L X g k = some (some (.d s)) ∧ DComp.next L g Q s e = some (some s') := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, St Q L X g k = some (some σ) :=
    Frame.stateAt_live (C := code L Q) ht hg hs' (show k ≤ k + 1 by omega)
  have hn := Lk.next_of_st_succ he hσ hs'
  obtain ⟨s, rfl⟩ : ∃ s, σ = .d s := by
    cases σ with
    | d s => exact ⟨s, rfl⟩
    | w s =>
      exfalso
      obtain ⟨a, -, ha⟩ := Ledger.mapInv (show (WComp.next L g s e).map
        (Option.map TSt.w) = some (some (.d s')) from hn)
      cases ha
  obtain ⟨a, ha, hsa⟩ := Lk.next_d_inv hn
  cases hsa
  exact ⟨e, s, he, hσ, ha⟩

theorem isB24_iff {g k : Nat} {s : DComp.St} (hσ : St Q L X g k = some (some (.d s))) :
    IsB24 Q L X g k ↔ isB24 s = true := by
  constructor
  · rintro ⟨d, hd, hs⟩
    rw [hσ] at hd
    cases hd
    simp [isB24, hs]
  · intro h
    cases s with
    | sm d => exact ⟨d, hσ, by simpa [isB24] using h⟩
    | _ => simp [isB24] at h

/-- The numbers of iterations of a thread's CTA. -/
abbrev nIt (Q : Params) (L : Launch) (g : Nat) : Nat :=
  Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)

/-- **The `bar24` states before every state, when every iteration's decision agrees.** -/
theorem rinv_all (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} (hg : g < L.threads) (hd : g % L.block < 128)
    (hD : ∀ j, DecAgree Q L X (g / L.block) j) :
    ∀ k, k ≤ (X.tr g).length → ∀ s : DComp.St, St Q L X g k = some (some (.d s)) →
      JSx (Dc Q L X (g / L.block)) s ∧
        nB24 Q L X g k = Rval (Dc Q L X (g / L.block)) (nIt Q L g) s := by
  intro k
  induction k with
  | zero =>
    intro _ s hs
    rw [init_state hd hs]
    simp [JSx, Rval, nB24]
  | succ k ih =>
    intro hk s' hs'
    obtain ⟨e, s, he, hσ, ha⟩ := trace_step hg hk hf.tracked hs'
    have hge : X.get (g, k) = some e := he
    obtain ⟨hJ, h0⟩ := ih (by omega) s hσ
    obtain ⟨h1, h2⟩ := rval_next (n := nIt Q L g) ha hJ
      (fun d hd => by subst hd; exact (r26_numIters hpre hX hf hg hge hσ).symm)
      (fun d t hd hs ht => by
        subst hd
        exact dec_iff (hD d.i) hg rfl hge hσ hs rfl ht)
    refine ⟨h1, ?_⟩
    rw [nB24_succ, h2, h0]
    simp only [isB24_iff hσ]

/-- **The `bar24` states before every state, below the bound `I`.** -/
theorem rlow (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} (hg : g < L.threads) (hd : g % L.block < 128)
    (I : Nat) (hD : ∀ j < I, DecAgree Q L X (g / L.block) j) :
    ∀ k, k ≤ (X.tr g).length → ∀ s : DComp.St, St Q L X g k = some (some (.d s)) →
      RLow I (Dc Q L X (g / L.block)) (nIt Q L g) s (nB24 Q L X g k) := by
  intro k
  induction k with
  | zero =>
    intro _ s hs
    rw [init_state hd hs]
    simp [RLow, nB24]
  | succ k ih =>
    intro hk s' hs'
    obtain ⟨e, s, he, hσ, ha⟩ := trace_step hg hk hf.tracked hs'
    have hge : X.get (g, k) = some e := he
    have h0 := ih (by omega) s hσ
    have hmono : nB24 Q L X g k ≤ nB24 Q L X g (k + 1) := by
      rw [nB24_succ]; omega
    have hsucc : nB24 Q L X g (k + 1) =
        nB24 Q L X g k + if isB24 s = true then 1 else 0 := by
      rw [nB24_succ]; simp only [isB24_iff hσ]
    set Dc' := Dc Q L X (g / L.block)
    -- the exact case
    have exact_case : JSx Dc' s → nB24 Q L X g k = Rval Dc' (nIt Q L g) s →
        (∀ d, s = .sm d → d.site = .shfl12 → d.i < I) →
        RLow I Dc' (nIt Q L g) s' (nB24 Q L X g (k + 1)) := by
      intro hJ hR hlt
      obtain ⟨h1, h2⟩ := rval_next (n := nIt Q L g) ha hJ
        (fun d hd => by subst hd; exact (r26_numIters hpre hX hf hg hge hσ).symm)
        (fun d t hd hs ht => by
          subst hd
          exact dec_iff (hD d.i (hlt _ rfl hs)) hg rfl hge hσ hs rfl ht)
      have hv : nB24 Q L X g (k + 1) = Rval Dc' (nIt Q L g) s' := by rw [hsucc, h2, hR]
      cases s' with
      | sm d' =>
        refine ⟨fun _ => ⟨h1, hv⟩, fun hb => ?_⟩
        rw [hv]
        simp only [Bnd, not_or, not_and] at hb
        simp only [Rval, RD]
        have : I ≤ d'.i := by
          by_cases h : d'.i = I
          · omega
          · omega
        have := nResc_mono Dc' this
        omega
      | epi d' =>
        rw [hv]
        simp only [RLow, Rval]
        exact nResc_mono _ (Nat.min_le_left _ _)
      | dstart d' => simp only [RLow]; rw [hv]; rfl
      | pro d' => simp only [RLow]; rw [hv]; rfl
    cases s with
    | dstart d0 =>
      exact exact_case trivial h0 (fun d hd => by cases hd)
    | pro d0 =>
      exact exact_case trivial h0 (fun d hd => by cases hd)
    | epi d0 =>
      simp only [DComp.next] at ha
      obtain ⟨a, -, rfl⟩ := Ledger.mapInv ha
      exact le_trans h0 hmono
    | sm d0 =>
      obtain ⟨hB, hU⟩ := h0
      by_cases hb0 : Bnd I (.sm d0)
      · obtain ⟨hJ, hR⟩ := hB hb0
        by_cases h12 : d0.site = .shfl12 ∧ d0.i = I
        · -- the decision of iteration `I`: the successor is past the bound
          have hR0 : nResc Dc' I ≤ nB24 Q L X g k := by
            rw [hR, RD, h12.2]; omega
          simp only [DComp.next, DComp.smNext] at ha
          split at ha
          · rename_i hl
            exfalso
            have := h12.1
            revert hl
            obtain ⟨st, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d0
            simp only at this
            subst this
            simp [DComp.leaves]
          · obtain ⟨t, ht, rfl⟩ := Ledger.mapInv ha
            refine ⟨fun hbt => ?_, fun _ => le_trans hR0 hmono⟩
            exfalso
            simp only [Bnd] at hbt
            have hi := Interface.next_iter ht
            simp only [Sm.next, h12.1] at ht
            split at ht
            · split at ht
              · split at ht
                · rw [toBar20_iff] at ht
                  obtain ⟨-, rfl⟩ := ht
                  simp [late, Sm.D.upd] at hbt
                  omega
                · obtain rfl := Option.some.inj (Option.some.inj ht)
                  simp [late] at hbt
                  omega
              · simp at ht
            · simp at ht
        · exact exact_case hJ hR (fun d hd hs => by
            cases hd
            simp only [Bnd] at hb0
            rcases hb0 with h | ⟨h1, h2⟩
            · exact h
            · exact absurd ⟨hs, h1⟩ h12)
      · have hl0 := hU hb0
        simp only [DComp.next, DComp.smNext] at ha
        split at ha
        · simp only [DComp.exitNext] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst ha
            simp only [RLow]
            exact le_trans (nResc_mono _ (Nat.min_le_right _ _)) (le_trans hl0 hmono)
          · simp at ha
        · obtain ⟨t, ht, rfl⟩ := Ledger.mapInv ha
          refine ⟨fun hbt => absurd (bnd_prev ht hbt) hb0, fun _ => le_trans hl0 hmono⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
