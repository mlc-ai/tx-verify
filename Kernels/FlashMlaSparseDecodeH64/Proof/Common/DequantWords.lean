-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Nc

@[expose] public section

/-! # Warpgroup 2's length words are the launch's
-- domain: consistent

A warpgroup-2 state records the two length words it loaded (`l0`, `l1`). From the Q poll on they
are the launch's words of the CTA's row (`deq_words`: `lenWA`, `lenWB`, `Lib/Rounds.lean`), so the
role's block count is the CTA's (`deq_rounds`: `Dequant.rounds d.l0 d.l1 = blocksOf`). The words
are set by the set-up (the parameters; the CTA is inside the batch, `batch_in`) and by the two
`.nc` length loads, which read the row's words in a consistent execution (`deq_topk`,
`deq_extra`, `Dequant/Nc.lean`); every other step keeps them (`keep_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Dequant.Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A set-up site of warpgroup 2 (before the Q poll). -/
def deqSetup : Dequant.Site → Bool
  | .smr | .lenA | .lenB => true
  | _ => false

/-- **The words a warpgroup-2 state has recorded.** -/
def deqWordsOk (P : Params) (L : Launch) (g : Nat) (d : Dequant.Control.D) : Prop :=
  match d.site with
  | .smr => True
  | .lenA => eqz64 (pw8 (P.topkLenBase.getD 0)) = false ∧ d.l1 = pw P.extra_topk
  | .lenB => eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false ∧ d.l0 = lenWA P L (g / L.block)
  | _ => d.l0 = lenWA P L (g / L.block) ∧ d.l1 = lenWB P L (g / L.block)

private theorem rawNext_set (r : Fin 4) (s : Fin 8) : deqSetup (rawNext r s) = false := by
  revert r s; decide
private theorem storeNext_set (r : Fin 4) (s : Fin 8) : deqSetup (storeNext r s) = false := by
  revert r s; decide
/-- **A step after the set-up keeps the words** and stays after the set-up. -/
theorem keep_step {d a : Dequant.Control.D} {f : Event} (hs : deqSetup d.site = false)
    (h : succ P L g d f = some (some a)) :
    a.l0 = d.l0 ∧ a.l1 = d.l1 ∧ deqSetup a.site = false := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have hw {s' : Dequant.Site} (h' : deqSetup s' = false) :
      ∀ {a : Dequant.Control.D}, some (some a) =
        some (some (⟨s', el, ac, l0, l1, cnt, sb, pb⟩ : Dequant.Control.D)) →
      a.l0 = l0 ∧ a.l1 = l1 ∧ deqSetup a.site = false := by
    intro a h; cases h; exact ⟨rfl, rfl, h'⟩
  cases site with
  | smr | lenA | lenB => simp [deqSetup] at hs
  | exit => simp [succ] at h
  | wq =>
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split
      · simp only [loopEntry]; split <;> simp [deqSetup]
      · exact ⟨rfl, rfl, hs⟩
    · cases h
  | wraw | wsv =>
    simp only [succ, poll] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split <;> simp [deqSetup]
    · cases h
  | scale r =>
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [scaleNext]; split <;> simp [deqSetup]
    · cases h
  | raw r s =>
    simp only [succ, dataRd] at h
    split at h
    · exact hw (rawNext_set r s) h.symm
    · cases h
  | store r s => exact hw (storeNext_set r s) h.symm
  | fpx | arrD | bar => exact hw rfl h.symm
  | arrF =>
    simp only [succ, advance, Option.some.injEq] at h
    subst h
    split <;> simp [deqSetup]

/-- After the set-up the words are the launch's. -/
theorem words_of_ok {d : Dequant.Control.D} (hs : deqSetup d.site = false)
    (h : deqWordsOk P L g d) :
    d.l0 = lenWA P L (g / L.block) ∧ d.l1 = lenWB P L (g / L.block) := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | smr | lenA | lenB => simp [deqSetup] at hs
  | _ => exact h

/-- Launch words after the set-up are recorded words. -/
theorem ok_of_words {d : Dequant.Control.D} (hs : deqSetup d.site = false)
    (h0 : d.l0 = lenWA P L (g / L.block)) (h1 : d.l1 = lenWB P L (g / L.block)) :
    deqWordsOk P L g d := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | smr | lenA | lenB => simp [deqSetup] at hs
  | _ => exact ⟨h0, h1⟩

/-- **A set-up step records the launch's words**, given the length loads' words. -/
theorem setup_step (hp : Pre P L m) {d a : Dequant.Control.D} {f : Event}
    (hok : deqWordsOk P L g d)
    (hA : d.site = .lenA → eqz64 (pw8 (P.topkLenBase.getD 0)) = false →
      succ P L g d f = some (some (afterA P { d with l0 := W (P.topkLen (ctaidY L g)) })))
    (hB : d.site = .lenB → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false →
      succ P L g d f = some (some { d with site := .wq, l1 := W (P.extraTopkLen (ctaidY L g)) }))
    (h : succ P L g d f = some (some a)) : deqWordsOk P L g a := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | smr =>
    simp only [succ, afterSmr, batch_in hp g, Option.some.injEq] at h
    subst h
    cases hA0 : eqz64 (pw8 (P.topkLenBase.getD 0)) <;>
      cases hB0 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) <;>
      simp only [hA0, hB0, afterA, deqWordsOk, lenWA, lenWB, ite_true, ite_false,
        Bool.false_eq_true, and_self]
  | lenA =>
    obtain ⟨hA1, hl1⟩ := hok
    rw [hA rfl hA1, Option.some.injEq, Option.some.injEq] at h
    subst h
    cases hB0 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) <;>
      simp only [hB0, afterA, deqWordsOk, lenWA, lenWB, hA1, hl1, rowOf_cta, ite_true, ite_false,
        Bool.false_eq_true, and_self]
  | lenB =>
    obtain ⟨hB1, hl0⟩ := hok
    rw [hB rfl hB1, Option.some.injEq, Option.some.injEq] at h
    subst h
    exact ⟨hl0, by simp [lenWB, hB1, rowOf_cta]⟩
  | _ =>
    obtain ⟨h1, h2, h3⟩ := keep_step (by rfl) h
    obtain ⟨w0, w1⟩ := words_of_ok (by rfl) hok
    exact ok_of_words h3 (h1.trans w0) (h2.trans w1)

/-- The warpgroup-2 states with their recorded words. -/
def DeqWordsR (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Prop :=
  ∀ d n, σ = (.inr ⟨.inl .dequant, d⟩, n) → deqWordsOk P L g d

/-- A state the glue enters is a role's first state. -/
private theorem enter_ok {s : (startupCode P L g).D} {d : Dequant.Control.D} {n n' : Cls → Nat}
    (h : (Code.enter (startupCode P L g) (Code.withStubs (frag P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) s, n) =
      (.inr ⟨.inl .dequant, d⟩, n')) : deqWordsOk P L g d := by
  unfold Code.enter at h
  split at h
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at h
    obtain ⟨h1, -⟩ := h
    rename_i i _
    cases i with
    | inl e =>
      cases e <;> simp only [Sigma.mk.inj_iff, Sum.inl.injEq, reduceCtorEq, false_and] at h1
      obtain ⟨-, h2⟩ := h1
      cases eq_of_heq h2
      trivial
    | inr r => simp at h1
  · simp at h

/-- **The thread state behind a warpgroup-2 event.** -/
theorem deq_fired (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Dequant.Control.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .dequant, d⟩, n))) :
    ∃ t ins o, (code P L g (warpW L g)).AtD d t ∧ (code P L g (warpW L g)).inv d ∧
      kernel.code[(code P L g (warpW L g)).pc d]? = some ins ∧
      Fires ((code P L g (warpW L g)).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
  exact ⟨t, ins, o, hat, hi, hc, hf⟩

/-- A warpgroup-2 step from a state with its words, in a consistent execution. -/
private theorem deq_step_ok (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d d' : Dequant.Control.D} {n : Cls → Nat} {i : Nat} {f : Event}
    (hσ : Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .dequant, d⟩, n)))
    (hf : (X.tr g)[i]? = some f) (hok : deqWordsOk P L g d)
    (ha : succ P L g d f = some (some d')) : deqWordsOk P L g d' := by
  have hget : X.get (g, i) = some f := hf
  have nc {s : Dequant.Site} (hs : d.site = s) (hs' : s = .lenA ∨ s = .lenB) :
      ∀ fl, f.kind ≠ .ub fl := by
    intro fl hk
    rcases hs' with rfl | rfl <;> simp [succ, hs, hk] at ha
  refine setup_step hp hok (fun hs hA => ?_) (fun hs hB => ?_) ha
  · obtain ⟨t, ins, o, hat, hi, hc, hf'⟩ := deq_fired hp hX hget (nc hs (.inl rfl)) hσ
    exact deq_topk hp hX hget hat hi hc hf' hA hs
  · obtain ⟨t, ins, o, hat, hi, hc, hf'⟩ := deq_fired hp hX hget (nc hs (.inr rfl)) hσ
    exact deq_extra hp hX hget hat hi hc hf' hB hs

/-- **Warpgroup 2's states carry the launch's words** (`deqWordsOk`). -/
theorem deq_words (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) : DeqWordsR P L g σ := by
  refine region_stays_ev (DeqWordsR P L g) (j := 0) ?_ (Frame.stateAt_zero ..) ?_ k
    (Nat.zero_le k) σ hσ
  · rintro i ⟨s | ⟨r, d⟩, n⟩ σ' f - hσi hR hf hn d' n' rfl
    · simp only [Code.toMachine, Code.glue] at hn
      cases hs : Startup.succ L g s f with
      | none => simp [hs] at hn
      | some o =>
        cases o with
        | none => simp [hs] at hn
        | some s' =>
          simp only [hs, Option.map_some, Option.some.injEq] at hn
          exact enter_ok hn
    · simp only [Code.toMachine, Code.glue] at hn
      cases hs : (Code.withStubs (frag P L g) Entry.pc r).next d f with
      | none => simp [hs] at hn
      | some o =>
        cases o with
        | none => simp [hs] at hn
        | some a =>
          simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq,
            Sigma.mk.inj_iff] at hn
          obtain ⟨⟨rfl, ha⟩, -⟩ := hn
          cases eq_of_heq ha
          exact deq_step_ok hp hX hσi hf (hR d n rfl) hs
  · rintro d n h
    exact enter_ok (s := (startupCode P L g).init) (n := fun _ => 0) h

/-- Away from the length loads warpgroup 2's machine never stops. -/
private theorem succ_ne_none {d : Dequant.Control.D} {e : Event} (hA : d.site ≠ .lenA)
    (hB : d.site ≠ .lenB) : succ P L g d e ≠ some none := by
  intro h
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | lenA => exact hA rfl
  | lenB => exact hB rfl
  | wq | scale _ => simp only [succ] at h; split at h <;> simp at h
  | wraw | wsv => simp only [succ, poll] at h; split at h <;> simp at h
  | raw _ _ => simp only [succ, dataRd] at h; split at h <;> simp at h
  | _ => simp [succ] at h

/-- **Warpgroup 2's machine does not stop at its events** (the no-stop obligation of
`Common/FollowProof.lean`): its length loads read the launch's 32-bit words. -/
theorem deq_live (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Dequant.Control.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .dequant, d⟩, n))) :
    succ P L g d e ≠ some none := by
  have hok := deq_words hp hX hσ d n rfl
  have nc {s : Dequant.Site} (hs : d.site = s) (hs' : s = .lenA ∨ s = .lenB)
      (hu : ∃ fl, e.kind = .ub fl) : succ P L g d e ≠ some none := by
    obtain ⟨fl, hk⟩ := hu
    rcases hs' with rfl | rfl <;> simp [succ, hs, hk]
  by_cases hA : d.site = .lenA
  · by_cases hu : ∃ fl, e.kind = .ub fl
    · exact nc hA (.inl rfl) hu
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := deq_fired hp hX he (fun fl h => hu ⟨fl, h⟩) hσ
    have hok' := hok
    simp only [deqWordsOk, hA] at hok'
    rw [deq_topk hp hX he hat hi hc hf hok'.1 hA]
    simp
  by_cases hB : d.site = .lenB
  · by_cases hu : ∃ fl, e.kind = .ub fl
    · exact nc hB (.inr rfl) hu
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := deq_fired hp hX he (fun fl h => hu ⟨fl, h⟩) hσ
    have hok' := hok
    simp only [deqWordsOk, hB] at hok'
    rw [deq_extra hp hX he hat hi hc hf hok'.1 hB]
    simp
  exact succ_ne_none hA hB

/-- **Warpgroup 2's block count is the CTA's**: after the set-up, the blocks of the recorded
words are `blocksOf P L (g / L.block)`. -/
theorem deq_rounds (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Dequant.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .dequant, d⟩, n)))
    (hs : deqSetup d.site = false) :
    Dequant.rounds d.l0 d.l1 = blocksOf P L (g / L.block) := by
  obtain ⟨h0, h1⟩ := words_of_ok hs (deq_words hp hX hσ d n rfl)
  rw [h0, h1]
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
