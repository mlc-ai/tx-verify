-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefCount

@[expose] public section

/-! # Warpgroup 0's reference invariant: the plain steps

The step obligation of a site (`StepRef`). A site that fires neither an arrival nor a successful
poll (`Site.mb = false`, `evK_noMb`) keeps the mbarrier counts; its successor keeps the region,
the place and the words, or moves within the set-up, from the set-up to the end, or from the
epilogue after the SV poll to the end (`Same`, `succ_same`), so the invariant is kept
(`step_same`, `next_plain`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The step obligation of the reference invariant at site `s`. -/
def StepRef (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (s : Site) : Prop :=
  ∀ (d : D) (n : Cnt → Nat) (e : Event) (d' : D), d.site = s → inRole e = true →
    (∀ f, e.kind ≠ .ub f) → RefCore L g d n → EvK P L g w d e →
    succ P L g w d e = some (some d') → RefCore L g d' (Code.bump cls n e)

/-- The sites of the mbarrier events. -/
def Site.mb : Site → Bool
  | .arrL | .wv | .wq | .arrV | .arrS | .wsv => true
  | _ => false

/-- Every other site fires neither an arrival nor a successful poll. -/
theorem evK_noMb {d : D} {e : Event} (hs : d.site.mb = false) (hu : ∀ f, e.kind ≠ .ub f)
    (hev : EvK P L g w d e) : isMb e.kind = false := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, k⟩ := e
  simp only at hu
  cases s <;> simp only [Site.mb, Bool.true_eq_false] at hs <;>
    simp only [EvK, GWrAt, RdAt, WrAt, GenWrAt, NcEv, TcLdEv, TcStEv] at hev <;>
    (try casesm* _ ∨ _, _ ∧ _, Exists _) <;> subst_vars <;> simp_all [isMb]

/-- The successor moves within what the invariant does not distinguish. -/
def Same (d d' : D) : Prop :=
  (d'.site.reg = d.site.reg ∧ d'.site.idx = d.site.idx ∧ d'.words = d.words) ∨
    (d.site.reg = .setup ∧ d'.site.reg = .setup) ∨
    (d.site.reg = .epi ∧ d.site.idx = 1 ∧ d'.site.reg = .fin ∧ d'.words = d.words)

theorem step_same {d d' : D} {n : Cnt → Nat} {e : Event} (hmb : isMb e.kind = false)
    (hJ : RefCore L g d n) (hS : Same d d') : RefCore L g d' (Code.bump cls n e) := by
  unfold RefCore at hJ ⊢
  have hb := bump_plain (n := n) hmb
  rcases hS with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · rw [h1, h2, h3]
    exact hJ.congr hb
  · rw [h1] at hJ
    rw [h2]
    exact RefAt.congr (k := .setup) hb hJ
  · rw [h1, h2] at hJ
    rw [h3, h4]
    exact (RefAt.congr (k := .epi) (i := 1) hb hJ).imp id id

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The successor of a site of no mbarrier event** moves within `Same`. -/
theorem succ_same {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
    (hs : d.site.mb = false) (hn : succ P L g w d e = some (some d')) : Same d d' := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [Site.mb, Bool.true_eq_false] at hs
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals
    simp only [succ, dataRd, tcLoad, ncWord, poll, elemNext, afterSmr, afterSink, hb,
      Bool.false_eq_true, ↓reduceIte, afterA, finish, afterOst, nextChunk, afterObar, afterEld,
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
      List.getD_cons_succ, Fin.zero_eta, Fin.mk_one] at hn
    repeat' split at hn
    all_goals (simp only [Option.some.injEq, reduceCtorEq] at hn) <;> subst hn <;>
      simp [Same, Site.reg, Site.idx, Control.D.words]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **A step from a site other than the length loads keeps the launch facts**: a length load is
entered only where its pointer is set, and a word is set to the parameter only where the pointer
is not; a CTA inside the batch (`hb`) does not end at the sink. -/
theorem launch_plain {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
    (hL : LaunchOk P L g d) (hA : d.site ≠ .lenA) (hB : d.site ≠ .lenB)
    (hn : succ P L g w d e = some (some d')) : LaunchOk P L g d' := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  revert hL hA hB
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  case lenA => exact fun _ h => absurd rfl h
  case lenB => exact fun _ _ h => absurd rfl h
  all_goals
    intro hL _ _
    simp only [succ, dataRd, tcLoad, poll, elemNext, afterSmr, afterSink, afterA,
      finish, afterOst, nextChunk, afterObar, afterEld, loopEntry, advance, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero, List.getD_cons_succ,
      Fin.zero_eta, Fin.mk_one] at hn
    repeat' split at hn
    all_goals (simp only [Option.some.injEq, reduceCtorEq] at hn) <;> subst hn <;>
      simp_all [LaunchOk, Site.lens, lenWA, lenWB]

/-- **The plain steps keep the invariant.** -/
theorem next_plain {s : Site} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
    (hs : s.mb = false) : StepRef P L g w s := by
  intro d n e d' hd _ hu hJ hev hn
  subst hd
  exact step_same (evK_noMb hs hu hev) hJ (succ_same hb hs hn)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
