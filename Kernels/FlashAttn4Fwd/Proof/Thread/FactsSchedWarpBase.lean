-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBase

@[expose] public section

/-! # The warp collectives' schedule from the counts and the site tables (`Cross.WarpSched`)

`WarpSched` is a collective schedule of `Sched.isWarpColl` with the warp as key and three strict
clauses. From the per-thread data of `Sched.collSched_of` (the count `C g d`, the site tables
against `S`) with the collective sites the warp-collective kinds (`nextKind d = .warp`):

* `endAt`, `endLt` are the two halves of the site-table comparison at the state at the trace's
  end;
* `stopLt` asks a stopped machine's last state to be more than one before the next collective:
  the event it stopped at is not a warp collective, so the count is the state's; this is the
  premise `hstop` (per role: the times are even, or the machine never stops at a site one before
  a collective);
* `gap`: consecutive collectives more than one apart.

`warpSched_of` assembles it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The warp collectives' schedule of the warps of a group (the threads `Grp` selects, closed
under the warp): `Cross.WarpSched`'s clauses for those threads. -/
structure WarpSchedG (L : Launch) (X : Execution) (Grp : Nat → Prop) (S : Nat × Nat → Nat → Nat) :
    Prop where
  sched : Sched.CollSched (timed L) X Sched.isWarpColl (warpKey L) Grp S
  endAt : ∀ {g : Nat} {d : ThreadD}, g < L.threads → Grp g →
    St L X g (X.tr g).length = some (some d) →
    nextKind d = .warp → stateTime L g d = S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)
  endLt : ∀ {g : Nat} {d : ThreadD}, g < L.threads → Grp g →
    St L X g (X.tr g).length = some (some d) →
    nextKind d ≠ .warp → stateTime L g d < S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)
  stopLt : ∀ {g : Nat} {d : ThreadD} {e : Event}, g < L.threads → Grp g →
    St L X g (X.tr g).length = none → St L X g ((X.tr g).length - 1) = some (some d) →
    X.get (g, (X.tr g).length - 1) = some e → Sched.isWarpColl e = false →
    stateTime L g d + 1 < S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)
  gap : ∀ c n, S c n + 1 < S c (n + 1)

/-- The schedule of all threads is `Cross.WarpSched`. -/
theorem WarpSchedG.toWarpSched {S : Nat × Nat → Nat → Nat} (h : WarpSchedG L X (fun _ => True) S) :
    WarpSched L X S where
  sched := h.sched
  endAt hg := h.endAt hg trivial
  endLt hg := h.endLt hg trivial
  stopLt hg := h.stopLt hg trivial
  gap := h.gap

/-- **Two groups' schedules** cut by a predicate of the warp make one of their union. -/
theorem warpSchedG_union {G : Nat → Prop} {Q : Nat × Nat → Prop} [DecidablePred Q]
    {S1 S2 : Nat × Nat → Nat → Nat}
    (h1 : WarpSchedG L X (fun g => G g ∧ Q (warpKey L g)) S1)
    (h2 : WarpSchedG L X (fun g => G g ∧ ¬ Q (warpKey L g)) S2) :
    WarpSchedG L X G (fun c n => if Q c then S1 c n else S2 c n) where
  sched := Sched.collSched_union h1.sched h2.sched
  endAt := by
    intro g d hg hG hσ hk
    by_cases hq : Q (warpKey L g)
    · simp only [hq, ↓reduceIte]; exact h1.endAt hg ⟨hG, hq⟩ hσ hk
    · simp only [hq, ↓reduceIte]; exact h2.endAt hg ⟨hG, hq⟩ hσ hk
  endLt := by
    intro g d hg hG hσ hk
    by_cases hq : Q (warpKey L g)
    · simp only [hq, ↓reduceIte]; exact h1.endLt hg ⟨hG, hq⟩ hσ hk
    · simp only [hq, ↓reduceIte]; exact h2.endLt hg ⟨hG, hq⟩ hσ hk
  stopLt := by
    intro g d e hg hG h0 hσ he hp
    by_cases hq : Q (warpKey L g)
    · simp only [hq, ↓reduceIte]; exact h1.stopLt hg ⟨hG, hq⟩ h0 hσ he hp
    · simp only [hq, ↓reduceIte]; exact h2.stopLt hg ⟨hG, hq⟩ h0 hσ he hp
  gap := by
    intro c n
    by_cases hq : Q c
    · simp only [hq, ↓reduceIte]; exact h1.gap c n
    · simp only [hq, ↓reduceIte]; exact h2.gap c n

/-- A group's schedule is one of each smaller group. -/
theorem WarpSchedG.mono {G G' : Nat → Prop} {S : Nat × Nat → Nat → Nat}
    (h : WarpSchedG L X G S) (hG : ∀ g, G' g → G g) : WarpSchedG L X G' S where
  sched := h.sched.mono_grp hG
  endAt hg hg' := h.endAt hg (hG _ hg')
  endLt hg hg' := h.endLt hg (hG _ hg')
  stopLt hg hg' := h.stopLt hg (hG _ hg')
  gap := h.gap

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **A run invariant holds at every followed state**, before an event or at the trace's end. -/
theorem runInv_at {g k : Nat} {d : ThreadD} {J : ThreadD → List Event → Prop}
    (hJ : RunInv L g J) (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St L X g k = some (some d)) : J d ((X.tr g).take k) := by
  rcases Nat.lt_or_ge k (X.tr g).length with hlt | hge
  · exact RunInv.holds hpre hX hg hJ hlt hσ
  have hk' : k = (X.tr g).length := by omega
  subst hk'
  rw [List.take_length]
  by_cases hl : (X.tr g).length = 0
  · have h0 : X.tr g = [] := List.length_eq_zero_iff.mp hl
    have hi : St L X g (X.tr g).length = some (some (code L g).init) := by
      rw [hl]; exact Frame.stateAt_zero
    rw [hσ] at hi
    cases hi
    rw [h0]
    exact hJ.init
  · obtain ⟨d0, hσ0⟩ := Frame.stateAt_live (C := code L) ht hg hσ (Nat.sub_le _ 1)
    obtain ⟨t, ins, u, hat, hinv, hc, hf, hn⟩ := last_step hpre hX hok hg hσ (by omega) hσ0
    have h := hJ.step (RunInv.holds hpre hX hg hJ (by omega) hσ0) hat hinv hc hf hn
    rwa [← List.take_succ_eq_append_getElem (by omega), Nat.sub_add_cancel (by omega),
      List.take_length] at h

omit ht in
/-- **The warp collectives' schedule from the counts and the site tables.** -/
theorem warpSched_of {Grp : Nat → Prop} {S : Nat × Nat → Nat → Nat} (C : Nat → ThreadD → Nat)
    (hcnt : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → Grp g → k ≤ (X.tr g).length →
      St L X g k = some (some d) → ((X.tr g).take k).countP Sched.isWarpColl = C g d)
    (htime : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → Grp g → k ≤ (X.tr g).length →
      St L X g k = some (some d) →
        (nextKind d = .warp → stateTime L g d = S (warpKey L g) (C g d)) ∧
        (nextKind d ≠ .warp → stateTime L g d < S (warpKey L g) (C g d)))
    (hstop : ∀ {g : Nat} {d : ThreadD} {e : Event}, g < L.threads → Grp g →
      St L X g (X.tr g).length = none → St L X g ((X.tr g).length - 1) = some (some d) →
      X.get (g, (X.tr g).length - 1) = some e → Sched.isWarpColl e = false →
      stateTime L g d + 1 < S (warpKey L g) (C g d))
    (hgap : ∀ c n, S c n + 1 < S c (n + 1)) : WarpSchedG L X Grp S where
  sched := Sched.collSched_of C (fun _ d => nextKind d == .warp)
    (fun hg hG hk hσ => hcnt hg hG hk hσ)
    (fun hg _ hσ he => (fired_kind hpre hX hok hg hσ he).1)
    (fun hg hG hk hσ => ⟨fun h => (htime hg hG hk hσ).1 (beq_iff_eq.mp h),
      fun h => (htime hg hG hk hσ).2 (by simpa using h)⟩)
    (fun c n => (Nat.lt_succ_self _).trans (hgap c n))
  endAt := by
    intro g d hg hG hσ hk
    have h := hcnt hg hG le_rfl hσ
    rw [List.take_length] at h
    rw [h]
    exact (htime hg hG le_rfl hσ).1 hk
  endLt := by
    intro g d hg hG hσ hk
    have h := hcnt hg hG le_rfl hσ
    rw [List.take_length] at h
    rw [h]
    exact (htime hg hG le_rfl hσ).2 hk
  stopLt := by
    intro g d e hg hG hσ0 hσ he hp
    have hlen := Sched.len_pos_of_stop hσ0
    have h := hcnt hg hG (Nat.sub_le _ 1) hσ
    have hsp := Sched.split_last (X := X) (g := g) hlen
    have hge : (X.tr g)[(X.tr g).length - 1] = e := by
      have hj : (X.tr g).length - 1 < (X.tr g).length := by omega
      have : X.get (g, (X.tr g).length - 1) = some (X.tr g)[(X.tr g).length - 1] :=
        List.getElem?_eq_getElem hj
      rw [this] at he
      exact Option.some.inj he
    have h2 := congrArg (List.countP Sched.isWarpColl) hsp
    rw [List.countP_append, hge] at h2
    simp only [List.countP_singleton, hp] at h2
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h2
    rw [h2, h]
    exact hstop hg hG hσ0 hσ he hp
  gap := hgap

omit ht in
/-- The event fired from a followed state is fired from a template of the site's kind. -/
theorem fired_tmpl {g k : Nat} {d : ThreadD} {e : Event} (hg : g < L.threads)
    (hσ : St L X g k = some (some d)) (he : X.get (g, k) = some e) :
    ∃ pc m o, KindTmpl (nextKind d) m ∧ Fires pc m e o := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX he hσ
  rcases tmpl_kind hat hc with ⟨f, hub⟩ | hk
  · exact absurd hub (hok g hg d t ins hat hinv hc f)
  · exact ⟨_, _, o, hk, hf⟩

omit hpre hX ht hok in
/-- The state after a loader event, from the state before it. -/
theorem loader_succ {g j : Nat} {e : Event} {d : Loader.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.loader d)))) :
    St L X g (j + 1) = (Loader.next L g d e).map (Option.map (.inr ∘ .loader)) := by
  unfold St at hσ ⊢
  rw [Frame.stateAt_succ he, hσ]
  rfl

omit ht in
/-- **The loader never stops at its sites one before a collective**: its empty polls, its
arrivals and its copies continue on their events. -/
theorem loader_tight {g j : Nat} {e : Event} {d : Loader.D} (hg : g < L.threads)
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.loader d))))
    (hs : (∃ u, d.site = .wait u) ∨ (∃ u, d.site = .arrive u) ∨ ∃ u jj, d.site = .copy u jj) :
    St L X g (j + 1) ≠ none := by
  rw [loader_succ he hσ]
  obtain ⟨pc, m, o, hk, hf⟩ := fired_tmpl hpre hX hok hg hσ he
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  rcases hs with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, jj, rfl⟩
  all_goals simp only [nextKind, loaderKind, KindTmpl] at hk
  all_goals (try casesm* _ ∨ _, ∃ _, _, _ ∧ _)
  all_goals subst_vars
  all_goals simp only [Fires] at hf
  all_goals (try casesm* _ ∨ _, ∃ _, _, _ ∧ _)
  all_goals subst_vars
  all_goals simp [Loader.next]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
