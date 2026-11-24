-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreBytes
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

/-! # Actual score-load payloads at the WG0 validity-mask boundary -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The event at the given role visit reads these 32 words from the indicated score half. -/
def ScoreLoadVisit (P : Params) (L : Launch) (X : Execution)
    (g j block : Nat) (a k : Fin 2) (words : List Value) : Prop :=
  ∃ d : D, Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
    d.site = .scoreLoad a k ∧ d.block = block ∧
    X.TLd (g, j) (scoreLoadColumn k) words .s32x32b ∧ words.length = 32

private theorem followed_step (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    {i stop : Nat} {d : D} {last : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hlast : Frame.stateAt (Machine.code P L) X g stop = some (some last))
    (hb : BeforeMaskRead d.site) (hi : i < stop) (hlen : stop ≤ (X.tr g).length) :
    ∃ e s, X.get (g, i) = some e ∧
      Wg0.next P L g d e = some (some s) ∧
      Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 s)) := by
  have hil : i < (X.tr g).length := by omega
  obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e :=
    ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨_, _, ⟨_, hinv⟩, _⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  have hstep : Frame.stateAt (Machine.code P L) X g (i + 1) =
      Machine.next P L g (.wg0 d) e := by
    rw [Frame.stateAt_succ he, hd]
    rfl
  rcases next_beforeMaskRead (e := e) hinv hb with hnone | ⟨s, hn, _, _⟩
  · have hdead : Frame.stateAt (Machine.code P L) X g (i + 1) = none :=
      hstep.trans (by rw [Machine.next, hnone]; rfl)
    rw [Frame.stateAt_none_mono hdead hi] at hlast
    cases hlast
  · exact ⟨e, s, he, hn, hstep.trans (by rw [Machine.next, hn]; rfl)⟩

private theorem score_step (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    {i stop : Nat} {d : D} {last : Machine.ThreadD} {k : Fin 2}
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .scoreLoad ⟨arm L g, armLt L g⟩ k)
    (hlast : Frame.stateAt (Machine.code P L) X g stop = some (some last))
    (hi : i < stop) (hlen : stop ≤ (X.tr g).length) :
    ∃ words, ScoreLoadVisit P L X g i d.block ⟨arm L g, armLt L g⟩ k words ∧
      Frame.stateAt (Machine.code P L) X g (i + 1) =
        some (some (.wg0 { loadScores d (arm L g == k.val) words with
          site := afterScoreSite ⟨arm L g, armLt L g⟩ k })) := by
  obtain ⟨e, s, he, hn, hnext⟩ :=
    followed_step hX hs hd hlast (by rw [hsite]; trivial) hi hlen
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  cases o with
  | none =>
    have hnone := composed_ending_next hf
    simp [Machine.next, hn] at hnone
  | some u =>
    obtain ⟨words, hw, hk⟩ := fired_scoreLoad_event hpre hsite hf
    have hload : X.TLd (g, i) (scoreLoadColumn k) words .s32x32b := by
      cases e
      exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩
    simp only [Wg0.next, nextSite, hsite, hk, ↓reduceIte, Option.some.injEq] at hn
    subst s
    exact ⟨words, ⟨d, hd, hsite, rfl, hload, hw⟩, hnext⟩

private theorem fenceLoad_target {d s : D} {e : Event} (hd : d.site = .fenceLoad)
    (hn : Wg0.next P L g d e = some (some s)) :
    s = { d with site := .scoreLoad ⟨arm L g, armLt L g⟩ 0 } := by
  cases hk : e.kind <;> simp only [Wg0.next, nextSite, hd, hk, reduceCtorEq] at hn
  case tc k => cases k <;> simp_all

private theorem scoreWait_target {d s : D} {e : Event} (hd : d.site = .scoreWait)
    (hn : Wg0.next P L g d e = some (some s)) :
    s = { d with site := .fenceBefore } := by
  cases hk : e.kind <;> simp only [Wg0.next, nextSite, hd, hk, reduceCtorEq] at hn
  case tc k => cases k <;> simp_all

private theorem fenceBefore_target {d s : D} {e : Event} (hd : d.site = .fenceBefore)
    (hn : Wg0.next P L g d e = some (some s)) :
    s = { d with site := .maskRead } := by
  cases hk : e.kind <;> simp only [Wg0.next, nextSite, hd, hk, reduceCtorEq] at hn
  case tc k => cases k <;> simp_all

private theorem loadScores_block (d : D) (own : Bool) (words : List Value) :
    (loadScores d own words).block = d.block := by
  cases own <;> rfl

/-- Five events after the post-QK fence, the two fired Tensor Memory loads supply exactly
the mask site's own and peer words. This holds independently of their numerical values. -/
theorem maskRead_score_history (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    {i : Nat} {entry d : D}
    (hstart : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 entry)))
    (hsite : entry.site = .fenceLoad)
    (hmask : Frame.stateAt (Machine.code P L) X g (i + 5) = some (some (.wg0 d)))
    (hlen : i + 5 ≤ (X.tr g).length) :
    ∃ lo hi, d.site = .maskRead ∧ d.block = entry.block ∧
      ScoreLoadVisit P L X g (i + 1) d.block ⟨arm L g, armLt L g⟩ 0 lo ∧
      ScoreLoadVisit P L X g (i + 2) d.block ⟨arm L g, armLt L g⟩ 1 hi ∧
      (d.ownScores, d.peerScores) = if arm L g = 0 then (lo, hi) else (hi, lo) := by
  let a : Fin 2 := ⟨arm L g, armLt L g⟩
  obtain ⟨_, d0, _, hd0, h0⟩ := followed_step hX hs hstart hmask
    (by rw [hsite]; trivial) (by omega) hlen
  have h0site := fenceLoad_target hsite hd0
  subst d0
  obtain ⟨lo, hlo, h1⟩ := score_step hpre hX hs h0 rfl hmask (by omega) hlen
  let d1 : D := { loadScores { entry with site := .scoreLoad a 0 } (arm L g == 0) lo with
    site := afterScoreSite a 0 }
  change Frame.stateAt (Machine.code P L) X g (i + 2) = some (some (.wg0 d1)) at h1
  obtain ⟨hi, hhi, h2⟩ := score_step hpre hX hs h1 rfl hmask (by omega) hlen
  let d2 : D := { loadScores d1 (arm L g == 1) hi with site := afterScoreSite a 1 }
  change Frame.stateAt (Machine.code P L) X g (i + 3) = some (some (.wg0 d2)) at h2
  obtain ⟨_, d3, _, hd3, h3⟩ := followed_step hX hs h2 hmask trivial (by omega) hlen
  have h3site := scoreWait_target (d := d2) rfl hd3
  subst d3
  obtain ⟨_, d4, _, hd4, h4⟩ := followed_step hX hs h3 hmask trivial (by omega) hlen
  have h4site := fenceBefore_target (d := { d2 with site := .fenceBefore }) rfl hd4
  subst d4
  rw [hmask] at h4
  cases h4
  have hb1 : d1.block = entry.block := loadScores_block _ _ _
  have hb2 : d2.block = d1.block := loadScores_block _ _ _
  change ScoreLoadVisit P L X g (i + 1) entry.block a 0 lo at hlo
  refine ⟨lo, hi, rfl, hb2.trans hb1, ?_, ?_, ?_⟩
  · change ScoreLoadVisit P L X g (i + 1) d2.block a 0 lo
    rwa [hb2, hb1]
  · change ScoreLoadVisit P L X g (i + 2) d2.block a 1 hi
    rwa [hb2]
  · change (d2.ownScores, d2.peerScores) = _
    have har : arm L g = 0 ∨ arm L g = 1 := by have := armLt L g; omega
    rcases har with h | h <;> simp [d2, d1, loadScores, h]

private theorem score_visit_f32 (hX : Consistent L kernel Assumptions.all mem0 X)
    {j block : Nat} {a k : Fin 2} {words : List Value}
    (hv : ScoreLoadVisit P L X g j block a k words)
    (hsource : ∀ reg : Fin 32, ∃ (src : EvId) (score : ℝ),
      TcMma.ReadSource L X .ld src (g, j) (tcDataCell L g .s32x32b (scoreLoadColumn k) reg.val) ∧
      TcMma.Result L Assumptions.all X src
        (tcDataCell L g .s32x32b (scoreLoadColumn k) reg.val) (.float .f32 score)) :
    words.all (fun v => decide (Assumptions.scoreHalf v)) = true := by
  obtain ⟨_, _, _, _, hload, hlen⟩ := hv
  apply List.all_eq_true.mpr
  intro word hm
  obtain ⟨n, hn, hw⟩ := List.mem_iff_getElem.mp hm
  let reg : Fin 32 := ⟨n, by omega⟩
  let cell := tcDataCell L g .s32x32b (scoreLoadColumn k) reg.val
  obtain ⟨src, score, hread, hvalue⟩ := hsource reg
  have hcell : TcMma.LoadCell L X (g, j) n cell := ⟨_, _, _, hload, hn, rfl⟩
  have hword := TcMma.LoadReadOk.f32 hX.tcRead.1 hload hcell hread (.inl hvalue)
  rw [List.getElem?_eq_getElem hn, hw] at hword
  cases hword
  exact decide_eq_true (show Assumptions.scoreHalf (.float .f32 score) from trivial)

/-- Identifying the FP32 QK result source for each actual score cell closes the score
representation guard. The read-source attribution remains a separate synchronization fact. -/
theorem exchangeReady_of_score_sources
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : Nat} {d : D} {lo hi : List Value}
    (hlo : ScoreLoadVisit P L X g (i + 1) d.block ⟨arm L g, armLt L g⟩ 0 lo)
    (hhi : ScoreLoadVisit P L X g (i + 2) d.block ⟨arm L g, armLt L g⟩ 1 hi)
    (hwords : (d.ownScores, d.peerScores) = if arm L g = 0 then (lo, hi) else (hi, lo))
    (hsource : ∀ (k : Fin 2) (reg : Fin 32), ∃ (src : EvId) (score : ℝ),
      let cell := tcDataCell L g .s32x32b (scoreLoadColumn k) reg.val
      TcMma.ReadSource L X .ld src (g, i + 1 + k.val) cell ∧
      TcMma.Result L Assumptions.all X src cell (.float .f32 score)) :
    exchangeReady d = true := by
  have hl := score_visit_f32 hX hlo (hsource 0)
  have hh := score_visit_f32 hX hhi (hsource 1)
  by_cases h : arm L g = 0
  · rw [ite_eq_left h, Prod.mk.injEq] at hwords
    simp only [exchangeReady, hwords.1, hwords.2, hl, hh, Bool.and_self]
  · rw [ite_eq_right h, Prod.mk.injEq] at hwords
    simp only [exchangeReady, hwords.1, hwords.2, hl, hh, Bool.and_self]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
