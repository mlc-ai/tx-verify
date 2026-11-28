-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine

@[expose] public section

/-! # The control machine never goes back, except from the softmax-ready arrival

A step of warpgroup 0's control machine from a site other than `arrS` goes to a site of at least
the same pc (`succ_pc_mono`): the only backward step is the loop's, at the arrival. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem site_finish (d : D) : (finish w d).site = .exit ∨ (finish w d).site = .dealloc := by
  unfold finish; split <;> simp

theorem site_afterA (d : D) : (afterA P d).site = .bwait ∨ (afterA P d).site = .lenB := by
  unfold afterA; split <;> simp

theorem site_afterSink (d : D) :
    (afterSink P L g w d).site = .exit ∨ (afterSink P L g w d).site = .dealloc ∨
      (afterSink P L g w d).site = .bwait ∨ (afterSink P L g w d).site = .lenB ∨
      (afterSink P L g w d).site = .lenA := by
  unfold afterSink; split
  · rcases site_finish (w := w) d with h | h <;> simp [h]
  · split
    · rcases site_afterA (P := P) { d with l0 := pw P.topk } with h | h <;> simp [h]
    · simp

theorem site_afterSmr (d : D) :
    (afterSmr P L g w d).site = .sink ∨ (afterSmr P L g w d).site = .exit ∨
      (afterSmr P L g w d).site = .dealloc ∨ (afterSmr P L g w d).site = .bwait ∨
      (afterSmr P L g w d).site = .lenB ∨ (afterSmr P L g w d).site = .lenA := by
  unfold afterSmr; split
  · rcases site_afterSink (P := P) (L := L) (g := g) (w := w) d with h | h | h | h | h <;> simp [h]
  · simp

theorem site_loopEntry (d : D) : (loopEntry d).site = .ebar0 ∨ (loopEntry d).site = .bar0 := by
  unfold loopEntry; split <;> simp

theorem site_afterEld (d : D) : (afterEld L g d).site = .wsv ∨ (afterEld L g d).site = .lse := by
  unfold afterEld; split <;> simp

theorem site_nextChunk (k : Fin 4) (d : D) :
    (nextChunk k d).site = [.old 1, .old 2, .old 3, .commit].getD k.val .commit := rfl

theorem site_afterObar (k : Fin 4) (d : D) :
    (afterObar w k d).site = .oel k ∨ (afterObar w k d).site = (nextChunk k d).site := by
  unfold afterObar; split <;> simp

theorem site_afterOst (d : D) : afterOst d = .fpx ∨ afterOst d = .rsf := by
  unfold afterOst; split <;> simp

/-- The pcs of a step: forward, and no jump over the exchange load (pc 572) but to the
epilogue (pc 1154, no block) or the end, none over the epilogue's (pc 1157) but to the end. -/
def PcStepN (p p' : Nat) : Prop :=
  p ≤ p' ∧ (p < 572 → p' ≤ 572 ∨ 1154 ≤ p') ∧ (p < 1157 → p' ≤ 1157 ∨ 1840 ≤ p')

abbrev PcStep (c c' : D) : Prop := PcStepN c.site.pc c'.site.pc

variable {c c' : D} {e : Event}

theorem pcm_d1
    (hs : c.site = .bar0 ∨ c.site = .bwait ∨ c.site = .sldw ∨ c.site = .tcfb
      ∨ c.site = .mst ∨ c.site = .bar2 ∨ c.site = .arrV ∨ c.site = .rsf ∨ c.site = .rsfb
      ∨ c.site = .fpx ∨ c.site = .bar1 ∨ c.site = .ebar0 ∨ c.site = .est ∨ c.site = .ebar1
      ∨ c.site = .lse ∨ c.site = .efa ∨ c.site = .commit ∨ c.site = .dealloc)
    (h : succ P L g w c e = some (some c')) : PcStep c c' := by
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs |
      hs | hs <;>
    simp only [succ, hs] at h <;> cases h <;> simp [hs, Site.pc, PcStep, PcStepN]

theorem pcm_tcfa (hs : c.site = .tcfa) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  cases h
  simp only [hs, Site.pc, PcStep, PcStepN]
  split <;> simp

theorem pcm_pst {k : Fin 8} (hs : c.site = .pst k) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  cases h
  fin_cases k <;> simp [hs, Site.pc, PcStep, PcStepN]

theorem pcm_k4 {k : Fin 4}
    (hs : c.site = .rldw k ∨ c.site = .rst k ∨ c.site = .rstw k ∨ c.site = .oldw k
      ∨ c.site = .ofpx k ∨ c.site = .otma k)
    (h : succ P L g w c e = some (some c')) : PcStep c c' := by
  rcases hs with hs | hs | hs | hs | hs | hs <;>
    simp only [succ, hs] at h <;> cases h <;> fin_cases k <;>
    simp [hs, Site.pc, nextChunk, ost2Base, PcStep, PcStepN]

theorem pcm_poll (hs : c.site = .wv ∨ c.site = .wq ∨ c.site = .wsv)
    (h : succ P L g w c e = some (some c')) : PcStep c c' := by
  rcases hs with hs | hs | hs <;> simp only [succ, hs, poll] at h <;> split at h <;>
    (try split at h) <;> cases h <;> simp [hs, Site.pc, PcStep, PcStepN]

theorem pcm_rd (hs : c.site = .vm ∨ c.site = .mld ∨ c.site = .eld)
    (h : succ P L g w c e = some (some c')) : PcStep c c' := by
  rcases hs with hs | hs | hs <;> simp only [succ, hs, dataRd] at h <;> split at h <;> cases h <;>
    (rcases site_afterEld (L := L) (g := g) c with h | h <;> simp [hs, h, Site.pc, PcStep, PcStepN])

theorem pcm_sink (hs : c.site = .sink) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs, dataRd] at h
  split at h <;> cases h <;>
  rcases site_afterSink (P := P) (L := L) (g := g) (w := w) c with h | h | h | h | h <;>
    simp [hs, h, Site.pc, PcStep, PcStepN]

theorem pcStepN_afterA {p : Nat} (hp : p = 168) (d : D) : PcStepN p (afterA P d).site.pc := by
  rcases site_afterA (P := P) d with h | h <;> simp [h, hp, Site.pc, PcStepN]

theorem pcm_lenA (hs : c.site = .lenA) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  unfold ncWord at h
  split at h
  · generalize rebuild 3 _ = r at h
    split at h
    · have h' := Option.some.inj (Option.some.inj h)
      subst h'
      exact pcStepN_afterA (by simp [hs, Site.pc]) _
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem pcm_lenB (hs : c.site = .lenB) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  unfold ncWord at h
  split at h
  · generalize rebuild 3 _ = r at h
    split at h
    · have h' := Option.some.inj (Option.some.inj h)
      subst h'
      simp [hs, Site.pc, PcStep, PcStepN]
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem pcm_sld {a : Bool} {k : Fin 2} (hs : c.site = .sld a k)
    (h : succ P L g w c e = some (some c')) : PcStep c c' := by
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl <;> simp only [succ, hs, tcLoad] at h <;> split at h <;> cases h <;>
    cases a <;> simp [hs, Site.pc, PcStep, PcStepN]

theorem pcm_rld {k : Fin 4} (hs : c.site = .rld k) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs, tcLoad] at h
  split at h <;> cases h
  fin_cases k <;> simp [hs, Site.pc, PcStep, PcStepN]

theorem pcm_old {k : Fin 4} (hs : c.site = .old k) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs, tcLoad] at h
  split at h <;> cases h
  fin_cases k <;> simp [hs, Site.pc, PcStep, PcStepN]

theorem pcm_pld {k : Fin 8} (hs : c.site = .pld k) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  split at h
  · split at h <;> cases h <;> fin_cases k <;> simp [hs, Site.pc, PcStep, PcStepN]
  · cases h

theorem pcm_vote (hs : c.site = .vote) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  split at h <;> cases h
  simp [hs, Site.pc, PcStep, PcStepN]

theorem pcm_ost {k : Fin 4} (hs : c.site = .ost k) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs, elemNext] at h
  split at h <;> cases h
  · have := k.isLt
    simp only [hs, Site.pc, PcStep, PcStepN]
    omega
  · rcases site_afterOst c with h | h <;> fin_cases k <;> simp [hs, h, Site.pc, PcStep, PcStepN]

theorem pcm_ost2 {k : Fin 4} {j : Fin 8} (hs : c.site = .ost2 k j)
    (h : succ P L g w c e = some (some c')) : PcStep c c' := by
  simp only [succ, hs, elemNext] at h
  split at h <;> cases h
  · have := k.isLt
    have := j.isLt
    simp only [hs, Site.pc, PcStep, PcStepN]
    fin_cases k <;> simp [ost2Base] <;> omega
  · fin_cases k <;> fin_cases j <;> simp [hs, Site.pc, ost2Base, PcStep, PcStepN]

theorem pcm_obar {k : Fin 4} (hs : c.site = .obar k) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  cases h
  have h1 := site_afterObar (w := w) k c
  have h2 := site_nextChunk k c
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h1 h2 hs ⊢ <;>
    rcases h1 with h1 | h1 <;> simp [hs, h1, h2, Site.pc, PcStep, PcStepN]

theorem pcm_oel {k : Fin 4} (hs : c.site = .oel k) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  split at h
  · cases h
    split <;> fin_cases k <;> simp [hs, Site.pc, nextChunk, PcStep, PcStepN]
  · cases h

theorem pcm_smr (hs : c.site = .smr) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  have h' := Option.some.inj (Option.some.inj h)
  subst h'
  rcases site_afterSmr (P := P) (L := L) (g := g) (w := w) c with h | h | h | h | h | h <;>
    simp [hs, h, Site.pc, PcStep, PcStepN]

theorem pcm_arrL (hs : c.site = .arrL) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  have h' := Option.some.inj (Option.some.inj h)
  subst h'
  rcases site_loopEntry c with h | h <;> simp [hs, h, Site.pc, PcStep, PcStepN]

theorem pcm_ebar (hs : c.site = .ebar) (h : succ P L g w c e = some (some c')) :
    PcStep c c' := by
  simp only [succ, hs] at h
  have h' := Option.some.inj (Option.some.inj h)
  subst h'
  rcases site_finish (w := w) c with h | h <;> simp [hs, h, Site.pc, PcStep, PcStepN]

/-- **The control machine goes forward**: a step from a site other than the softmax-ready
arrival goes to a site of at least the same pc. -/
theorem succ_pc_step (h : succ P L g w c e = some (some c')) (hs : c.site ≠ .arrS) :
    PcStep c c' := by
  cases hc : c.site with
  | smr => exact pcm_smr hc h
  | sink => exact pcm_sink hc h
  | lenA => exact pcm_lenA hc h
  | lenB => exact pcm_lenB hc h
  | bwait => exact pcm_d1 (by simp [hc]) h
  | arrL => exact pcm_arrL hc h
  | bar0 => exact pcm_d1 (by simp [hc]) h
  | wv => exact pcm_poll (by simp [hc]) h
  | wq => exact pcm_poll (by simp [hc]) h
  | tcfa => exact pcm_tcfa hc h
  | sld a k => exact pcm_sld hc h
  | sldw => exact pcm_d1 (by simp [hc]) h
  | tcfb => exact pcm_d1 (by simp [hc]) h
  | vm => exact pcm_rd (by simp [hc]) h
  | pst k => exact pcm_pst hc h
  | bar1 => exact pcm_d1 (by simp [hc]) h
  | pld k => exact pcm_pld hc h
  | mst => exact pcm_d1 (by simp [hc]) h
  | bar2 => exact pcm_d1 (by simp [hc]) h
  | arrV => exact pcm_d1 (by simp [hc]) h
  | mld => exact pcm_rd (by simp [hc]) h
  | vote => exact pcm_vote hc h
  | ost k => exact pcm_ost hc h
  | rsf => exact pcm_d1 (by simp [hc]) h
  | rld k => exact pcm_rld hc h
  | rldw k => exact pcm_k4 (k := k) (by simp [hc]) h
  | rst k => exact pcm_k4 (k := k) (by simp [hc]) h
  | rstw k => exact pcm_k4 (k := k) (by simp [hc]) h
  | rsfb => exact pcm_d1 (by simp [hc]) h
  | fpx => exact pcm_d1 (by simp [hc]) h
  | arrS => exact absurd hc hs
  | ebar0 => exact pcm_d1 (by simp [hc]) h
  | est => exact pcm_d1 (by simp [hc]) h
  | ebar1 => exact pcm_d1 (by simp [hc]) h
  | eld => exact pcm_rd (by simp [hc]) h
  | lse => exact pcm_d1 (by simp [hc]) h
  | wsv => exact pcm_poll (by simp [hc]) h
  | efa => exact pcm_d1 (by simp [hc]) h
  | old k => exact pcm_old hc h
  | oldw k => exact pcm_k4 (k := k) (by simp [hc]) h
  | ost2 k j => exact pcm_ost2 hc h
  | ofpx k => exact pcm_k4 (k := k) (by simp [hc]) h
  | obar k => exact pcm_obar hc h
  | oel k => exact pcm_oel hc h
  | otma k => exact pcm_k4 (k := k) (by simp [hc]) h
  | commit => exact pcm_d1 (by simp [hc]) h
  | ebar => exact pcm_ebar hc h
  | dealloc => exact pcm_d1 (by simp [hc]) h
  | exit => simp only [succ, hc] at h; cases h

/-- **The loop's step goes to the block's head or to the epilogue.** -/
theorem succ_arrS (h : succ P L g w c e = some (some c')) (hs : c.site = .arrS) :
    c'.site = .bar0 ∨ c'.site = .ebar0 := by
  simp only [succ, hs] at h
  split at h
  · cases h; simp
  · cases h; simp

/-- **The control machine goes forward**: a step from a site other than the softmax-ready
arrival goes to a site of at least the same pc. -/
theorem succ_pc_mono (h : succ P L g w c e = some (some c')) (hs : c.site ≠ .arrS) :
    c.site.pc ≤ c'.site.pc := (succ_pc_step h hs).1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
