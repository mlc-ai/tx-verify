-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Kinds

@[expose] public section

/-! # The chain's sites keep the data flag, site by site

A step of the control machine from a site on the block's chain goes to the site `succOk` expects,
or leaves the loop (`innerSite` is false: the end of the warpgroup); from a site off the chain it
never enters the loop's inner sites (`okc_chain`, `okc_off`). One lemma per family of sites: a
combined case analysis over `Control.succ` hits the heartbeat limit. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

def innerSite (s : Site) : Bool := onChain s && !isStart s

/-- Direct sites. -/
theorem okc_d1 {c c' : Control.D} {e : Event}
    (hs : c.site = .bar0 ∨ c.site = .bwait ∨ c.site = .tcfa ∨ c.site = .sldw ∨ c.site = .tcfb
      ∨ c.site = .mst ∨ c.site = .bar2 ∨ c.site = .arrV ∨ c.site = .rsf ∨ c.site = .rsfb
      ∨ c.site = .fpx)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs <;>
    simp only [Control.succ, hs] at h <;> cases h <;> simp [succOk, innerSite, hs, isStart, onChain]

theorem okc_d2 {c c' : Control.D} {e : Event} {k : Fin 4}
    (hs : c.site = .rldw k ∨ c.site = .rst k ∨ c.site = .rstw k)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs <;>
    simp only [Control.succ, hs] at h <;> cases h <;> simp [succOk, innerSite, hs, isStart, onChain]

theorem okc_bar1 {c c' : Control.D} {e : Event} (hs : c.site = .bar1)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs] at h; cases h; simp [succOk, hs]

theorem okc_pst {c c' : Control.D} {e : Event} {k : Fin 8} (hs : c.site = .pst k)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs] at h; cases h; simp [succOk, hs]

theorem okc_arrL {c c' : Control.D} {e : Event} (hs : c.site = .arrL)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs] at h; cases h
  unfold Control.loopEntry; split <;> simp [succOk, innerSite, hs, isStart, onChain]

theorem okc_wv {c c' : Control.D} {e : Event} (hs : c.site = .wv ∨ c.site = .wq)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs <;> simp only [Control.succ, hs, Control.poll] at h <;> split at h <;>
    (try split at h) <;> cases h <;> simp [succOk, hs]

theorem okc_rd {c c' : Control.D} {e : Event} (hs : c.site = .vm ∨ c.site = .mld)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs <;> simp only [Control.succ, hs, Control.dataRd] at h <;> split at h <;>
    cases h <;> simp [succOk, hs]

theorem okc_sld {c c' : Control.D} {e : Event} {a : Bool} {k : Fin 2} (hs : c.site = .sld a k)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl <;> simp only [Control.succ, hs, Control.tcLoad] at h <;>
    split at h <;> cases h <;> simp only [succOk, hs] <;> simp

theorem okc_rld {c c' : Control.D} {e : Event} {j : Fin 4} (hs : c.site = .rld j)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs, Control.tcLoad] at h; split at h <;> cases h
  simp [succOk, hs]

theorem okc_pld {c c' : Control.D} {e : Event} {k : Fin 8} (hs : c.site = .pld k)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs] at h
  split at h
  · by_cases hel : c.el = 0
    · simp only [hel, ite_true] at h; cases h; simp [succOk, hs, hel]
    · simp only [hel, ite_false] at h; cases h; simp [succOk, hs, hel]
  · cases h

theorem okc_vote {c c' : Control.D} {e : Event} (hs : c.site = .vote)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs] at h; split at h
  · cases h; simp [succOk, hs]
  · cases h

theorem okc_ost {c c' : Control.D} {e : Event} {k : Fin 4} (hs : c.site = .ost k)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs, Control.elemNext] at h
  by_cases hel : c.el + 1 < 4
  · simp only [hel, ite_true] at h; cases h; simp [succOk, hs, hel]
  · simp only [hel, ite_false] at h; cases h
    simp only [succOk, hs, hel, ite_false]
    fin_cases k <;> simp [Control.afterOst, innerSite, onChain, isStart]

theorem ok_site_finish (d : Control.D) :
    (Control.finish w d).site = .exit ∨ (Control.finish w d).site = .dealloc := by
  unfold Control.finish; split <;> simp

theorem ok_site_afterA (d : Control.D) :
    (Control.afterA P d).site = .bwait ∨ (Control.afterA P d).site = .lenB := by
  unfold Control.afterA; split <;> simp

theorem ok_site_afterSink (d : Control.D) :
    ((Control.afterSink P L g w d).site = .exit ∨ (Control.afterSink P L g w d).site = .dealloc) ∨
    (Control.afterSink P L g w d).site = .bwait ∨ (Control.afterSink P L g w d).site = .lenB ∨
    (Control.afterSink P L g w d).site = .lenA := by
  unfold Control.afterSink
  split
  · exact .inl (ok_site_finish d)
  · split
    · rcases ok_site_afterA (P := P) { d with l0 := pw P.topk } with h | h <;> simp [h]
    · simp

theorem ok_site_afterSmr (d : Control.D) :
    ((Control.afterSmr P L g w d).site = .exit ∨ (Control.afterSmr P L g w d).site = .dealloc) ∨
    (Control.afterSmr P L g w d).site = .bwait ∨ (Control.afterSmr P L g w d).site = .lenB ∨
    (Control.afterSmr P L g w d).site = .lenA ∨ (Control.afterSmr P L g w d).site = .sink := by
  unfold Control.afterSmr
  split
  · rcases ok_site_afterSink (P := P) (L := L) (g := g) (w := w) d with h | h | h | h <;> simp [h]
  · simp

theorem ok_innerSite_exit (s : Site) (h : s = .exit ∨ s = .dealloc) : innerSite s = false := by
  rcases h with rfl | rfl <;> rfl

theorem ok_ncWord_some {e : Event} {f : BitVec 64 → Control.D} {c' : Control.D}
    (h : Control.ncWord e f = some (some c')) : ∃ x, c' = f x := by
  unfold Control.ncWord at h
  split at h
  · split at h
    · exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem okc_after {c c' : Control.D} {e : Event}
    (hs : c.site = .smr ∨ c.site = .sink ∨ c.site = .lenA ∨ c.site = .lenB)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs | hs
  · unfold Control.succ at h; rw [hs] at h
    have hc := (Option.some.inj (Option.some.inj h)).symm
    subst hc
    rcases ok_site_afterSmr (P := P) (L := L) (g := g) (w := w) c with (h | h) | h | h | h | h
    all_goals simp [succOk, hs, h, innerSite, onChain, isStart]
  · unfold Control.succ at h; rw [hs] at h
    simp only [Control.dataRd] at h
    split at h <;> try (exact (Option.some_ne_none _ h.symm).elim)
    all_goals
      have hc := (Option.some.inj (Option.some.inj h)).symm
      subst hc
      rcases ok_site_afterSink (P := P) (L := L) (g := g) (w := w) c with (h | h) | h | h | h
      all_goals simp [succOk, hs, h, innerSite, onChain, isStart]
  · unfold Control.succ at h; rw [hs] at h
    obtain ⟨x, hx⟩ := ok_ncWord_some h
    subst hx
    rcases ok_site_afterA (P := P) { c with site := .lenA, l0 := x } with h | h <;>
      simp [succOk, hs, h, innerSite, onChain, isStart]
  · unfold Control.succ at h; rw [hs] at h
    obtain ⟨x, hx⟩ := ok_ncWord_some h
    subst hx
    simp [succOk, hs, innerSite, onChain, isStart]

theorem succOk_afterEld (d : Control.D) (hs : d.site = .eld) :
    succOk d (Control.afterEld L g d) = true := by
  unfold Control.afterEld; split <;> simp [succOk, hs]

theorem okc_exit {c c' : Control.D} {e : Event} (hs : c.site = .exit)
    (h : Control.succ P L g w c e = some (some c')) : False := by
  simp only [Control.succ, hs] at h; cases h

theorem okc_off1 {c c' : Control.D} {e : Event}
    (hs : c.site = .commit ∨ c.site = .dealloc)
    (h : Control.succ P L g w c e = some (some c')) : innerSite c'.site = false := by
  rcases hs with hs | hs <;>
    simp only [Control.succ, hs] at h <;> cases h <;> simp [innerSite, onChain, isStart]

theorem okc_ebar {c c' : Control.D} {e : Event} (hs : c.site = .ebar)
    (h : Control.succ P L g w c e = some (some c')) : innerSite c'.site = false := by
  simp only [Control.succ, hs] at h; cases h; exact ok_innerSite_exit _ (ok_site_finish c)

/-- The next chunk's load, or the commit after the last chunk. -/
theorem okc_next {c c' : Control.D} (k : Fin 4)
    (hs : c.site = .obar k ∨ c.site = .oel k ∨ c.site = .otma k)
    (h : c'.site = [.old 1, .old 2, .old 3, .commit].getD k.val .commit) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs <;> fin_cases k <;>
    simp [succOk, hs, h, innerSite, onChain, isStart]

/-- The output chunk's load, its wait and its proxy fence. -/
theorem okc_o1 {c c' : Control.D} {e : Event} {k : Fin 4}
    (hs : c.site = .old k ∨ c.site = .oldw k ∨ c.site = .ofpx k)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs
  · simp only [Control.succ, hs, Control.tcLoad] at h; split at h <;> cases h
    simp [succOk, hs]
  · simp only [Control.succ, hs] at h; cases h; simp [succOk, hs]
  · simp only [Control.succ, hs] at h; cases h; simp [succOk, hs]

/-- The staging stores. -/
theorem okc_ost2 {c c' : Control.D} {e : Event} {k : Fin 4} {j : Fin 8} (hs : c.site = .ost2 k j)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs, Control.elemNext] at h
  by_cases hel : c.el + 1 < 4
  · simp only [hel, ite_true] at h; cases h; simp [succOk, hs, hel]
  · simp only [hel, ite_false] at h; cases h
    simp only [succOk, hs, hel, ite_false]
    fin_cases j <;> simp

/-- The named barrier, the election and the TMA store. -/
theorem okc_o2 {c c' : Control.D} {e : Event} {k : Fin 4}
    (hs : c.site = .obar k ∨ c.site = .oel k ∨ c.site = .otma k)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs
  · simp only [Control.succ, hs, Control.afterObar] at h
    split at h <;> cases h
    · exact okc_next k (.inl hs) rfl
    · simp [succOk, hs]
  · simp only [Control.succ, hs] at h
    split at h
    · split at h <;> cases h
      · simp [succOk, hs]
      · exact okc_next k (.inr (.inl hs)) rfl
    · cases h
  · simp only [Control.succ, hs] at h; cases h
    exact okc_next k (.inr (.inr hs)) rfl

/-- The LSE store, the poll and the fence. -/
theorem okc_tail {c c' : Control.D} {e : Event}
    (hs : c.site = .lse ∨ c.site = .wsv ∨ c.site = .efa)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs
  · simp only [Control.succ, hs] at h; cases h; simp [succOk, hs]
  · simp only [Control.succ, hs, Control.poll] at h; split at h
    · split at h <;> cases h <;> simp [succOk, hs]
    · cases h
  · simp only [Control.succ, hs] at h; cases h; simp [succOk, hs]

/-- The row-sum read goes to the LSE store or the poll. -/
theorem okc_eld {c c' : Control.D} {e : Event} (hs : c.site = .eld)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  simp only [Control.succ, hs, Control.dataRd] at h
  split at h <;> try (exact (Option.some_ne_none _ h.symm).elim)
  all_goals
    have hc := (Option.some.inj (Option.some.inj h)).symm
    subst hc
    exact .inl (succOk_afterEld c hs)

theorem okc_e {c c' : Control.D} {e : Event}
    (hs : c.site = .ebar0 ∨ c.site = .est ∨ c.site = .ebar1)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  rcases hs with hs | hs | hs <;> simp only [Control.succ, hs] at h <;> cases h <;>
    simp [succOk, innerSite, hs, onChain, isStart]

theorem okc_chain {c c' : Control.D} {e : Event} (hc : onChain c.site = true) (hn : c.site ≠ .arrS)
    (h : Control.succ P L g w c e = some (some c')) :
    succOk c c' = true ∨ innerSite c'.site = false := by
  cases hh : c.site <;> rw [hh] at hc hn <;> simp [onChain] at hc <;>
  first
  | (exact absurd rfl hn)
  | (refine okc_d1 ?_ h; simp [hh]; done)
  | exact okc_d2 (Or.inl hh) h
  | exact okc_d2 (Or.inr (Or.inl hh)) h
  | exact okc_d2 (Or.inr (Or.inr hh)) h
  | (exact okc_bar1 hh h)
  | exact okc_pst hh h
  | exact okc_arrL hh h
  | (refine okc_wv ?_ h; simp [hh]; done)
  | (refine okc_rd ?_ h; simp [hh]; done)
  | exact okc_sld hh h
  | exact okc_rld hh h
  | exact okc_pld hh h
  | exact okc_vote hh h
  | exact okc_ost hh h
  | exact okc_e (Or.inl hh) h
  | exact okc_e (Or.inr (Or.inl hh)) h
  | exact okc_e (Or.inr (Or.inr hh)) h
  | exact okc_eld hh h
  | exact okc_tail (Or.inl hh) h
  | exact okc_tail (Or.inr (Or.inl hh)) h
  | exact okc_tail (Or.inr (Or.inr hh)) h
  | exact okc_o1 (Or.inl hh) h
  | exact okc_o1 (Or.inr (Or.inl hh)) h
  | exact okc_o1 (Or.inr (Or.inr hh)) h
  | exact okc_ost2 hh h
  | exact okc_o2 (Or.inl hh) h
  | exact okc_o2 (Or.inr (Or.inl hh)) h
  | exact okc_o2 (Or.inr (Or.inr hh)) h
  | (refine okc_after ?_ h; simp [hh])

theorem okc_off {c c' : Control.D} {e : Event} (hc : onChain c.site = false)
    (h : Control.succ P L g w c e = some (some c')) : innerSite c'.site = false := by
  cases hh : c.site <;> rw [hh] at hc <;> simp [onChain] at hc <;>
  first
  | exact okc_off1 (Or.inl hh) h
  | exact okc_off1 (Or.inr hh) h
  | exact (okc_exit hh h).elim
  | exact okc_ebar hh h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
