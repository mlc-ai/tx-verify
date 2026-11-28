-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefNext

@[expose] public section

/-! # The index warp keeps its length words

Away from the two length loads every step of the control machine keeps the length words `l0`,
`l1` and leads to a site that is not a length load (`words_step`): the loops' transitions change
only the counters, the ring and the extra loop's words (`KeepW`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- A transition result keeps the length words of `c` and is not at a length load. -/
def KeepW (c : IxCtl) (p : IxSite × IxCtl) : Prop :=
  p.2.l0 = c.l0 ∧ p.2.l1 = c.l1 ∧ p.1 ≠ .lenA ∧ p.1 ≠ .lenB

theorem kw_mainTop (c : IxCtl) : KeepW c (mainTop c) := by
  unfold mainTop; dsimp only; split <;> exact ⟨rfl, rfl, by simp, by simp⟩

theorem kw_mainDone (c : IxCtl) : KeepW c (ixMainDone c) := by
  unfold ixMainDone; split <;> exact ⟨rfl, rfl, by simp, by simp⟩

theorem kw_afterPre (c : IxCtl) : KeepW c (afterPre P L g c) := by
  unfold afterPre; split
  · unfold ixNoMain; exact kw_mainDone _
  · unfold mainEntry; exact kw_mainTop _

theorem kw_mainEnd (c : IxCtl) : KeepW c (mainEnd c) := by
  unfold mainEnd; dsimp only; split
  · exact kw_mainTop _
  · exact kw_mainDone _

theorem kw_xTop (c : IxCtl) : KeepW c (xTop c) := by
  unfold xTop; dsimp only; split <;> exact ⟨rfl, rfl, by simp, by simp⟩

theorem kw_afterXpre (c : IxCtl) : KeepW c (afterXpre L g c) := by
  unfold afterXpre; split
  · exact ⟨rfl, rfl, by simp, by simp⟩
  · exact kw_xTop _

theorem kw_xEnd (c : IxCtl) : KeepW c (xEnd c) := by
  unfold xEnd; dsimp only; split
  · exact kw_xTop _
  · exact ⟨rfl, rfl, by simp, by simp⟩

/-- After the lengths: the words are kept and the site is not a length load. -/
theorem kw_lens (c : IxCtl) : KeepW c (ixLens c) := by
  unfold ixLens; dsimp only; split
  · unfold ixNoMain; exact kw_mainDone _
  · exact ⟨rfl, rfl, by simp, by simp⟩

/-- **A step away from the length loads keeps the length words.** -/
theorem words_step {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : succ P L g d e = some (some d')) (hA : d.site ≠ .lenA) (hB : d.site ≠ .lenB) :
    d'.c.l0 = d.c.l0 ∧ d'.c.l1 = d.c.l1 ∧ d'.site ≠ .lenA ∧ d'.site ≠ .lenB := by
  obtain ⟨site, el, ac, c⟩ := d
  have same : KeepW c (site, c) := ⟨rfl, rfl, hA, hB⟩
  have ofp {p : IxSite × IxCtl} (hp : KeepW c p) : KeepW c ((ofC p).site, (ofC p).c) := hp
  have ld {y : BitVec 64} {p : BitVec 64 → BitVec 64 → IxSite × IxCtl}
      (hp : ∀ y0 y1, KeepW c (p y0 y1)) :
      KeepW c ((ldNext ⟨site, el, ac, c⟩ y fun y0 y1 => ofC (p y0 y1)).site,
        (ldNext ⟨site, el, ac, c⟩ y fun y0 y1 => ofC (p y0 y1)).c) := by
    rcases ldNext_cases ⟨site, el, ac, c⟩ y (fun y0 y1 => ofC (p y0 y1)) with
      ⟨h1, h2⟩ | ⟨y0, y1, h'⟩
    · rw [h1, h2]; exact same
    · rw [h']; exact hp y0 y1
  suffices hk : KeepW c (d'.site, d'.c) by exact hk
  cases site with
  | lenA => exact absurd rfl hA
  | lenB => exact absurd rfl hB
  | pre | pf | xpre | xpf =>
    simp only [succ] at h
    obtain ⟨y, rfl⟩ := ncPair_some h
    first
      | exact ld (fun y0 y1 => kw_afterPre { c with m0 := y0, m1 := y1 })
      | exact ld (p := fun y0 y1 => (.wA, { c with n0 := y0, n1 := y1 }))
          (fun _ _ => ⟨rfl, rfl, by simp, by simp⟩)
      | exact ld (fun y0 y1 => kw_afterXpre { c with e0 := y0, e1 := y1 })
      | exact ld (p := fun y0 y1 => (.wB, { c with f0 := y0, f1 := y1 }))
          (fun _ _ => ⟨rfl, rfl, by simp, by simp⟩)
  | wA | wB =>
    simp only [succ, poll] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split
      · exact ⟨rfl, rfl, by simp, by simp⟩
      · exact same
    · cases h
  | stA | stB =>
    simp only [succ, Option.some.injEq] at h
    subst h
    rcases stNext_cases ⟨_, el, ac, c⟩ (ofC (afterSt L g _ _, c)) with ⟨h1, h2⟩ | h'
    · rw [h1, h2]; exact same
    · rw [h']
      refine ⟨rfl, rfl, ?_, ?_⟩ <;>
        rcases afterSt_cases (L := L) (g := g) (IxSite.bA) .arrA with h'' | h'' <;>
        first
          | (rcases afterSt_cases (L := L) (g := g) (IxSite.bB) .arrB with h3 | h3 <;>
              simp [h'', h3])
  | arrA =>
    simp only [succ, Option.some.injEq] at h
    subst h
    exact ofp (kw_mainEnd c)
  | arrB =>
    simp only [succ, Option.some.injEq] at h
    subst h
    exact ofp (kw_xEnd c)
  | exit => cases h
  | sA1 | sA2 | sB1 | sB2 =>
    simp only [succ] at h
    obtain ⟨r, rfl⟩ := shflNext_some h
    exact ⟨rfl, rfl, by simp, by simp⟩
  | _ =>
    simp only [succ, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, by simp, by simp⟩

/-- **A step leads to an element of the next site.** -/
theorem el_step {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : succ P L g d e = some (some d')) (hel : d.el < d.site.elems) : d'.el < d'.site.elems := by
  obtain ⟨site, el, ac, c⟩ := d
  have h0 {p : IxSite × IxCtl} : (ofC p).el < (ofC p).site.elems := IxSite.elems_pos _
  have ld {y : BitVec 64} {n : BitVec 64 → BitVec 64 → D} (hn : ∀ y0 y1, (n y0 y1).el <
      (n y0 y1).site.elems) (h2 : site.elems = 2) :
      (ldNext ⟨site, el, ac, c⟩ y n).el < (ldNext ⟨site, el, ac, c⟩ y n).site.elems := by
    unfold ldNext; split
    · rename_i hh; simp only at hh; show el + 1 < site.elems; omega
    · exact hn _ _
  have st {n : D} (hn : n.el < n.site.elems) (h2 : site.elems = 2) :
      (stNext ⟨site, el, ac, c⟩ n).el < (stNext ⟨site, el, ac, c⟩ n).site.elems := by
    unfold stNext; split
    · rename_i hh; simp only at hh; show el + 1 < site.elems; omega
    · exact hn
  simp only at hel
  cases site with
  | lenA | lenB =>
    simp only [succ, lenNext] at h
    split at h
    · obtain ⟨x, rfl⟩ := ncNext_some h; exact h0
    · cases h
  | pre | pf | xpre | xpf =>
    simp only [succ] at h
    obtain ⟨y, rfl⟩ := ncPair_some h
    exact ld (fun _ _ => h0) rfl
  | wA | wB =>
    simp only [succ, poll] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      split <;> exact hel
    · cases h
  | stA | stB =>
    simp only [succ, Option.some.injEq] at h; subst h; exact st h0 rfl
  | arrA | arrB => simp only [succ, Option.some.injEq] at h; subst h; exact h0
  | exit => cases h
  | sA1 | sA2 | sB1 | sB2 =>
    simp only [succ] at h
    obtain ⟨r, rfl⟩ := shflNext_some h
    simp only [IxSite.elems] at hel ⊢; omega
  | _ =>
    simp only [succ, Option.some.injEq] at h; subst h
    simp only [IxSite.elems] at hel ⊢; omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
