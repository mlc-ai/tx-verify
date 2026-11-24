-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftTc

@[expose] public section

/-! # The softmax fields of `ScoreFacts`

A softmax load of tile `T` of item `i` reads its row of its stage's scores, with `n i + T + 1`
successful S-full polls and `n i + T` P-ready arrivals before it, and its implicit
`tcgen05.wait::ld` is the thread's next event (`ScoreFacts_soft_ld`). The loads of a tile come
before its stores, since at a load the thread has made the stores of the earlier tiles only
(`ScoreFacts_soft_ld_st`), and a store site is passed once per tile, so two stores of a cell in
one tile are one event (`ScoreFacts_soft_st_one`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- At a load's wait every event is the wait. -/
theorem ldW_event {g : Nat} {d : Softmax.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {lp : Bool} {c : Fin 4} (hs : d.site = .ldW lp c)
    (h : Softmax.AtS L g d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    e.kind = .tc .waitLd := by
  rw [hs] at hc hf
  obtain ⟨ds, ta, hc'⟩ := Softmax.code_ldW lp c
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  have hw : asms.any (·.tcLdWait t.pc) = true := by
    rw [h.1, hs]
    cases lp
    · exact Softmax.tcLdWait_ld false c
    · exact Softmax.tcLdWait_ld true c
  have hsub : t.sub ≠ 0 := by rw [h.2.1, hs]; simp [Softmax.Site.sub]
  simp only [eventTmpl, tcLdTmpl, hw, ↓reduceIte, hsub, Fires] at hf
  rw [hf.1]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`ScoreFacts.soft_ld`.** -/
theorem ScoreFacts_soft_ld {h i a : Nat} {vals : List Value} (_hh : h < L.threads)
    (hw : warpOf L h < 8) (he : X.TLd (h, i) a vals .s32x32b) :
    (∀ j < vals.length, InS (warpOf L h / 4) (tcDataCell32 L h a j)) ∧
    (i + 1 < (X.tr h).length → ∃ pc, X.get (h, i + 1) = some ⟨pc, .tc .waitLd⟩) ∧
    pArr L X h (warpOf L h / 4) i + 1 = sPolls L X h (warpOf L h / 4) i := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨d, lp, c, hσ, hc, hi, hs, ha, hl⟩ := soft_tld hpre hX ht hw he
  have hst : Softmax.stOf L h = warpOf L h / 4 := rfl
  refine ⟨fun j hj => ?_, fun hlen => ?_, ?_⟩
  · simp only [InS]
    rw [ha, soft_column L h h (32 * c.val) j hw (by omega)]
    omega
  · obtain ⟨x, hx⟩ : ∃ x, X.get (h, i + 1) = some x := ⟨_, List.getElem?_eq_getElem hlen⟩
    have hn : Softmax.next L h d ⟨pc, .tc (.ld a vals .s32x32b)⟩ =
        some (some { d with site := .ldW lp c, w := Softmax.loadW d.w c.val vals }) := by
      simp only [Softmax.next, hs]
    have hσ' : Frame.stateAt (code L) X h (i + 1) = some (some (.inr (.softmax
        { d with site := .ldW lp c, w := Softmax.loadW d.w c.val vals }))) := by
      rw [soft_succ hσ he, hn]
      rfl
    have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
    obtain ⟨t, ins, o, hat, -, hcd, hf⟩ := Frame.fired_site hC hX hx hσ'
    have hk := ldW_event (d := { d with site := .ldW lp c, w := Softmax.loadW d.w c.val vals })
      rfl hat hcd hf
    exact ⟨x.pc, by rw [hx, ← hk]⟩
  · unfold pArr sPolls
    rw [soft_pReadyBar, soft_sFullBar, hc.pReady, hc.score]
    have ht0 := hi.tile0
    have htr := hi.trip
    obtain ⟨site, ii, tt, w, mm, l⟩ := d
    simp only at hs ht0 htr ⊢
    subst hs
    cases lp <;>
      simp [Softmax.pPos, Softmax.sPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.inTrip, Softmax.Site.tile0Ld, Softmax.Site.afterP] at ht0 htr ⊢
    omega

omit hX ht in
/-- The S-full polls before a load or store site are `n i + T + 1` for its tile `T < n`, and
the stores before it are `4 n i + 4 T` plus the stores of the tile made. -/
theorem soft_tile {g : Nat} {d : Softmax.D} (hi : Softmax.Inv L g d)
    (hs : (∃ lp c, d.site = .ld lp c) ∨ ∃ lp c, d.site = .pst lp c) :
    Softmax.sPos d = Softmax.tileNo d + 1 ∧ Softmax.tileNo d < Softmax.trips L ∧
      Softmax.stPos d = 4 * Softmax.tileNo d + (match d.site with | .pst _ c => c.val | _ => 0) ∧
      (d.site.tile0 = true ↔ Softmax.tileNo d = 0) := by
  have ht0 := hi.tile0
  have htr := hi.trip
  have hn := soft_trips_pos hpre
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs ht0 htr ⊢
  rcases hs with ⟨lp, c, rfl⟩ | ⟨lp, c, rfl⟩ <;> cases lp
  all_goals simp [Softmax.sPos, Softmax.tileNo, Softmax.stPos, Softmax.Site.tile0,
    Softmax.Site.tile0Ld, Softmax.Site.inTrip] at ht0 htr ⊢
  all_goals omega

/-- **`ScoreFacts.soft_ld_st`.** -/
theorem ScoreFacts_soft_ld_st {h i i' a a' : Nat} {vals vals' : List Value}
    (_hh : h < L.threads) (hw : warpOf L h < 8) (he : X.TLd (h, i) a vals .s32x32b)
    (he' : X.TSt (h, i') a' vals' .s32x32b)
    (hs : sPolls L X h (warpOf L h / 4) i = sPolls L X h (warpOf L h / 4) i') : i < i' := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨pc', he'⟩ := he'
  obtain ⟨d, lp, c, -, hc, hi, hsd, -, -⟩ := soft_tld hpre hX ht hw he
  obtain ⟨d', lp', c', -, hc', hi', hsd', ha', -⟩ := soft_tst hpre hX ht hw he'
  obtain ⟨h1, h2, h3, -⟩ := soft_tile hpre hi (.inl ⟨lp, c, hsd⟩)
  obtain ⟨h1', h2', h3', -⟩ := soft_tile hpre hi' (.inr ⟨lp', c', hsd'⟩)
  unfold sPolls at hs
  rw [soft_sFullBar, hc.score, hc'.score, h1, h1'] at hs
  obtain ⟨hii, hT⟩ := tile_inj (i := d.i) (i' := d'.i) h2 h2' (by omega)
  by_contra hlt
  have hne : i ≠ i' := by
    intro hh; subst hh; rw [he] at he'; cases he'
  have hcnt := countP_take_lt (k := i)
    (p := tcStAt (Softmax.tmem L h 64) (Softmax.tmem L h 128)) he'
    (by rw [ha']; simp [tcStAt, Softmax.tmem]; omega) (by omega)
  have q1 := hc.tcSt
  have q2 := hc'.tcSt
  unfold tcStsIn at q1 q2
  rw [q1, q2, h3, h3', hii, hT, hsd, hsd'] at hcnt
  simp only at hcnt
  omega

/-- **`ScoreFacts.soft_st_one`.** -/
theorem ScoreFacts_soft_st_one {h i i' a a' j j' : Nat} {vals vals' : List Value}
    (_hh : h < L.threads) (hw : warpOf L h < 8) (he : X.TSt (h, i) a vals .s32x32b)
    (he' : X.TSt (h, i') a' vals' .s32x32b) (hj : j < vals.length) (hj' : j' < vals'.length)
    (hcell : tcDataCell32 L h a j = tcDataCell32 L h a' j')
    (hs : sPolls L X h (warpOf L h / 4) i = sPolls L X h (warpOf L h / 4) i') : i = i' := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨pc', he'⟩ := he'
  obtain ⟨d, lp, c, -, hc, hi, hsd, ha, hl⟩ := soft_tst hpre hX ht hw he
  obtain ⟨d', lp', c', -, hc', hi', hsd', ha', hl'⟩ := soft_tst hpre hX ht hw he'
  obtain ⟨h1, h2, h3, -⟩ := soft_tile hpre hi (.inr ⟨lp, c, hsd⟩)
  obtain ⟨h1', h2', h3', -⟩ := soft_tile hpre hi' (.inr ⟨lp', c', hsd'⟩)
  unfold sPolls at hs
  rw [soft_sFullBar, hc.score, hc'.score, h1, h1'] at hs
  obtain ⟨hii, hT⟩ := tile_inj (i := d.i) (i' := d'.i) h2 h2' (by omega)
  have hcol := congrArg TcMma.Cell.column hcell
  rw [ha, ha', soft_column L h h _ _ hw (by omega), soft_column L h h _ _ hw (by omega)] at hcol
  have hcc : c.val = c'.val := by omega
  have hP : ∀ {x y : Nat} {e : Event}, X.get (h, x) = some e →
      tcStAt (Softmax.tmem L h 64) (Softmax.tmem L h 128) e = true →
      x < y → ((X.tr h).take x).countP (tcStAt (Softmax.tmem L h 64) (Softmax.tmem L h 128)) + 1
        ≤ ((X.tr h).take y).countP (tcStAt (Softmax.tmem L h 64) (Softmax.tmem L h 128)) :=
    fun hx hp hxy => countP_take_lt hx hp hxy
  have q1 := hc.tcSt
  have q2 := hc'.tcSt
  unfold tcStsIn at q1 q2
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · have := hP he (by rw [ha]; simp [tcStAt, Softmax.tmem]; omega) hlt
    rw [q1, q2, h3, h3', hii, hT, hsd, hsd'] at this
    simp only at this
    omega
  · exact heq
  · have := hP he' (by rw [ha']; simp [tcStAt, Softmax.tmem]; omega) hgt
    rw [q1, q2, h3, h3', hii, hT, hsd, hsd'] at this
    simp only at this
    omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
