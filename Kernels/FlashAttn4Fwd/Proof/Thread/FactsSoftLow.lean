-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSt
public import Lemmas.Flow.CountFirst

@[expose] public section

/-! # `TcMmaThreadFacts.soft_low` and `soft_high`

At its P-ready arrival of tile `T` of item `i` a softmax thread has made `4 n i + 4 T + 3`
probability stores, and at the tile's warp barrier `4 n i + 4 T + 4`. The store of a column
`64 + 16 c + j` of the tile is the thread's store of ordinal `4 n i + 4 T + c`
(`nth_countP` finds it), at the site `pst lp c` of the tile (the count of its state decomposes
into item, tile and site), so it comes before the arrival when `c < 3` and before the warp
barrier when `c = 3`, with `n i + T + 1` S-full polls before it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Store ordinals decompose into item, tile and site. -/
theorem st_decomp {n i T c i' T' c' : Nat} (hT : T < n) (hT' : T' < n) (hc : c < 4) (hc' : c' < 4)
    (h : 4 * n * i + (4 * T + c) = 4 * n * i' + (4 * T' + c')) : i = i' ∧ T = T' ∧ c = c' := by
  have e1 : 4 * n * i + (4 * T + c) = 4 * (n * i + T) + c := by ring
  have e2 : 4 * n * i' + (4 * T' + c') = 4 * (n * i' + T') + c' := by ring
  rw [e1, e2] at h
  have hcc : c = c' := by omega
  have hq : n * i + T = n * i' + T' := by omega
  obtain ⟨h1, h2⟩ := tile_inj hT hT' hq
  exact ⟨h1, h2, hcc⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **The store of ordinal `4 n i + 4 T + c`** of a softmax thread, before event `e` when the
thread has made more stores there: it is at site `pst lp c` of tile `T` of item `i`, writing the
stage's columns `64 + 16 c …`, after `n i + T + 1` S-full polls. -/
theorem soft_nth_st {g e i T c : Nat} (hw : warpOf L g < 8) (hT : T < Softmax.trips L)
    (hc : c < 4)
    (hlt : 4 * Softmax.trips L * i + (4 * T + c) <
      tcStsIn (Softmax.tmem L g 64) (Softmax.tmem L g 128) ((X.tr g).take e)) :
    ∃ k a, ∃ vals : List Value, k < e ∧ X.TSt (g, k) a vals .s32x32b ∧ vals.length = 16 ∧
      a = Softmax.tmem L g (64 + 16 * c) ∧
      sPolls L X g (warpOf L g / 4) k = Softmax.trips L * i + T + 1 := by
  obtain ⟨k, hk, x, hx, hp, hcnt⟩ := nth_countP hlt
  have hx' : X.get (g, k) = some x := hx
  obtain ⟨xpc, xk⟩ := x
  obtain ⟨a, vals, sh, rfl⟩ : ∃ a vals sh, xk = .tc (.st a vals sh) := by
    cases xk <;> simp_all [tcStAt]
    rename_i tk
    cases tk <;> simp_all
  obtain rfl := tc_shape_of_get hpre hX ht hx' (.inr rfl)
  obtain ⟨d, lp, c', -, hcn, hi, hs, ha, hl⟩ := soft_tst hpre hX ht hw hx'
  obtain ⟨h1, h2, h3, -⟩ := soft_tile hpre hi (.inr ⟨lp, c', hs⟩)
  have q := hcn.tcSt
  unfold tcStsIn at q
  rw [hcnt, h3, hs] at q
  simp only at q
  obtain ⟨hii, hTT, hcc⟩ := st_decomp hT h2 hc c'.isLt q
  refine ⟨k, a, vals, hk, ⟨xpc, hx'⟩, hl, by rw [ha, ← hcc], ?_⟩
  unfold sPolls
  rw [soft_sFullBar, hcn.score, h1, ← hii, ← hTT]
  omega

/-- **`TcMmaThreadFacts.soft_low`.** -/
theorem TcMmaThreadFacts_soft_low {h e pc tx cnt col : Nat} {rel : Bool} {sc : MbarScope}
    (_hh : h < L.threads) (hw : warpOf L h < 8)
    (he : X.get (h, e) = some ⟨pc,
      .arrive (pReadyBar L (leadCta (ctaOf L h)) (warpOf L h / 4)) tx cnt rel sc⟩)
    (hp : InP (warpOf L h / 4) (tcDataCell32 L h 0 col))
    (hn : ¬ InPHigh (warpOf L h / 4) (tcDataCell32 L h 0 col)) :
    ∃ k a j, ∃ vals : List Value, k < e ∧ X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧
      tcDataCell32 L h a j = tcDataCell32 L h 0 col ∧
      sPolls L X h (warpOf L h / 4) k = pArr L X h (warpOf L h / 4) e + 1 := by
  obtain ⟨d, -, hc, hi, -, -, -, hsite⟩ := soft_arrive hpre hX ht hw he
  have hso : Softmax.stOf L h = warpOf L h / 4 := rfl
  rcases hsite with ⟨lp, hs, -⟩ | ⟨lp, -, hm⟩
  swap
  · rw [← soft_pReady2Bar] at hm
    simp only [pReadyBar, pReady2Bar, Loc.mk.injEq] at hm
    omega
  simp only [InP, InPHigh, tcDataCell32, Nat.zero_mod, Nat.zero_add] at hp hn
  have hT := soft_trips_pos hpre
  have ht0 := hi.tile0
  have htr := hi.trip
  have hpos : Softmax.tileNo d < Softmax.trips L ∧ Softmax.pPos d = Softmax.tileNo d ∧
      Softmax.stPos d = 4 * Softmax.tileNo d + 3 := by
    obtain ⟨site, ii, tt, w, mm, l⟩ := d
    simp only at hs ht0 htr ⊢
    subst hs
    cases lp <;> simp [Softmax.pPos, Softmax.stPos, Softmax.tileNo, Softmax.Site.tile0,
      Softmax.Site.inTrip, Softmax.Site.afterP] at ht0 htr ⊢ <;> omega
  obtain ⟨hT', hpp, hsp⟩ := hpos
  set c := (col - (128 * (warpOf L h / 4) + 64)) / 16 with hcdef
  set j := (col - (128 * (warpOf L h / 4) + 64)) % 16 with hjdef
  have hc3 : c < 3 := by omega
  have hlt : 4 * Softmax.trips L * d.i + (4 * Softmax.tileNo d + c) <
      tcStsIn (Softmax.tmem L h 64) (Softmax.tmem L h 128) ((X.tr h).take e) := by
    rw [hc.tcSt, hsp]; omega
  obtain ⟨k, a, vals, hk, hst, hl, ha, hS⟩ := soft_nth_st hpre hX ht hw hT' (by omega) hlt
  refine ⟨k, a, j, vals, hk, hst, by omega, ?_, ?_⟩
  · have hcol := soft_column L h h (64 + 16 * c) j hw (by omega)
    rw [← ha] at hcol
    simp only [tcDataCell32, Nat.zero_mod, Nat.zero_add, TcMma.Cell.mk.injEq, true_and]
    simp only [tcDataCell32] at hcol
    omega
  · unfold pArr
    rw [hS, soft_pReadyBar, hc.pReady, hpp]

/-- **`TcMmaThreadFacts.soft_high`.** -/
theorem TcMmaThreadFacts_soft_high {h b m inst col : Nat} (_hh : h < L.threads)
    (hw : warpOf L h < 8) (he : X.WarpBar (h, b) m inst)
    (hp : InP (warpOf L h / 4) (tcDataCell32 L h 0 col))
    (hn : InPHigh (warpOf L h / 4) (tcDataCell32 L h 0 col)) :
    ∃ k a j, ∃ vals : List Value, k < b ∧ X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧
      tcDataCell32 L h a j = tcDataCell32 L h 0 col ∧
      sPolls L X h (warpOf L h / 4) k = warpBars X h b + 1 := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨d, t, ins, o, -, hc, hi, -, -, -, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hso : Softmax.stOf L h = warpOf L h / 4 := rfl
  obtain ⟨lp, hs⟩ : ∃ lp, d.site = .warpBar lp := by
    unfold Softmax.Ev at hev
    cases hsd : d.site <;> simp only [hsd, reduceCtorEq, exists_false] at hev
    all_goals exact ⟨_, rfl⟩
  simp only [InP, InPHigh, tcDataCell32, Nat.zero_mod, Nat.zero_add] at hp hn
  have hT := soft_trips_pos hpre
  have ht0 := hi.tile0
  have htr := hi.trip
  have hpos : Softmax.tileNo d < Softmax.trips L ∧ Softmax.wbPos d = Softmax.tileNo d ∧
      Softmax.stPos d = 4 * Softmax.tileNo d + 4 := by
    obtain ⟨site, ii, tt, w, mm, l⟩ := d
    simp only at hs ht0 htr ⊢
    subst hs
    cases lp <;> simp [Softmax.wbPos, Softmax.stPos, Softmax.tileNo, Softmax.Site.tile0,
      Softmax.Site.inTrip, Softmax.Site.afterWB] at ht0 htr ⊢ <;> omega
  obtain ⟨hT', hwp, hsp⟩ := hpos
  set j := col - (128 * (warpOf L h / 4) + 112) with hjdef
  have hlt : 4 * Softmax.trips L * d.i + (4 * Softmax.tileNo d + 3) <
      tcStsIn (Softmax.tmem L h 64) (Softmax.tmem L h 128) ((X.tr h).take b) := by
    rw [hc.tcSt, hsp]; omega
  obtain ⟨k, a, vals, hk, hst, hl, ha, hS⟩ := soft_nth_st hpre hX ht hw hT' (by omega) hlt
  refine ⟨k, a, j, vals, hk, hst, by omega, ?_, ?_⟩
  · have hcol := soft_column L h h (64 + 16 * 3) j hw (by omega)
    rw [← ha] at hcol
    simp only [tcDataCell32, Nat.zero_mod, Nat.zero_add, TcMma.Cell.mk.injEq, true_and]
    simp only [tcDataCell32] at hcol
    omega
  · unfold warpBars
    rw [hS, hc.warpBar, hwp]

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
